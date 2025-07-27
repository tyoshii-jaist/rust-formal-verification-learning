use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::layout::*;
use vstd::set_lib::*;

// Blockというメモリ領域の塊を表す構造体の例
// u32型固定で、指定した個数 (block_count)分の u32 を払い出すことができる。
// freeには対応していない。
// deallocもできない。
// deallocする場合は、PointsToRawをかき集めてからdeallocしないといけないはず。
verus!{

global layout u32 is size == 4, align == 4;

struct Block {
    block_count: u32, // 確保した個数
    block_ptr: *mut u32, // 払い出せる場所のポインタ。最初はブロック全体の先頭で、一つずつ後退する。
    allocated_count: u32, // 払い出した個数

    ghost_state: Tracked<GhostState>,
}

pub tracked struct GhostState {
    tracked points_to_raw_map: Map<nat, PointsToRaw>,
    tracked dealloc_token: Dealloc,
}

impl Block {
    spec fn well_formed(&self) -> bool {
        let points_to_raw = self.ghost_state@.points_to_raw_map.index(0);
        self.ghost_state@.points_to_raw_map.dom().contains(0)
        && self.block_ptr.addr() + (self.block_count - self.allocated_count) * size_of::<u32>() <= usize::MAX + 1
        && points_to_raw.is_range(self.block_ptr.addr() as int, (self.block_count - self.allocated_count) * size_of::<u32>())
        && self.block_ptr.addr() as int % align_of::<u32>() as int == 0
        && self.block_ptr@.provenance == points_to_raw.provenance()
    }

    spec fn not_full(&self) -> bool {
        self.allocated_count < self.block_count
    }

    fn new(block_count: u32) -> (s: Self)
        requires
            block_count > 0,
            block_count as usize * 4 <= usize::MAX,
            valid_layout((block_count as usize * 4) as usize, 4),
        ensures
            s.allocated_count == 0,
            s.block_count - s.allocated_count == block_count,
            s.block_count == block_count,
            s.well_formed()
    {
        let allocation_size = block_count as usize * 4;
        let (block_ptr, Tracked(points_to_raw), Tracked(dealloc_token)): (*mut u8, Tracked<PointsToRaw>, Tracked<Dealloc>) = allocate(allocation_size, 4);
        let tracked mut points_to_raw_map: Map<nat, PointsToRaw>;
        proof {
            points_to_raw_map = Map::tracked_empty();
            points_to_raw_map.tracked_insert(0 as nat, points_to_raw);
        }
        Block {
            block_count,
            block_ptr: block_ptr as *mut u32,
            allocated_count: 0,
            ghost_state: Tracked(GhostState {
                points_to_raw_map,
                dealloc_token,
            })
        }
    }

    fn allocate_u32(&mut self) -> (r: (*mut u32, Tracked<PointsTo<u32>>))
        requires
            old(self).not_full(),
            old(self).well_formed(),
        ensures
            self.block_count == old(self).block_count,
            self.allocated_count == old(self).allocated_count + 1,
            self.not_full() ==> self.well_formed(),
            r.0@.provenance == old(self).block_ptr@.provenance, // これより下は allocate の postcondition を参考に、引き継いでいる。
            r.1@.ptr() == r.0,
            r.1@.opt_value() == MemContents::<u32>::Uninit,
    {
        let ptr = with_exposed_provenance(self.block_ptr.addr(), expose_provenance(self.block_ptr)) as *mut u32;

        let tracked mut points_to_raw = self.ghost_state.borrow_mut().points_to_raw_map.tracked_remove(0);
        let tracked splitted = points_to_raw.split(set_int_range(ptr as int, ptr as int + size_of::<u32>() as int));
        let tracked points_to = splitted.0.into_typed::<u32>(ptr as usize);
        proof {
            self.ghost_state.borrow_mut().points_to_raw_map.tracked_insert(0 as nat, splitted.1);
        }
        self.allocated_count = self.allocated_count + 1;
        if self.allocated_count < self.block_count {
            self.block_ptr = with_exposed_provenance(self.block_ptr.addr() + 4, expose_provenance(self.block_ptr)) as *mut u32; // 次のu32のためにポインタを進める
        }
        (ptr as *mut u32, Tracked(points_to))
    }

}

fn main() {
    layout_for_type_is_valid::<u32>();
    let blocks = 2u32; // ブロックの個数を2に設定
    let mut block = Block::new(blocks); // 2つのu32を格納できるブロックを確保
    for i in 0u32..blocks
        invariant
            block.block_count == blocks,
            block.allocated_count == i,
            i < block.block_count ==> block.well_formed(),
            i < block.block_count ==> block.not_full(),
    {
        let (ptr, Tracked(points_to)) = block.allocate_u32(); // u32のポインタとPointsToを取得
        assert(equal(points_to.ptr(), ptr));
        assert(equal(points_to.opt_value(), MemContents::Uninit));
        ptr_mut_write(ptr, Tracked(&mut points_to), i as u32); // ポインタに値を書き込む
        assert(equal(points_to.ptr(), ptr));
        assert(equal(points_to.opt_value(), MemContents::Init(i as u32)));
    }
}
}