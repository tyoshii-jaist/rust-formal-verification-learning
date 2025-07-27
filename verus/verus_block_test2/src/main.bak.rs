#![feature(strict_provenance)]
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::layout::*;
use vstd::set_lib::*;

verus!{

global layout u32 is size == 4, align == 4;

struct Block {
    block_count: u32,
    block_ptr: *mut u8,
    current_pos: u32,

    ghost_state: Tracked<GhostState>,
}

pub tracked struct GhostState {
    tracked points_to_raw_map: Map<nat, PointsToRaw>,
    tracked dealloc_token: Dealloc,
}

impl Block {
    spec fn well_formed(&self) -> bool {
        self.ghost_state@.points_to_raw_map.dom().contains(0)
    }

    spec fn allocatable(&self) -> bool {
        self.current_pos < self.block_count
    }

    spec fn range_valid(&self) -> bool {
        let addr = self.block_ptr.addr() + self.current_pos as usize * size_of::<u32>();
        let range = set_int_range(addr as int, addr as int + size_of::<u32>() as int);

        addr as int % align_of::<u32>() as int == 0
        && range.subset_of(self.ghost_state@.points_to_raw_map.spec_index(0).dom())
    }

    spec fn address_range_valid(&self) -> bool {
        let addr = self.block_ptr.addr() + self.block_count as usize * 4;
        addr as usize <= usize::MAX
    }


    fn new(block_count: u32) -> (s: Self)
        requires
            block_count > 0,
            block_count as usize * 4 <= usize::MAX,
            valid_layout((block_count as usize * 4) as usize, 4),
        ensures
            s.well_formed(),
            s.allocatable(),
            s.range_valid(),
            s.address_range_valid(),
            s.current_pos == 0,
            s.block_count == block_count,
    {
        let (block_ptr, Tracked(points_to_raw), Tracked(dealloc_token)): (*mut u8, Tracked<PointsToRaw>, Tracked<Dealloc>) = allocate(block_count as usize * 4, 4);
        let tracked mut points_to_raw_map: Map<nat, PointsToRaw>;
        proof {
            points_to_raw_map = Map::tracked_empty();
            points_to_raw_map.tracked_insert(0 as nat, points_to_raw);
        }
        Block {
            block_count,
            block_ptr,
            current_pos: 0,
            ghost_state: Tracked(GhostState {
                points_to_raw_map,
                dealloc_token,
            })
        }
    }

    fn allocate_u32(&mut self) -> (r: (*mut u32, Tracked<PointsTo<u32>>))
        requires
            old(self).well_formed(),
            old(self).allocatable(),
            old(self).range_valid(),
            old(self).address_range_valid(),
        ensures
            self.well_formed(),
            self.current_pos < self.block_count ==> self.allocatable(),
            self.current_pos < self.block_count ==> self.range_valid(),
            old(self).block_count == self.block_count,
            (old(self).current_pos + 1) as int == self.current_pos as int,
    {
        proof {
            assert(old(self).current_pos < old(self).block_count);
            assert(old(self).address_range_valid());
            assume(old(self).block_ptr.addr() + old(self).block_count as usize * 4 <= usize::MAX);
        }
        //let ptr = self.block_ptr.with_addr(self.block_ptr.addr() + self.current_pos as usize * 4);
        let ptr = with_exposed_provenance(self.block_ptr as usize, expose_provenance(self.block_ptr));
        let tracked mut points_to_raw = self.ghost_state.borrow_mut().points_to_raw_map.tracked_remove(0);
        let tracked mut points_to: PointsTo<u32>;
        proof {
            let set_diff = set_int_range(ptr as int, ptr as int + size_of::<u32>() as int);
            let tracked splitted = points_to_raw.split(set_diff);
            points_to = splitted.0.into_typed::<u32>(ptr as usize);
            self.ghost_state.borrow_mut().points_to_raw_map.tracked_insert(0, splitted.1);
            assert(points_to.ptr() as usize == ptr as usize);
        }
        self.current_pos = self.current_pos + 1;
        proof {
            assume(self.current_pos < self.block_count ==> self.range_valid());
        }
        (ptr as *mut u32, Tracked(points_to))
    }
}

fn main() {
    layout_for_type_is_valid::<u32>();
    let mut block = Block::new(2); // 2つのu32を格納できるブロックを確保
    let (b1_ptr, Tracked(b1_pointsto)) = block.allocate_u32(); // 1つ目のu32のポインタとPointsToを取得
    let (b2_ptr, Tracked(b2_pointsto)) = block.allocate_u32(); // 2つ目のu32のポインタとPointsToを取得
    // 以下はそれぞれの領域の確認、書き込み、参照、読み出し(move)を行っている。
    assert(equal(b1_pointsto.ptr(), b1_ptr));
    assert(equal(b2_pointsto.ptr(), b2_ptr));
    assert(equal(b1_pointsto.opt_value(), MemContents::Uninit));
    assert(equal(b2_pointsto.opt_value(), MemContents::Uninit));
    ptr_mut_write(b1_ptr, Tracked(&mut b1_pointsto), 555);
    ptr_mut_write(b2_ptr, Tracked(&mut b2_pointsto), 666);
    assert(equal(b1_pointsto.ptr(), b1_ptr));
    assert(equal(b1_pointsto.opt_value(), MemContents::Init(555)));
    assert(equal(b2_pointsto.ptr(), b2_ptr));
    assert(equal(b2_pointsto.opt_value(), MemContents::Init(666)));
    let b1_val = ptr_ref(b1_ptr, Tracked(&b1_pointsto));
    assert(equal(*b1_val, 555));
    let b2_val = ptr_ref(b2_ptr, Tracked(&b2_pointsto));
    assert(equal(*b2_val, 666));
    let b1_read = ptr_mut_read(b1_ptr, Tracked(&mut b1_pointsto));
    assert(equal(b1_pointsto.ptr(), b1_ptr));
    assert(equal(b1_pointsto.opt_value(), MemContents::Uninit)); // moved?
    assert(equal(b1_read, 555));
    let b2_read = ptr_mut_read(b2_ptr, Tracked(&mut b2_pointsto));
    assert(equal(b2_pointsto.ptr(), b2_ptr));
    assert(equal(b2_pointsto.opt_value(), MemContents::Uninit)); // moved?
    assert(equal(b2_read, 666));
}
}