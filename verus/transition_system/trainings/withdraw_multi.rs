/*
withdraw のプログラムの説明

これは new_buf<T>(n) で初期化した長さ n のバッファの最初の位置 (0) の要素をチェックアウトするだけのプログラムである。

状態遷移としては checkout_first_two という transition しかない。
end_idx という変数があり、これを使って 0 番目がチェックアウトされていないことを証明するようにしている。
名前が適切ではないが、将来的に 0~end_idxまでをチェックアウトできるように拡張する予定なのでこの名前になっている。

checkout_first_two()を実行すると compare_exchange を用いて end_idx を 0 => 1 に変更しようとする。
これが成功すると、transition を発生させ、Ghostの方も end_idx を 0 => 1 に変更し、かつ、実際のバッファに紐づく PointsTo トークンを払い出す。これは atomic_with_ghost!内でハンドリングすることで Atomic 変数の変更と同時に行うことができる。
 */

use state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
use vstd::cell::*;
use vstd::map::*;
use vstd::{prelude::*, *};

verus! {

tokenized_state_machine!{VBQueue<T> {
    fields {
        #[sharding(constant)]
        pub backing_cells: Seq<CellId>,

        // All the stored permissions

        #[sharding(storage_map)]
        pub storage: Map<nat, cell::PointsTo<T>>,

        #[sharding(variable)]
        pub end_idx: nat,
    }

    pub open spec fn len(&self) -> nat {
        self.backing_cells.len()
    }

    pub open spec fn valid_storage_at_idx(&self, i: nat) -> bool {
        if self.is_checked_out(i) {
            !self.storage.dom().contains(i)
        } else {
            // Permission is stored
            self.storage.dom().contains(i)

            // Permission must be for the correct cell:
            && self.storage.index(i).id() === self.backing_cells.index(i as int)

            && self.storage.index(i).is_uninit()
        }
    }
    
    pub open spec fn is_checked_out(&self, i: nat) -> bool {
        0 <= i && i < self.end_idx
    }

    #[invariant]
    pub fn valid_storage_all(&self) -> bool {
        forall|i: nat| 0 <= i && i < self.len() ==>
            self.valid_storage_at_idx(i)
    }

    #[invariant]
    pub fn in_bounds(&self) -> bool {
        &&& 0 < self.len()
        &&& 0 <= self.end_idx && self.end_idx <= self.len()
    }

    init!{
        initialize(backing_cells: Seq<CellId>, storage: Map<nat, cell::PointsTo<T>>) {
            // Upon initialization, the user needs to deposit _all_ the relevant
            // cell permissions. Each permission should indicate
            // an empty cell.

            require(
                (forall|i: nat| 0 <= i && i < backing_cells.len() ==>
                    #[trigger] storage.dom().contains(i)
                    && storage.index(i).id() === backing_cells.index(i as int)
                    && storage.index(i).is_uninit())
            );
            require(backing_cells.len() > 0);

            init backing_cells = backing_cells;
            init storage = storage;
            init end_idx = 0;
        }
    }

    transition!{
        checkout_first_two() {
            assert(0 < pre.backing_cells.len());

            require(pre.end_idx == 0);
            require(pre.backing_cells.len() > 1);

            // https://github.com/verus-lang/verified-memory-allocator/blob/8588ce6accba37fa2ebc40e05af39038187c1ddc/verus-mimalloc/tokens.rs#L509
            birds_eye let perm_map: Map<nat, cell::PointsTo<T>> = Map::new(
                    |i: nat| 0 <= i && i < 2,
                    |i: nat| pre.storage[i]);

            withdraw storage -= (perm_map) by {
                assert(pre.valid_storage_at_idx(0) && pre.valid_storage_at_idx(1));
            };

            birds_eye let perm0 = perm_map[0];
            birds_eye let perm1 = perm_map[1];

            update end_idx = 2;

            // The transition needs to guarantee to the client that the
            // permission they are checking out:
            //  (i) is for the cell at index `tail` (the IDs match)
            //  (ii) the permission indicates that the cell is empty
            assert(
                perm0.id() === pre.backing_cells.index(0)
                && perm0.is_uninit()
            ) by {
                assert(pre.valid_storage_at_idx(0));
            };
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, backing_cells: Seq<CellId>, storage: Map<nat, cell::PointsTo<T>>) {
        assert forall|i: nat|
            0 <= i && i < post.len() implies post.valid_storage_at_idx(i)
        by {
            assert(post.storage.dom().contains(i));
        }
    }

    #[inductive(checkout_first_two)]
    fn checkout_first_two_inductive(pre: Self, post: Self) {
        assert(!pre.is_checked_out(0));
        assert(!pre.is_checked_out(1));
        assert(forall|i| pre.valid_storage_at_idx(i) ==> post.valid_storage_at_idx(i)) by {
        
        }
        assert(post.is_checked_out(0));
        assert(post.is_checked_out(1));
    }
}} // tokenized_state_machine

struct_with_invariants!{
    pub struct VBBuffer<T> {
        buffer: Vec<PCell<T>>,
        end_idx: AtomicU64<_, VBQueue::end_idx<T>, _>,
        instance: Tracked<VBQueue::Instance<T>>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            &&& 0 < self.instance@.backing_cells().len()
            &&& 0 < self.buffer@.len()
            &&& self.instance@.backing_cells().len() == self.buffer@.len()
            &&& forall|i: int| 0 <= i && i < self.buffer@.len() as int ==>
                self.instance@.backing_cells().index(i) === self.buffer@.index(i).id()
        }

        invariant on end_idx with (instance) is (v: u64, g: VBQueue::end_idx<T>) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
        }
    }
}

impl<T> VBBuffer<T> {
    fn checkout_first_two(&mut self, to_put: T) -> (t: Option<&[PCell<T>]>)
        requires
            old(self).wf(),
            old(self).buffer.len() > 1,
        ensures
            self.wf(),
            match t {
                Option::Some(tt) => {
                    tt == to_put
                }
                Option::None => {
                    true
                }
            },
    {
        let tracked mut cell_perm: Option<cell::PointsTo<T>>;

        let current_end_idx =
            atomic_with_ghost!(&self.end_idx => compare_exchange(0, 2);
                update old_val -> new_val;
                returning ret;
                ghost end_idx_token => {
                    match ret {
                        Result::Ok(prev) => {
                            assert(prev == 0);
                            assert(old_val == 0);
                            assert(new_val == 2);
                            assert(end_idx_token.value() == 0);
                            let tracked (_, Tracked(mut cp)) = self.instance.borrow_mut().checkout_first_two(&mut end_idx_token);
                            cell_perm = Option::Some(cp.tracked_remove(0));
                            assert(end_idx_token.value() == new_val);
                        }
                        Result::Err(prev) => {
                            assert(old_val == new_val);
                            cell_perm = Option::None;
                        }
                    };
                }
        );

        // current_end_idx は Compare Exchange が成功していたら Result::Ok(old_val) が入っている。
        // 失敗していたら Err(old_val) が入っている
        match current_end_idx {
            Result::Ok(_) => {
                // cell_perm を Unwrap して確認
                let tracked mut cell_perm = match cell_perm {
                    Option::Some(cp) => cp,
                    Option::None => {
                        assert(false);
                        proof_from_false()
                    },
                };

                self.buffer[0].put(Tracked(&mut cell_perm), to_put);
                let t = self.buffer[0].take(Tracked(&mut cell_perm));
                return Option::Some(t);
            }
            Result::Err(_) => {
                return Option::None
            }
        }
    }
}

fn new_buf<T>(len: usize) -> (vbuf: VBBuffer<T>)
    requires
        len > 0,
    ensures
        vbuf.wf(),
        vbuf.buffer@.len() == len,
{
    // Initialize the vector to store the cells
    let mut backing_cells_vec = Vec::<PCell<T>>::new();
    // Initialize map for the permissions to the cells
    // (keyed by the indices into the vector)
    let tracked mut perms = Map::<nat, cell::PointsTo<T>>::tracked_empty();
    for cell_i in 0..len
        invariant
            forall|j: nat|
                #![trigger( perms.dom().contains(j) )]
                #![trigger( backing_cells_vec@.index(j as int) )]
                #![trigger( perms.index(j) )]
                0 <= j && j < backing_cells_vec.len() as int ==> perms.dom().contains(j)
                    && backing_cells_vec@.index(j as int).id() === perms.index(j).id()
                    && perms.index(j).is_uninit(),
            backing_cells_vec.len() == cell_i,
        decreases
            len - cell_i,
    {
        let ghost i = backing_cells_vec.len();
        let (cell, cell_perm) = PCell::empty();
        backing_cells_vec.push(cell);
        proof {
            perms.tracked_insert(i as nat, cell_perm.get());
        }
        assert(perms.dom().contains(i as nat));
        assert(backing_cells_vec@.index(i as int).id() === perms.index(i as nat).id());
        assert(perms.index(i as nat).is_uninit());
    }
    proof {
        assert(backing_cells_vec@.len() == len);
    }
    // Vector for ids
    let ghost mut backing_cells_ids = Seq::<CellId>::new(
        backing_cells_vec@.len(),
        |i: int| backing_cells_vec@.index(i).id(),
    );
    // Initialize an instance of the VBQueue
    let tracked (
        Tracked(instance),
        Tracked(end_idx_token),
    ) = VBQueue::Instance::initialize(backing_cells_ids, perms /* storage */, perms /* param token storage */);

    let tracked_inst: Tracked<VBQueue::Instance<T>> = Tracked(instance.clone());
    let end_idx_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(end_idx_token));

    // Initialize the queue
    VBBuffer::<T> {
        buffer: backing_cells_vec,
        end_idx: end_idx_atomic,
        instance: Tracked(instance),
    }
}

fn main() {
    let mut vbuf : VBBuffer<u32> = new_buf(5);
    let val: u32 = 555;
    proof {
        assert(vbuf.buffer@.len() == 5)
    }

    let x = vbuf.checkout_first_two(val);

    assert(match x {
        Option::Some(xx) => {
            xx == val
        }
        Option::None => {
            true
        }
    });
}
} // verus