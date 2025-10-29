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
        pub prod_checkout_idx: nat,

        #[sharding(variable)]
        pub cons_checkout_idx: nat,
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
        (self.prod_checkout_idx > 0 && i == self.prod_checkout_idx - 1) ||
        (self.cons_checkout_idx > 0 && i == self.cons_checkout_idx - 1)
    }

    #[invariant]
    pub fn valid_storage_all(&self) -> bool {
        forall|i: nat| 0 <= i && i < self.len() ==>
            self.valid_storage_at_idx(i)
    }

    #[invariant]
    pub fn in_bounds(&self) -> bool {
        &&& 0 < self.len()
        &&& 0 <= self.prod_checkout_idx && self.prod_checkout_idx <= self.len()
        &&& 0 <= self.cons_checkout_idx && self.cons_checkout_idx <= self.len()
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
            init prod_checkout_idx = 0;
            init cons_checkout_idx = 0;
        }
    }

    transition!{
        prod_checkout_at(idx: nat) {
            require(0 <= idx && idx < pre.backing_cells.len());

            assert(pre.prod_checkout_idx - 1 != idx);

            withdraw storage -= [idx => let perm] by {
                assert(pre.valid_storage_at_idx(idx));
            };

            update prod_checkout_idx = idx + 1;

            assert(
                perm.id() === pre.backing_cells.index(idx as int)
                && perm.is_uninit()
            ) by {
                assert(pre.valid_storage_at_idx(idx));
            };
        }
    }

    transition!{
        cons_checkout_at(idx: nat) {
            require(0 <= idx && idx < pre.backing_cells.len());

            require(pre.cons_checkout_idx - 1 != idx);

            withdraw storage -= [idx => let perm] by {
                assert(pre.valid_storage_at_idx(idx));
            };

            update cons_checkout_idx = idx + 1;

            assert(
                perm.id() === pre.backing_cells.index(idx as int)
                && perm.is_uninit()
            ) by {
                assert(pre.valid_storage_at_idx(idx));
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

    #[inductive(prod_checkout_at)]
    fn prod_checkout_at_inductive(pre: Self, post: Self, idx: nat) {
        assert(!pre.is_checked_out(idx));
        assert(forall|i| pre.valid_storage_at_idx(i) ==> post.valid_storage_at_idx(i)) by {
        }
        assert(post.is_checked_out(idx));
    }
    
    #[inductive(cons_checkout_at)]
    fn cons_checkout_at_inductive(pre: Self, post: Self, idx: nat) {
        assert(!pre.is_checked_out(idx));
        assert(forall|i| pre.valid_storage_at_idx(i) ==> post.valid_storage_at_idx(i)) by {
        }
        assert(post.is_checked_out(idx));
    }
}} // tokenized_state_machine

struct_with_invariants!{
    pub struct VBBuffer<T> {
        buffer: Vec<PCell<T>>,
        prod_checkout_idx: AtomicU64<_, VBQueue::prod_checkout_idx<T>, _>,
        cons_checkout_idx: AtomicU64<_, VBQueue::cons_checkout_idx<T>, _>,
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

        invariant on prod_checkout_idx with (instance) is (v: u64, g: VBQueue::prod_checkout_idx<T>) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
        }

        invariant on cons_checkout_idx with (instance) is (v: u64, g: VBQueue::cons_checkout_idx<T>) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
        }
    }
}

impl<T> VBBuffer<T> {
    fn prod_checkout_at(&mut self, at: usize, to_put: T) -> (t: Option<T>)
        requires
            old(self).wf(),
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

        let current_prod_checkout_idx =
            atomic_with_ghost!(&self.prod_checkout_idx => compare_exchange(0, 1);
                update old_val -> new_val;
                returning ret;
                ghost prod_checkout_idx_token => {
                    match ret {
                        Result::Ok(prev) => {
                            assert(prev == 0);
                            assert(old_val == 0);
                            assert(new_val == 1);
                            assert(prod_checkout_idx_token.value() == 0);
                            let tracked cp = self.instance.borrow_mut().prod_checkout_at(at as nat, &mut prod_checkout_idx_token);
                            cell_perm = Option::Some(cp);
                            assert(prod_checkout_idx_token.value() == new_val);
                        }
                        Result::Err(prev) => {
                            assert(old_val == new_val);
                            cell_perm = Option::None;
                        }
                    };
                }
        );

        // current_prod_checkout_idx は Compare Exchange が成功していたら Result::Ok(old_val) が入っている。
        // 失敗していたら Err(old_val) が入っている
        match current_prod_checkout_idx {
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

pub fn new_buf<T>(len: usize) -> (vbuf: VBBuffer<T>)
    requires
        len > 0,
    ensures
        vbuf.wf(),
{
    // Initialize the vector to store the cells
    let mut backing_cells_vec = Vec::<PCell<T>>::new();
    // Initialize map for the permissions to the cells
    // (keyed by the indices into the vector)
    let tracked mut perms = Map::<nat, cell::PointsTo<T>>::tracked_empty();
    while backing_cells_vec.len() < len
        invariant
            forall|j: nat|
                #![trigger( perms.dom().contains(j) )]
                #![trigger( backing_cells_vec@.index(j as int) )]
                #![trigger( perms.index(j) )]
                0 <= j && j < backing_cells_vec.len() as int ==> perms.dom().contains(j)
                    && backing_cells_vec@.index(j as int).id() === perms.index(j).id()
                    && perms.index(j).is_uninit(),
        decreases
            len - backing_cells_vec.len(),
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
    // Vector for ids
    let ghost mut backing_cells_ids = Seq::<CellId>::new(
        backing_cells_vec@.len(),
        |i: int| backing_cells_vec@.index(i).id(),
    );
    // Initialize an instance of the VBQueue
    let tracked (
        Tracked(instance),
        Tracked(prod_checkout_idx_token),
        Tracked(cons_checkout_idx_token),
    ) = VBQueue::Instance::initialize(backing_cells_ids, perms /* storage */, perms /* param token storage */);

    let tracked_inst: Tracked<VBQueue::Instance<T>> = Tracked(instance.clone());
    let prod_checkout_idx_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(prod_checkout_idx_token));
    let cons_checkout_idx_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(cons_checkout_idx_token));

    // Initialize the queue
    VBBuffer::<T> {
        buffer: backing_cells_vec,
        prod_checkout_idx: prod_checkout_idx_atomic,
        cons_checkout_idx: cons_checkout_idx_atomic,
        instance: Tracked(instance),
    }
}

fn main() {
    let mut vbuf : VBBuffer<u32> = new_buf(5);
    let val: u32 = 555;

    let x = vbuf.prod_checkout_at(0, val);

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