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
        pub start: nat,
    }

    pub open spec fn len(&self) -> nat {
        self.backing_cells.len()
    }


    pub open spec fn valid_storage_at_idx(&self, i: nat) -> bool {
        if !self.storage.dom().contains(i) {
            true
        } else {
            // Permission is stored
            self.storage.dom().contains(i)

            // Permission must be for the correct cell:
            && self.storage.index(i).id() === self.backing_cells.index(i as int)

            && self.storage.index(i).is_uninit()
        }
    }

    #[invariant]
    pub fn valid_storage_all(&self) -> bool {
        forall|i: nat| 0 <= i && i < self.len() ==>
            self.valid_storage_at_idx(i)
    }

    init!{
        initialize(backing_cells: Seq<CellId>, storage: Map<nat, cell::PointsTo<T>>) {
            // Upon initialization, the user needs to deposit _all_ the relevant
            // cell permissions to start with. Each permission should indicate
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
            init start = 0;
        }
    }

    transition!{
        checkout_first() {
            /*
            withdraw storage -= [0 => let perm] by {
                assert(pre.valid_storage_at_idx(0));
            };

            // The transition needs to guarantee to the client that the
            // permission they are checking out:
            //  (i) is for the cell at index `tail` (the IDs match)
            //  (ii) the permission indicates that the cell is empty
            assert(
                perm.id() === pre.backing_cells.index(0)
                && perm.is_uninit()
            ) by {
                assert(pre.valid_storage_at_idx(0));
            };
             */
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

    #[inductive(checkout_first)]
    fn checkout_first_inductive(pre: Self, post: Self) {
        /*
        assert forall|i: nat|
            0 <= i && i < pre.len() implies pre.valid_storage_at_idx(i)
        by {
            assert(pre.storage.dom().contains(i));
        }
        assert(forall|i| pre.valid_storage_at_idx(i) ==> post.valid_storage_at_idx(i));
        assert forall|i: nat|
            0 <= i && i < post.len() implies post.valid_storage_at_idx(i)
        by {
            assert(post.storage.dom().contains(i));
        } */
    }
}} // tokenized_state_machine

struct_with_invariants!{
    pub struct VBBuffer<T> {
        buffer: Vec<PCell<T>>,
        start: AtomicU64<_, VBQueue::start<T>, _>,
        instance: Tracked<VBQueue::Instance<T>>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            &&& self.instance@.backing_cells().len() == self.buffer@.len()
            &&& forall|i: int| 0 <= i && i < self.buffer@.len() as int ==>
                self.instance@.backing_cells().index(i) === self.buffer@.index(i).id()
        }

        invariant on start with (instance) is (v: u64, g: VBQueue::start<T>) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
        }
    }
}

impl<T> VBBuffer<T> {
    fn checkout_first(&mut self)
        requires
            old(self).wf(),
        ensures
            self.wf(),
    {
        let start =
            atomic_with_ghost!(&self.start => load();
            returning start;
            ghost start_token => {
                let tracked _ = self.instance.borrow().checkout_first();
            }
        );
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
        Tracked(start_token),
    ) = VBQueue::Instance::initialize(backing_cells_ids, perms /* storage */, perms /* param token storage */);

    let tracked_inst: Tracked<VBQueue::Instance<T>> = Tracked(instance.clone());
    let start_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(start_token));

    // Initialize the queue
    VBBuffer::<T> {
        instance: Tracked(instance),
        start: start_atomic,
        buffer: backing_cells_vec,
    }
}

fn main() {
    let mut vbuf : VBBuffer<u32> = new_buf(5);
    let _ = vbuf.checkout_first();
}
} // verus