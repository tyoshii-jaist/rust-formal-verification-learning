use state_machines_macros::tokenized_state_machine;
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
        }
    }

    /*
    transition!{
        reserve(sz: nat) {
            withdraw storage -= [tail => let perm] by {
                assert(pre.valid_storage_at_idx(tail));
            };

            // The transition needs to guarantee to the client that the
            // permission they are checking out:
            //  (i) is for the cell at index `tail` (the IDs match)
            //  (ii) the permission indicates that the cell is empty
            assert(
                perm.id() === pre.backing_cells.index(tail as int)
                && perm.is_uninit()
            ) by {
                assert(!pre.in_active_range(tail));
                assert(pre.valid_storage_at_idx(tail));
            };
        }
    }
     */
}} // tokenized_state_machine

pub struct VBBuffer<T> {
    buffer: Vec<PCell<T>>,
    instance: Tracked<VBQueue::Instance<T>>,
}

impl<T> VBBuffer<T> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.instance@.backing_cells().len() == self.buffer@.len()
        &&& forall|i: int| 0 <= i && i < self.buffer@.len() as int ==>
            self.instance@.backing_cells().index(i) === self.buffer@.index(i).id()
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
    // Initialize an instance of the FIFO queue
    let tracked instance = VBQueue::Instance::initialize(backing_cells_ids, perms /* storage */, perms /* param token storage */);

    // Initialize the queue
    VBBuffer::<T> {
        instance: Tracked(instance),
        buffer: backing_cells_vec,
    }
}

fn main() {
    let _ : VBBuffer<u32> = new_buf(5);
}
} // verus