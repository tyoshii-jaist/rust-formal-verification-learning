use state_machines_macros::tokenized_state_machine;
use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::cell::*;
use vstd::map::*;
use vstd::{pervasive::*, prelude::*, *};

verus! {
tokenized_state_machine!{VBQueue<T> {
    fields {
        #[sharding(constant)]
        pub backing_cells: Seq<CellId>,

        // All the stored permissions

        #[sharding(storage_map)]
        pub storage: Map<nat, cell::PointsTo<T>>,

        // Represents the shared `head` field

        #[sharding(variable)]
        pub write: nat,

        // Represents the shared `tail` field

        #[sharding(variable)]
        pub reserve: nat,
    }

    pub open spec fn len(&self) -> nat {
        self.backing_cells.len()
    }

    pub open spec fn add_wrap(i: nat, sz: nat, len: nat) -> (nat, bool) {
        if i + sz >= len { (i + sz - len, true) } else { (i + sz, false) }
    }

    // Indicates whether we expect the cell at index `i` to be full based on
    // the values of the `head` and `tail`.

    pub open spec fn in_active_range(&self, i: nat) -> bool {
        // Note that self.head = self.tail means empty range
        0 <= i && i < self.len() && (
            if self.write <= self.reserve {
                self.write <= i && i < self.reserve
            } else {
                i >= self.write || i < self.reserve
            }
        )
    }

    // Predicate to determine that the state at cell index `i`
    // is correct. For each index, there are three possibilities:
    //
    //  1. No cell permission is stored
    //  2. Permission is stored; permission indicates a full cell
    //  3. Permission is stored; permission indicates an empty cell
    //
    // Which of these 3 possibilities we should be in depends on the
    // producer/consumer/head/tail state.

    pub open spec fn valid_storage_at_idx(&self, i: nat) -> bool {
        // TODO: Checked out の状態も考慮する必要がある
        // Permission is stored
        self.storage.dom().contains(i)
        // Permission must be for the correct cell:
        && self.storage.index(i).id() === self.backing_cells.index(i as int)
        && if self.in_active_range(i) {
            // The cell is full
            self.storage.index(i).is_init()
        } else {
            // The cell is empty
            self.storage.index(i).is_uninit()
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
            init write = 0;
            init reserve = 0;
        }
    }

    transition!{
        reserve_start(sz: nat) {
            // In order to begin, we have to be in ProducerState::Idle.
            // require(pre.producer is Idle);

            // We'll be comparing the producer's _local_ copy of the tail
            // with the _shared_ version of the head.
            let write = pre.write;

            // assert(0 <= tail && tail < pre.backing_cells.len());

            // Compute the incremented tail, wrapping around if necessary.
            let (next_reserve, wrapped) = Self::add_wrap(write, sz, pre.backing_cells.len());

            // We have to check that the buffer isn't full to proceed.
            require(!wrapped || next_reserve <= write);

            // Update the producer's local state to be in the `Producing` state.
            // update producer = ProducerState::Producing(tail);
            update reserve = next_reserve;

            // Withdraw ("check out") the permission stored at index `tail`.
            // This creates a proof obligation for the transition system to prove that
            // there is actually a permission stored at this index.
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
}} // tokenized_state_machine

struct_with_invariants!{
    struct VBBuffer<T> {
        buffer: Vec<PCell<T>>,
        write: AtomicU64<_, VBQueue::write<T>, _>,
        reserve: AtomicU64<_, VBQueue::reserve<T>, _>,

        instance: Tracked<VBQueue::Instance<T>>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            // The Cell IDs in the instance protocol match the cell IDs in the actual vector:
            &&& self.instance@.backing_cells().len() == self.buffer@.len()
            &&& forall|i: int| 0 <= i && i < self.buffer@.len() as int ==>
                self.instance@.backing_cells().index(i) ===
                    self.buffer@.index(i).id()
        }

        invariant on head with (instance) is (v: u64, g: VBQueue::write<T>) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
        }

        invariant on tail with (instance) is (v: u64, g: VBQueue::reserve<T>) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
        }
    }
}

pub struct Producer<T> {
    buf: Arc<VBBuffer<T>>,
    write: usize,
    reserve: usize,
    //producer: Tracked<FifoQueue::producer<T>>,
}

impl<T> Producer<T> {
    pub closed spec fn wf(&self) -> bool {
        (*self.buf).wf()
            && self.producer@.instance_id() == (*self.buf).instance@.id()
            && self.producer@.value() == ProducerState::Idle(self.tail as nat)
            && (self.tail as int) < (*self.buf).buffer@.len()
    }
}

impl<T> Producer<T> {
    pub closed spec fn wf(&self) -> bool {
        (*self.buf).wf()
            && self.producer@.instance_id() == (*self.buf).instance@.id()
            //&& self.producer@.value() == ProducerState::Idle(self.tail as nat)
            && (self.write as int) < (*self.buf).buffer@.len()
            && (self.reserve as int) < (*self.buf).buffer@.len()
    }
}


pub fn new_buf<T>(len: usize) -> (p: Producer)
    requires
        len > 0,
    ensures
        p.wf(),
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
    let tracked (
        Tracked(instance),
        Tracked(write_token),
        Tracked(reserve_token),
    ) = VBQueue::Instance::initialize(backing_cells_ids, perms /* storage */, perms /* param token storage */); // なぜ perms が二つ必要なのか？
    // Initialize atomics
    let tracked_inst: Tracked<VBQueue::Instance<T>> = Tracked(instance.clone());
    let write_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(head_token));
    let reserve_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(tail_token));
    // Initialize the queue
    let queue = VBQueue::<T> {
        instance: Tracked(instance),
        write: write_atomic,
        reserve: reserve_atomic,
        buffer: backing_cells_vec,
    };
    // Share the queue between the producer and consumer
    let queue_arc = Arc::new(queue);
    let prod = Producer::<T> {
        queue: queue_arc.clone(),
        write: 0,
        reserve: 0,
        //producer: Tracked(producer_token),
    };

    prod
}

impl<T> Producer<T> {
    #[verifier::exec_allows_no_decreases_clause]
    fn reserve(&mut self, size: usize) -> (v: Vec<T>)
        requires
            size <= old((*self.queue).buffer@.len()),
            old(self).wf(),
        ensures
            self.wf(),
    {
        // Loop: if the queue is full, then block until it is not.
        loop
            invariant
                self.wf(),
        {
            let queue = &*self.queue;
            let len = queue.buffer.len();
            assert(size < len);
            // Calculate the index of the slot right after `tail`, wrapping around
            // if necessary. If the enqueue is successful, then we will be updating
            // the `tail` to this value.
            let (next_reserve, wrapped) = if self.reserve + size >= len {
                (size, true)
            } else {
                (self.reserve + size, false)
            };
            let tracked cell_perm: Option<cell::PointsTo<T>>;
            // Get the current `write` value from the shared atomic.
            let write =
                atomic_with_ghost!(&queue.write => load();
                returning write;
                ghost write_token => {
                    cell_perm = if !wrapped || next_reserve <= write {
                        let tracked cp = queue.instance.borrow().reserve_start(next_reserve, &reserve_token, self.producer.borrow_mut());
                        Option::Some(cp)
                    } else {
                        Option::None
                    };
                }
            );
            let reserve =
                atomic_with_ghost!(&queue.reserve => load();
                returning reserve;
                ghost reserve_token => {

                }
            );
            // Here's where we "actually" do the `head != next_tail` check:
            if head != next_tail as u64 {
                // Unwrap the cell_perm from the option.
                let tracked mut cell_perm = match cell_perm {
                    Option::Some(cp) => cp,
                    Option::None => {
                        assert(false);
                        proof_from_false()
                    },
                };
                // Write the element t into the buffer, updating the cell
                // from uninitialized to initialized (to the value t).
                queue.buffer[self.tail].put(Tracked(&mut cell_perm), t);
                // Store the updated tail to the shared `tail` atomic,
                // while performing the `produce_end` transition.
                atomic_with_ghost!(&queue.tail => store(next_tail as u64); ghost tail_token => {
                    queue.instance.borrow().produce_end(cell_perm,
                        cell_perm, &mut tail_token, self.producer.borrow_mut());
                });
                self.tail = next_tail;
                return ;
            }
        }
    }
}

} // verus