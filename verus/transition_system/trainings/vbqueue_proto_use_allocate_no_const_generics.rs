use state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
//use vstd::atomic_ghost::*;
use vstd::raw_ptr::*;
//use vstd::cell::*;
//use vstd::map::*;
use vstd::{prelude::*, *};
//use vstd::modes::*;
use vstd::layout::*;
use std::sync::Arc;

verus! {
global layout u8 is size == 1, align == 1;

pub enum ProducerState {
    Idle((bool, nat)), // (write_in_progress, write)
    GrantStarted((bool, nat)), // (write_in_progress, write)
    GrantWriteLoaded((bool, nat)), // (write_in_progress, write)
    GrantWriteAndReadLoaded((bool, nat, nat)), // (write_in_progress, write, read)
    Reserved((bool, nat, nat)), // (write_in_progress, grant_start, grant_start + grant_sz)
    CommitWriteLoaded((bool, nat, nat, nat)),  // (write_in_progress, grant_start, grant_start + grant_sz, write)
    CommitReserveSubbed((bool, nat, nat, nat)), // (write_in_progress, grant_start, grant_start + grant_sz, write)
    CommitLastLoaded((bool, nat, nat, nat, nat)), // (write_in_progress, grant_start, grant_start + grant_sz, write, last)
    CommitReserveLoaded((bool, nat, nat, nat, nat, nat)), // (write_in_progress, grant_start, grant_start + grant_sz, write, last, reserve)
}

pub enum ConsumerState {
    Idle(nat),
}

 tokenized_state_machine!{VBQueue {
    fields {
        #[sharding(constant)]
        pub base_addr: nat,

        #[sharding(constant)]
        pub provenance: raw_ptr::Provenance,

        #[sharding(constant)]
        pub length: nat,

        #[sharding(storage_map)]
        pub storage: Map<nat, raw_ptr::PointsTo<u8>>,

        #[sharding(storage_option)]
        pub buffer_dealloc: Option<raw_ptr::Dealloc>,

        #[sharding(variable)]
        pub write: nat,

        #[sharding(variable)]
        pub read: nat,

        #[sharding(variable)]
        pub last: nat,

        #[sharding(variable)]
        pub reserve: nat,

        #[sharding(variable)]
        pub read_in_progress: bool,

        #[sharding(variable)]
        pub write_in_progress: bool,

        #[sharding(variable)]
        pub already_split: bool,

        // Represents the local state of the single-producer
        #[sharding(variable)]
        pub producer: ProducerState,

        // Represents the local state of the single-consumer
        #[sharding(variable)]
        pub consumer: ConsumerState,
    }

    /*
    #[invariant]
    pub fn valid_write_in_progress_in_producer(&self) -> bool {
        match self.producer {
            ProducerState::Idle((wip, _)) |
            ProducerState::GrantStarted((wip, _)) |
            ProducerState::GrantWriteLoaded((wip, _)) |
            ProducerState::GrantWriteAndReadLoaded((wip, _, _)) |
            ProducerState::Reserved((wip, _, _)) |
            ProducerState::CommitWriteLoaded((wip, _, _, _)) |
            ProducerState::CommitReserveSubbed((wip, _, _, _)) |
            ProducerState::CommitLastLoaded((wip, _, _, _, _)) |
            ProducerState::CommitReserveLoaded((wip, _, _, _, _, _)) => {
                wip == self.write_in_progress
            }
        }
    } */
    #[invariant]
    pub fn no_write_in_progress(&self) -> bool {
        !self.write_in_progress ==> self.producer is Idle &&
        self.producer is Idle ==> !self.write_in_progress
    }

    #[invariant]
    pub fn valid_storage_all(&self) -> bool {
        match self.producer {
            ProducerState::Reserved((_, grant_start, grant_end)) |
            ProducerState::CommitWriteLoaded((_, grant_start, grant_end, _)) |
            ProducerState::CommitReserveSubbed((_, grant_start, grant_end, _)) |
            ProducerState::CommitLastLoaded((_, grant_start, grant_end, _, _)) |
            ProducerState::CommitReserveLoaded((_, grant_start, grant_end, _, _, _)) => {
                &&& forall |i: nat|
                    ((i >= self.base_addr && i < self.base_addr + grant_start as nat) || 
                    (i >= self.base_addr + grant_end && i < self.base_addr + self.length))
                        ==> (
                            self.storage.contains_key(i)
                        )
                &&& forall |i: nat|
                    (i >= self.base_addr + grant_start && i < self.base_addr + grant_end as nat)
                        ==> (
                            !self.storage.contains_key(i)
                        )
                &&& forall |i: nat|
                    ((i >= self.base_addr && i < self.base_addr + grant_start as nat) || 
                    (i >= self.base_addr + grant_end && i < self.base_addr + self.length))
                        ==> (
                            self.storage.index(i).ptr().addr() == i
                        )
                &&& forall |i: nat|
                    ((i >= self.base_addr && i < self.base_addr + grant_start as nat) || 
                    (i >= self.base_addr + grant_end && i < self.base_addr + self.length))
                        ==> (
                            self.storage.index(i).ptr()@.provenance == self.provenance
                        )
            },
            _ => {
                &&& forall |i: nat| i >= self.base_addr && i < self.base_addr + self.length <==> self.storage.contains_key(i)
                &&& forall |i: nat| i >= self.base_addr && i < self.base_addr + self.length ==> self.storage.index(i).ptr().addr() == i
                &&& forall |i: nat| i >= self.base_addr && i < self.base_addr + self.length ==> self.storage.index(i).ptr()@.provenance == self.provenance
            },
        }
    }

    #[invariant]
    pub fn valid_producer_local_state(&self) -> bool {
        match self.producer {
            ProducerState::Idle((wip, idle)) => self.write_in_progress == false && wip == self.write_in_progress && self.write == idle,
            ProducerState::GrantStarted((wip, idle)) => self.write_in_progress == true && wip == self.write_in_progress && self.write == idle,
            ProducerState::GrantWriteLoaded((wip, write)) => self.write_in_progress == true && wip == self.write_in_progress && self.write == write,
            ProducerState::GrantWriteAndReadLoaded((wip, write, _)) => self.write_in_progress == true && wip == self.write_in_progress && self.write == write,
            ProducerState::Reserved((wip, _, reserve_end)) => self.write_in_progress == true && wip == self.write_in_progress && self.reserve == reserve_end,
            // (reserve_start, reserve_end, write, last, reserve)
            ProducerState::CommitWriteLoaded((wip, reserve_start, reserve_end, write)) => self.write_in_progress == true && wip == self.write_in_progress && self.write == write && self.reserve == reserve_end,
            ProducerState::CommitReserveSubbed((wip, reserve_start, reserve_end, write)) => self.write_in_progress == true && wip == self.write_in_progress && self.write == write,
            ProducerState::CommitLastLoaded((wip, reserve_start, reserve_end, write, last)) => self.write_in_progress == true && wip == self.write_in_progress && self.write == write && self.last == last,
            ProducerState::CommitReserveLoaded((wip, reserve_start, reserve_end, write, last, reserve)) => self.write_in_progress == true && wip == self.write_in_progress && self.write == write && self.reserve == reserve && self.last == last,
        }
    }

    init! {
        initialize(
            base_addr: nat,
            provenance: raw_ptr::Provenance,
            length: nat,
            storage: Map<nat, raw_ptr::PointsTo<u8>>,
            buffer_dealloc: raw_ptr::Dealloc)
        {
            require(
                {
                    &&& forall |i: nat| i >= base_addr && i < base_addr + length <==> storage.contains_key(i)
                    &&& forall |i: nat| i >= base_addr && i < base_addr + length ==> storage.index(i).ptr().addr() == i
                    &&& forall |i: nat| i >= base_addr && i < base_addr + length ==> storage.index(i).ptr()@.provenance == provenance
                }
            );

            init base_addr = base_addr;
            init provenance = provenance;
            init length = length;
            init storage = storage;
            init buffer_dealloc = Some(buffer_dealloc);
            init write = 0;
            init read = 0;
            init last = length;
            init reserve = 0;
            init read_in_progress = false;
            init write_in_progress = false;
            init already_split = false;

            init producer = ProducerState::Idle((false, 0));
            init consumer = ConsumerState::Idle(0);
        }
    }

    
    #[inductive(initialize)]
    fn initialize_inductive(post: Self, base_addr: nat, provenance: raw_ptr::Provenance, length: nat, storage: Map<nat, raw_ptr::PointsTo<u8>>, buffer_dealloc: raw_ptr::Dealloc) {
        assert(post.producer is Idle);
        assert(post.buffer_dealloc is Some);
    }

    transition!{
        try_split() {
            require(pre.already_split == false);

            update already_split = true;
        }
    }

    transition!{
        grant_start() {
            require(pre.producer is Idle);
            require(pre.write_in_progress == false);

            update write_in_progress = true;
            update producer = ProducerState::GrantStarted((true, pre.producer->Idle_0.1));
        }
    }

    transition!{
        grant_load_write() {
            require(pre.producer is GrantStarted);

            update producer = ProducerState::GrantWriteLoaded((pre.producer->GrantStarted_0.0, pre.write));
        }
    }

    transition!{
        grant_load_read() {
            require(pre.producer is GrantWriteLoaded);

            update producer = ProducerState::GrantWriteAndReadLoaded((pre.producer->GrantWriteLoaded_0.0, pre.producer->GrantWriteLoaded_0.1, pre.read));
        }
    }

    transition!{
        do_reserve(start: nat, sz: nat) {
            require(start + sz <= pre.length);
            require(pre.producer is GrantWriteAndReadLoaded);

            update reserve = start + sz;

            birds_eye let range_keys = Set::new(|i: nat| pre.base_addr + start <= i && i < pre.base_addr + start + sz);
            // restrict を使わないとうまく pre.storage の情報が引き継がれない?
            birds_eye let withdraw_range_map = pre.storage.restrict(range_keys);

            withdraw storage -= (withdraw_range_map) by {
                assert(withdraw_range_map.submap_of(pre.storage)) by {
                    // assert(Set::new(|i: nat| i >= start + pre.base_addr && i < start + sz  + pre.base_addr).subset_of(Set::new(|i: nat| i >= pre.base_addr && i < pre.base_addr + pre.length)));
                    // assert(Set::new(|i: nat| i >= pre.base_addr && i < pre.base_addr + pre.length).subset_of(pre.storage.dom()));
                    assert(withdraw_range_map.dom().subset_of(Set::new(|i: nat| i >= start + pre.base_addr && i < start + sz + pre.base_addr)));
                    assert(pre.valid_storage_all());
                    assert(forall |j: nat| j >= pre.base_addr + start && j < pre.base_addr as nat + start + sz <==> pre.storage.contains_key(j));
                    assert(forall |j: nat| j >= pre.base_addr + start && j < pre.base_addr as nat + start + sz ==> pre.storage.index(j).ptr().addr() == j);
                    assert(forall |j: nat| j >= pre.base_addr + start && j < pre.base_addr as nat + start + sz ==> pre.storage.index(j).ptr()@.provenance == pre.provenance);
                }
            };
            
            update producer = ProducerState::Reserved((pre.producer->GrantWriteAndReadLoaded_0.0, start, start + sz));

            assert(
                withdraw_range_map.dom().subset_of(Set::new(|i: nat| i >= start + pre.base_addr && i < start + sz + pre.base_addr))
            );
            assert(
                Set::new(|i: nat| i >= start + pre.base_addr && i < start + sz + pre.base_addr).subset_of(withdraw_range_map.dom())
            );
            assert(forall |j: nat| j >= pre.base_addr + start && j < pre.base_addr as nat + start + sz ==> withdraw_range_map.contains_key(j));
            assert(forall |j: nat| j >= pre.base_addr + start && j < pre.base_addr as nat + start + sz ==> withdraw_range_map.index(j).ptr().addr() == j);
            assert(forall |j: nat| j >= pre.base_addr + start && j < pre.base_addr as nat + start + sz ==> withdraw_range_map.index(j).ptr()@.provenance == pre.provenance);
        }
    }

    transition!{
        grant_fail() {
            require(pre.producer is GrantWriteAndReadLoaded);

            update write_in_progress = false;
            update producer = ProducerState::Idle((false, pre.producer->GrantWriteAndReadLoaded_0.1));
        }
    }

    transition!{
        commit_start() {
            require(pre.producer is Idle || pre.producer is Reserved);
            //assert(!pre.write_in_progress ==> pre.producer is Idle && pre.producer is Idle ==> !pre.write_in_progress);
            if !pre.write_in_progress {
                assert(pre.producer is Idle);
            } else {
                assert(pre.producer is Reserved);
            }
        }
    }

    transition!{
        commit_load_write() {
            require(pre.producer is Reserved);

            update producer = ProducerState::CommitWriteLoaded((pre.producer->Reserved_0.0, pre.producer->Reserved_0.1, pre.producer->Reserved_0.2, pre.write));
        }
    }

    transition!{
        commit_sub_reserve(commited: nat) {
            require(pre.producer is CommitWriteLoaded);
            assert(pre.reserve == pre.producer->CommitWriteLoaded_0.2); // 重要!
            require(pre.reserve >= commited);

            let new_reserve = (pre.reserve - commited) as nat;

            update reserve = new_reserve;
            update producer = ProducerState::CommitReserveSubbed((pre.producer->CommitWriteLoaded_0.0, pre.producer->CommitWriteLoaded_0.1, pre.producer->CommitWriteLoaded_0.2, pre.producer->CommitWriteLoaded_0.3));
        }
    }    

    transition!{
        commit_load_last() {
            require(pre.producer is CommitReserveSubbed);

            update producer = ProducerState::CommitLastLoaded(
                (pre.producer->CommitReserveSubbed_0.0, pre.producer->CommitReserveSubbed_0.1, pre.producer->CommitReserveSubbed_0.2, pre.producer->CommitReserveSubbed_0.3, pre.last)
            );
        }
    }

    transition!{
        commit_load_reserve() {
            require(pre.producer is CommitLastLoaded);

            update producer = ProducerState::CommitReserveLoaded(
                (pre.producer->CommitLastLoaded_0.0, pre.producer->CommitLastLoaded_0.1, pre.producer->CommitLastLoaded_0.2, pre.producer->CommitLastLoaded_0.3, pre.producer->CommitLastLoaded_0.4, pre.reserve)
            );
        }
    }

    transition!{
        commit_store_last(new_last: nat) {
            require(pre.producer is CommitReserveLoaded);

            update last = new_last;

            update producer = ProducerState::CommitReserveLoaded(
                (pre.producer->CommitReserveLoaded_0.0, pre.producer->CommitReserveLoaded_0.1, pre.producer->CommitReserveLoaded_0.2, pre.producer->CommitReserveLoaded_0.3, new_last, pre.producer->CommitReserveLoaded_0.5)
            );
        }
    }

    transition!{
        commit_store_write(new_write: nat) {
            require(pre.producer is CommitReserveLoaded);

            update write = new_write;

            update producer = ProducerState::CommitReserveLoaded(
                (pre.producer->CommitReserveLoaded_0.0, pre.producer->CommitReserveLoaded_0.1, pre.producer->CommitReserveLoaded_0.2, new_write, pre.producer->CommitReserveLoaded_0.4, pre.producer->CommitReserveLoaded_0.5)
            );
        }
    }

    transition!{
        commit_end(to_deposit: Map::<nat, vstd::raw_ptr::PointsTo<u8>>) {
            require(pre.producer is CommitReserveLoaded);

            deposit storage += (to_deposit) by {
                assert(forall |i: nat| to_deposit.contains_key(i)
                        ==> !pre.storage.contains_key(i));
            };

            update write_in_progress = false;
            update producer = ProducerState::Idle((false, pre.producer->CommitReserveLoaded_0.3));
        }
    }

    #[inductive(try_split)]
    fn try_split_inductive(pre: Self, post: Self) { }

    #[inductive(grant_start)]
    fn grant_start_inductive(pre: Self, post: Self) { }

    #[inductive(grant_load_write)]
    fn grant_load_write_inductive(pre: Self, post: Self) {
        assert(post.producer is GrantWriteLoaded);
    }

    #[inductive(grant_load_read)]
    fn grant_load_read_inductive(pre: Self, post: Self) {
        assert(post.producer is GrantWriteAndReadLoaded);
    }

    #[inductive(grant_fail)]
    fn grant_fail_inductive(pre: Self, post: Self) { }

    #[inductive(do_reserve)]
    fn do_reserve_inductive(pre: Self, post: Self, start: nat, sz: nat) {        
        assert(post.producer is Reserved);
        // assert(post.producer->Reserved_0.0 == post.write);
        assert(post.producer->Reserved_0.2 == post.reserve);
    }

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self) {
        if post.producer is Idle {
            assert(
                {
                    &&& forall |i: nat| i >= post.base_addr && i < post.base_addr + post.length ==> post.storage.contains_key(i)
                    &&& forall |i: nat| i >= post.base_addr && i < post.base_addr + post.length ==> post.storage.index(i).ptr().addr() == i
                    &&& forall |i: nat| i >= post.base_addr && i < post.base_addr + post.length ==> post.storage.index(i).ptr()@.provenance == post.provenance
                }
            );
        }
    }

    #[inductive(commit_load_write)]
    fn commit_load_write_inductive(pre: Self, post: Self) {
        assert(post.producer->CommitWriteLoaded_0.2 == post.reserve);
    }

    #[inductive(commit_sub_reserve)]
    fn commit_sub_reserve_inductive(pre: Self, post: Self, commited: nat) {
        assert(pre.producer->CommitWriteLoaded_0.2 == pre.reserve);
    }

    #[inductive(commit_load_last)]
    fn commit_load_last_inductive(pre: Self, post: Self) { }

    #[inductive(commit_load_reserve)]
    fn commit_load_reserve_inductive(pre: Self, post: Self) { }

    #[inductive(commit_store_last)]
    fn commit_store_last_inductive(pre: Self, post: Self, new_last: nat) { }

    #[inductive(commit_store_write)]
    fn commit_store_write_inductive(pre: Self, post: Self, new_write: nat) { }

    #[inductive(commit_end)]
    fn commit_end_inductive(pre: Self, post: Self, to_deposit: Map::<nat, vstd::raw_ptr::PointsTo<u8>>) {
        assume(
            {
                &&& forall |i: nat| i >= post.base_addr && i < post.base_addr + post.length <==> post.storage.contains_key(i)
                &&& forall |i: nat| i >= post.base_addr && i < post.base_addr + post.length ==> post.storage.index(i).ptr().addr() == i
                &&& forall |i: nat| i >= post.base_addr && i < post.base_addr + post.length ==> post.storage.index(i).ptr()@.provenance == post.provenance
            }
        );
    }
}}

struct_with_invariants!{
    pub struct VBBuffer {
        buffer: *mut u8,
        length: usize,
        write: AtomicUsize<_, VBQueue::write, _>,
        read: AtomicUsize<_, VBQueue::read, _>,
        last: AtomicUsize<_, VBQueue::last, _>,
        reserve: AtomicUsize<_, VBQueue::reserve, _>,
        read_in_progress: AtomicBool<_, VBQueue::read_in_progress, _>,
        write_in_progress: AtomicBool<_, VBQueue::write_in_progress, _>, 
        already_split: AtomicBool<_, VBQueue::already_split, _>,

        instance: Tracked<VBQueue::Instance>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            &&& self.instance@.length() == self.length
            &&& self.instance@.base_addr() == self.buffer as nat
            &&& self.instance@.provenance() == self.buffer@.provenance
            &&& self.buffer.addr() + self.length <= usize::MAX + 1
            &&& self.buffer.addr() as int % 1 as int == 0
        }

        invariant on write with (instance) is (v: usize, g: VBQueue::write) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
            &&& g.value() <= instance@.length()
        }

        invariant on read with (instance) is (v: usize, g: VBQueue::read) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
            &&& g.value() <= instance@.length()
        }

        invariant on last with (instance) is (v: usize, g: VBQueue::last) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
            &&& g.value() <= instance@.length()
        }

        invariant on reserve with (instance) is (v: usize, g: VBQueue::reserve) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
            &&& g.value() <= instance@.length()
        }

        invariant on read_in_progress with (instance) is (v: bool, g: VBQueue::read_in_progress) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v
        }

        invariant on write_in_progress with (instance) is (v: bool, g: VBQueue::write_in_progress) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v
        }

        invariant on already_split with (instance) is (v: bool, g: VBQueue::already_split) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v
        }
    }
}

pub struct Producer {
    vbq: Arc<VBBuffer>,
}

impl Producer {
    pub closed spec fn wf(&self) -> bool {
        (*self.vbq).wf()
            //&& (self.tail as int) < (*self.queue).buffer@.len()
    }
}

pub struct Consumer {
    vbq: Arc<VBBuffer>,
}

/*
impl<T> Consumer<T> {
    pub closed spec fn wf(&self) -> bool {
        (*self.queue).wf()
            && self.consumer@.instance_id() === (*self.queue).instance@.id()
            && self.consumer@.value() === ConsumerState::Idle(self.head as nat)
            && (self.head as int) < (*self.queue).buffer@.len()
    }
}
 */
impl VBBuffer
{
    fn new(length: usize) -> (r:(Self, Tracked<VBQueue::producer>,Tracked<VBQueue::consumer>))
        requires
            valid_layout(length, 1),
            length > 0, // TODO: 元の BBQueue はこの制約は持っていない。0で使うことはないと思うが。
        ensures
        /*
            s.instance@.buffer_perm().is_range(s.buffer.addr() as int, length as int),
            s.instance@.buffer_dealloc()@
                == (DeallocData {
                    addr: s.buffer.addr(),
                    size: length as nat,
                    align: 1,
                    provenance: s.instance@.buffer_perm().provenance(),
                }),
            
        */
            r.0.wf(),
            r.0.instance@.id() == r.1@.instance_id(),
            r.1@.value() is Idle,
    {
        // TODO: 元の BBQueue は静的に確保している。
        let (buffer_ptr, Tracked(buffer_perm), Tracked(buffer_dealloc)) = allocate(length, 1);

        // allocate で得た buffer_perm (PointsToRaw) を u8 1バイトごとに分割して、addr => PointsTo の Map として格納する
        let tracked mut buffer_perm = buffer_perm;
        assert(buffer_perm.is_range(buffer_ptr as int, length as int));
        assert(buffer_ptr as int + length <= usize::MAX + 1);
        let tracked mut points_to_map = Map::<nat, vstd::raw_ptr::PointsTo<u8>>::tracked_empty();

        for len in 0..length
            invariant
                len <= length,
                buffer_ptr as int + length <= usize::MAX + 1,
                buffer_perm.is_range(buffer_ptr as int + len as int, length - len),
                forall |i: nat|
                    i >= buffer_ptr as nat && i < buffer_ptr as nat + len as nat
                        <==> points_to_map.contains_key(i),
                forall |i: nat|
                    i >= buffer_ptr as nat && i < buffer_ptr as nat + len as nat
                        ==> points_to_map.index(i as nat).ptr() as nat == i as nat,
                forall |i: nat|
                    i >= buffer_ptr as nat && i < buffer_ptr as nat + len as nat
                        ==> points_to_map.index(i as nat).ptr()@.provenance == buffer_perm.provenance(),
                buffer_ptr@.provenance == buffer_perm.provenance(),
            decreases
                length - len,
        {
            proof {
                let ghost range_base_addr = buffer_ptr as int + len as int;
                let ghost range_end_addr = range_base_addr + 1;
                
                let tracked (top, rest) = buffer_perm.split(crate::set_lib::set_int_range(range_base_addr, range_end_addr as int));
                assert(top.is_range(range_base_addr as usize as int, 1));

                let tracked top_pointsto = top.into_typed::<u8>(range_base_addr as usize);
                buffer_perm = rest;
                points_to_map.tracked_insert(range_base_addr as nat, top_pointsto);
                assert(points_to_map.contains_key(range_base_addr as nat));
                assert(points_to_map.index(range_base_addr as nat).ptr() as nat == range_base_addr as nat);
                assert(top_pointsto.ptr()@.provenance == top.provenance());
                assert(top.provenance() == buffer_perm.provenance());
            }
        }

        let tracked (
            Tracked(instance),
            Tracked(write_token),
            Tracked(read_token),
            Tracked(last_token),
            Tracked(reserve_token),
            Tracked(read_in_progress_token),
            Tracked(write_in_progress_token),
            Tracked(already_split_token),
            Tracked(producer_token),
            Tracked(consumer_token),
        ) = VBQueue::Instance::initialize(
            buffer_ptr as nat,
            buffer_ptr@.provenance,
            length as nat,
            points_to_map,
            buffer_dealloc,
            points_to_map,
            Some(buffer_dealloc));

        let tracked_inst: Tracked<VBQueue::Instance> = Tracked(instance.clone());
        let write_atomic = AtomicUsize::new(Ghost(tracked_inst), 0, Tracked(write_token));
        let read_atomic = AtomicUsize::new(Ghost(tracked_inst), 0, Tracked(read_token));
        let last_atomic = AtomicUsize::new(Ghost(tracked_inst), length, Tracked(last_token));
        let reserve_atomic = AtomicUsize::new(Ghost(tracked_inst), 0, Tracked(reserve_token));
        let read_in_progress_atomic = AtomicBool::new(Ghost(tracked_inst), false, Tracked(read_in_progress_token));
        let write_in_progress_atomic = AtomicBool::new(Ghost(tracked_inst), false, Tracked(write_in_progress_token));
        let already_split_atomic = AtomicBool::new(Ghost(tracked_inst), false, Tracked(already_split_token));

        // Initialize the queue
        (Self {
            buffer: buffer_ptr,
            length,
            write: write_atomic,
            read: read_atomic,
            last: last_atomic,
            reserve: reserve_atomic,
            read_in_progress: read_in_progress_atomic,
            write_in_progress: write_in_progress_atomic,
            already_split: already_split_atomic,
            instance: Tracked(instance),
        }, Tracked(producer_token), Tracked(consumer_token))
    }

    fn try_split(self, Tracked(producer_token): Tracked<&mut VBQueue::producer>, Tracked(consumer_token): Tracked<VBQueue::consumer>) -> (res: Result<(Producer, Consumer),  &'static str>)
        requires
            self.wf(),
            old(producer_token).instance_id() == self.instance@.id(),
            old(producer_token).value() is Idle,
        ensures
            self.wf(),
            match res {
                Ok((prod, cons)) => {
                    prod.wf() &&/* //cons.wf(), */
                    producer_token.instance_id() == prod.vbq.instance@.id()
                }, 
                Err(_) => true
            },
            producer_token.instance_id() == self.instance@.id(),
            producer_token.value() is Idle,
    {
        let already_splitted =
            atomic_with_ghost!(&self.already_split => swap(true);
                update prev -> next;
                returning ret;
                ghost already_split_token => {
                    if !ret {
                        assert(prev == false);
                        assert(next == true);
                        assert(already_split_token.value() == false);
                        let _ = self.instance.borrow().try_split(&mut already_split_token);
                        assert(already_split_token.value() == true);
                    };
                }
        );

        if already_splitted {
            return Err("already splitted");
        }

        // FIXME:元の実装は Arc は使っていない。
        // また、buffer のゼロ化もしているが、こちらは今はやっていない。
        let vbbuffer_arc = Arc::new(self);
        Ok((
            Producer {
                vbq: vbbuffer_arc.clone(),
            },
            Consumer {
                vbq: vbbuffer_arc.clone(),
            }
        ))
    }
}

struct GrantW {
    buf: Vec<*mut u8>,
    vbq: Arc<VBBuffer>,
    to_commit: usize,
}

impl GrantW {
    pub closed spec fn wf_with_buf_perms(&self, buf_perms: Map<nat, raw_ptr::PointsTo<u8>>) -> bool {
        &&& self.buf.len() == buf_perms.len()
        &&& forall |i: int| 0 <= i && i < self.buf.len() ==> self.buf[i] == buf_perms.index(self.buf[i] as nat).ptr()
        &&& forall |i: int| 0 <= i && i < self.buf.len() ==> self.buf[i]@.provenance == buf_perms.index(self.buf[i] as nat).ptr()@.provenance
    }

    pub closed spec fn wf_with_producer(&self, producer_token: ProducerState, buf_perms: Map<nat, raw_ptr::PointsTo<u8>>) -> bool {
        match producer_token {
            ProducerState::Reserved((wip, reserve_start, reserve_end)) |
            ProducerState::CommitWriteLoaded((wip, reserve_start, reserve_end, _)) |
            ProducerState::CommitReserveSubbed((wip, reserve_start, reserve_end, _)) |
            ProducerState::CommitLastLoaded((wip, reserve_start, reserve_end, _, _)) |
            ProducerState::CommitReserveLoaded((wip, reserve_start, reserve_end, _, _, _)) => {
                &&& wip == true
                &&& self.buf.len() == reserve_end - reserve_start
                &&& forall |i: int| 0 <= i && i < self.buf.len() ==> buf_perms.index(self.buf[i] as nat).ptr().addr() == self.vbq.instance@.base_addr() as nat + reserve_start + i as nat
            },
            ProducerState::Idle(_) => true,
            _ => false,
        }
    }

    fn commit(&mut self,
        used: usize,
        Tracked(producer_token): Tracked<&mut VBQueue::producer>, 
        Tracked(buf_perms): Tracked<Map<nat, raw_ptr::PointsTo<u8>>>
    )
        requires
            old(self).wf_with_buf_perms(buf_perms),
            old(self).vbq.wf(),
            old(producer_token).instance_id() == old(self).vbq.instance@.id(),
            old(producer_token).value() is Idle || old(producer_token).value() is Reserved,
            old(self).wf_with_producer(old(producer_token).value(), buf_perms)
        ensures
            producer_token.value() is Idle,
            self.vbq.wf(),
    {
        self.commit_inner(used, Tracked(producer_token), Tracked(buf_perms));
        // forget(self); // FIXME
    }

    pub(crate) fn commit_inner(&mut self,
        used: usize,
        Tracked(producer_token): Tracked<&mut VBQueue::producer>, 
        Tracked(buf_perms): Tracked<Map<nat, raw_ptr::PointsTo<u8>>>
    )
        requires
            old(self).wf_with_buf_perms(buf_perms),
            old(self).vbq.wf(),
            old(producer_token).instance_id() == old(self).vbq.instance@.id(),
            old(producer_token).value() is Idle || old(producer_token).value() is Reserved,
            old(self).wf_with_producer(old(producer_token).value(), buf_perms)
        ensures
            producer_token.value() is Idle,
            self.vbq.wf(),
    {
        // If there is no grant in progress, return early. This
        // generally means we are dropping the grant within a
        // wrapper structure

        let is_write_in_progress =
            atomic_with_ghost!(&self.vbq.write_in_progress => load();
                update prev -> next;
                returning ret;
                ghost write_in_progress_token => {
                    assert(producer_token.value() is Idle || producer_token.value() is Reserved);
                    assert(!(producer_token.value() is Idle) ==> producer_token.value() is Reserved);
                    let _ = self.vbq.instance.borrow().commit_start(&write_in_progress_token, producer_token);
                }
        );

        if !is_write_in_progress {
            assert(producer_token.value() is Idle);
            return;
        }

        // Writer component. Must never write to READ,
        // be careful writing to LAST

        // Saturate the grant commit
        let len = self.buf.len();
        let used = if len <= used { len } else { used }; // min の代用。

        proof {
            assert(used <= len);
            assert(producer_token.value() is Reserved);
        }

        let write = atomic_with_ghost!(&self.vbq.write => load();
            ghost write_token => {
                let _ = self.vbq.instance.borrow().commit_load_write(&write_token, producer_token);
                assert(producer_token.value()->CommitWriteLoaded_0.2 - producer_token.value()->CommitWriteLoaded_0.1 == len);
                assert(producer_token.value()->CommitWriteLoaded_0.2 >= producer_token.value()->CommitWriteLoaded_0.1);
                assert(producer_token.value()->CommitWriteLoaded_0.2 >= len);
            }
        );

        proof {
            assert(producer_token.value() is CommitWriteLoaded);
            assert(self.wf_with_producer(producer_token.value(), buf_perms));
        }

        atomic_with_ghost!(&self.vbq.reserve => fetch_sub(len - used);
            update prev -> next;
            returning ret;
            ghost reserve_token => {
                let _ = self.vbq.instance.borrow().commit_sub_reserve((len - used) as nat, &mut reserve_token, producer_token);
            }
        );

        let max = self.vbq.length as usize;
        let last = atomic_with_ghost!(&self.vbq.last => load();
            ghost last_token => {
                let _ = self.vbq.instance.borrow().commit_load_last(&last_token, producer_token);
            }
        );
        
        let new_write = atomic_with_ghost!(&self.vbq.reserve => load();
            ghost reserve_token => {
                let _ = self.vbq.instance.borrow().commit_load_reserve(&reserve_token, producer_token);
            }
        );

        if (new_write < write) && (write != max) {
            // We have already wrapped, but we are skipping some bytes at the end of the ring.
            // Mark `last` where the write pointer used to be to hold the line here
            atomic_with_ghost!(&self.vbq.last => store(write);
                ghost last_token => {
                    let _ = self.vbq.instance.borrow().commit_store_last(write as nat, &mut last_token, producer_token);
                }
            );
        } else if new_write > last {
            // We're about to pass the last pointer, which was previously the artificial
            // end of the ring. Now that we've passed it, we can "unlock" the section
            // that was previously skipped.
            //
            // Since new_write is strictly larger than last, it is safe to move this as
            // the other thread will still be halted by the (about to be updated) write
            // value
            atomic_with_ghost!(&self.vbq.last => store(max);
                ghost last_token => {
                    let _ = self.vbq.instance.borrow().commit_store_last(max as nat, &mut last_token, producer_token);
                }
            );
        }
        // else: If new_write == last, either:
        // * last == max, so no need to write, OR
        // * If we write in the end chunk again, we'll update last to max next time
        // * If we write to the start chunk in a wrap, we'll update last when we
        //     move write backwards

        // Write must be updated AFTER last, otherwise read could think it was
        // time to invert early!
        atomic_with_ghost!(&self.vbq.write => store(new_write);
            ghost write_token => {
                let _ = self.vbq.instance.borrow().commit_store_write(new_write as nat, &mut write_token, producer_token);
            }
        );

        let tracked mut granted_perms_map = Map::<nat, vstd::raw_ptr::PointsTo<u8>>::tracked_empty();
        for l in 0..len
            invariant
                0 <= l,
                l <= len,
                buf_perms.len() == len,// - l,
                buf_perms.len() == self.buf.len(),
                forall |i: int| 0 <= i && i < self.buf.len() ==> self.buf[i] == buf_perms.index(self.buf[i] as nat).ptr(),
                forall |i: int| 0 <= i && i < self.buf.len() ==> buf_perms.index(self.buf[i] as nat).ptr().addr() == self.vbq.instance@.base_addr() as nat + producer_token.value()->CommitReserveLoaded_0.1 + i as nat,
                /*forall |i: nat|
                    i >= self.vbq.instance@.base_addr() as nat + producer_token.value()->CommitReserveLoaded_0.1 && i < self.vbq.instance@.base_addr() as nat + producer_token.value()->CommitReserveLoaded_0.1 + l as nat
                        <==> granted_perms_map.contains_key(i),
                forall |i: nat|
                    i >= self.vbq.instance@.base_addr() as nat && i < self.vbq.instance@.base_addr() as nat + l as nat
                        ==> granted_perms_map.index(i as nat).ptr() as nat == i as nat,
                forall |i: nat|
                    i >= self.vbq.instance@.base_addr() as nat && i < self.vbq.instance@.base_addr() as nat + l as nat
                        ==> granted_perms_map.index(i as nat).ptr()@.provenance == self.vbq.instance@.provenance(), */
                self.vbq.wf(),
                producer_token.instance_id() == self.vbq.instance@.id(),
                //producer_token.value() is Idle,
            decreases
                len - l,
        {
            proof {
                //let points_to = self.buf_perms.borrow_mut().tracked_remove(0);
                assert(buf_perms.index(self.buf[l as int] as nat).ptr().addr() == self.vbq.instance@.base_addr() as nat + producer_token.value()->CommitReserveLoaded_0.1 as nat + l as nat);
                //assert(points_to.ptr().addr() as nat == self.vbq.instance@.base_addr() as nat + producer_token.value()->CommitReserveLoaded_0.1 as nat + l as nat);
                //assert(points_to.ptr().addr() as nat == points_to.ptr() as nat);
                //granted_perms_map.insert(points_to.ptr().addr() as nat, points_to);
            }
        }
/*
        for l in 0..len
            invariant
                l <= len,
                self.buf_perms@.len() == len,// - l,
                forall |i: int| 0 <= i && i < self.buf.len() ==> self.buf[i] == self.buf_perms@[i].ptr(),
                /*forall |i: nat|
                    i >= self.vbq.instance@.base_addr() as nat + producer_token.value()->CommitReserveLoaded_0.1 && i < self.vbq.instance@.base_addr() as nat + producer_token.value()->CommitReserveLoaded_0.1 + l as nat
                        <==> granted_perms_map.contains_key(i),
                forall |i: nat|
                    i >= self.vbq.instance@.base_addr() as nat && i < self.vbq.instance@.base_addr() as nat + l as nat
                        ==> granted_perms_map.index(i as nat).ptr() as nat == i as nat,
                forall |i: nat|
                    i >= self.vbq.instance@.base_addr() as nat && i < self.vbq.instance@.base_addr() as nat + l as nat
                        ==> granted_perms_map.index(i as nat).ptr()@.provenance == self.vbq.instance@.provenance(), */
                self.vbq.wf(),
                producer_token.instance_id() == self.vbq.instance@.id(),
                //producer_token.value() is Idle,
            decreases
                len - l,
        {
            proof {
                //let points_to = self.buf_perms.borrow_mut().tracked_remove(0);
                assert(self.buf[l as int].ptr().addr() == self.vbq.instance@.base_addr() as nat + producer_token.value()->CommitReserveLoaded_0.1 as nat + l as nat);
                //assert(points_to.ptr().addr() as nat == self.vbq.instance@.base_addr() as nat + producer_token.value()->CommitReserveLoaded_0.1 as nat + l as nat);
                //assert(points_to.ptr().addr() as nat == points_to.ptr() as nat);
                //granted_perms_map.insert(points_to.ptr().addr() as nat, points_to);
            }
        } */

        // Allow subsequent grants
        atomic_with_ghost!(&self.vbq.write_in_progress => store(false);
            ghost write_in_progress_token => {
                let _ = self.vbq.instance.borrow().commit_end(buf_perms, buf_perms, &mut write_in_progress_token, producer_token);
                assert(write_in_progress_token.value() == false);
            }
        );
    }

    /// Configures the amount of bytes to be commited on drop.
    pub fn to_commit(&mut self, amt: usize) {
        self.to_commit = self.buf.len().min(amt);
    }
}

impl Producer {
    fn grant_exact(&mut self, sz: usize, Tracked(producer_token): Tracked<&mut VBQueue::producer>) -> (r: Result<(GrantW, Tracked<Map<nat, PointsTo<u8>>>), &'static str>)
        requires
            old(self).wf(),
            old(producer_token).instance_id() == old(self).vbq.instance@.id(),
            old(producer_token).value() is Idle,
        ensures
            match r {
                Ok((wgr, buf_perms)) => {
                    wgr.wf_with_buf_perms(buf_perms@) &&
                    wgr.buf.len() == sz &&
                    producer_token.value() is Reserved
                },
                _ => true
            },
    {
        let is_write_in_progress =
            atomic_with_ghost!(&self.vbq.write_in_progress => swap(true);
                update prev -> next;
                returning ret;
                ghost write_in_progress_token => {
                    if !ret {
                        assert(prev == false);
                        assert(next == true);
                        assert(write_in_progress_token.value() == false);
                        let _ = self.vbq.instance.borrow().grant_start(&mut write_in_progress_token, producer_token);
                        assert(write_in_progress_token.value() == true);
                        assert(producer_token.value() is GrantStarted);
                        assert(ret == false);
                    } else {
                        assert(write_in_progress_token.value() == true);
                        assert(producer_token.value() is Idle);
                        assert(ret == true);
                    };
                }
        );

        if is_write_in_progress {
            proof {
                assert(producer_token.value() is Idle);
            }
            return Err("write in progress");
        }

        proof {
            assert(producer_token.value() is GrantStarted);
        }
        let write = atomic_with_ghost!(&self.vbq.write => load();
            ghost write_token => {
                let _ = self.vbq.instance.borrow().grant_load_write(&write_token, producer_token);
            }
        );

        let read = atomic_with_ghost!(&self.vbq.read => load();
            ghost read_token => {
                let _ = self.vbq.instance.borrow().grant_load_read(&read_token, producer_token);
            }
        );
        let max = self.vbq.length as usize;
        let already_inverted = write < read;

        let start: usize = if already_inverted {
            if ((write as u128 + sz as u128) as u128) < read as u128 {
                // Inverted, room is still available
                write
            } else {
                // Inverted, no room is available
                atomic_with_ghost!(&self.vbq.write_in_progress => store(false);
                    ghost write_in_progress_token => {
                        let _ = self.vbq.instance.borrow().grant_fail(&mut write_in_progress_token, producer_token);
                        assert(write_in_progress_token.value() == false);
                    }
                );
                return Err("Inverted, no room is available");
            }
        } else {
            if ((write as u128 + sz as u128) as u128) <= max as u128 {
                // Non inverted condition
                write
            } else {
                // Not inverted, but need to go inverted

                // NOTE: We check sz < read, NOT <=, because
                // write must never == read in an inverted condition, since
                // we will then not be able to tell if we are inverted or not
                if sz < read {
                    // Invertible situation
                    0
                } else {
                    // Not invertible, no space
                    atomic_with_ghost!(&self.vbq.write_in_progress => store(false);
                        ghost write_in_progress_token => {
                            let _ = self.vbq.instance.borrow().grant_fail(&mut write_in_progress_token, producer_token);
                            assert(write_in_progress_token.value() == false);
                        }
                    );
                    return Err("Insufficient size");
                }
            }
        };
        // 上記のエラーケース以外の条件を集約
        assert(start + sz < read || start + sz <= max || (start == 0 && sz < read));
        assert(start + sz <= max);
        assert(start + sz <= self.vbq.length);

        // Safe write, only viewed by this task

        let tracked mut granted_perms_map;
        atomic_with_ghost!(&self.vbq.reserve => store(start + sz);
            ghost reserve_token => {
                // (Ghost<Map<nat, PointsTo<u8>>>, Tracked<Map<nat, PointsTo<u8>>>) が返る
                let tracked ret = self.vbq.instance.borrow().do_reserve(start as nat, sz as nat, &mut reserve_token, producer_token);
                granted_perms_map = ret.1.get();
                assert(self.vbq.buffer as nat == self.vbq.instance@.base_addr());
                assert(
                    forall |j: nat| j >= self.vbq.buffer as nat + start as nat && j < self.vbq.buffer as nat + start as nat + sz as nat 
                        <==> granted_perms_map.contains_key(j));
                assert(
                    forall |j: nat|
                        j >= self.vbq.buffer as nat + start as nat && j < self.vbq.buffer as nat + start as nat + sz as nat
                            ==> (
                                granted_perms_map.index(j).ptr().addr() == j
                            )
                );
                assert(
                    forall |j: nat|
                        j >= self.vbq.buffer as nat + start as nat && j < self.vbq.buffer as nat + start as nat + sz as nat
                            ==> (
                                granted_perms_map.index(j).ptr()@.provenance == self.vbq.instance@.provenance()
                            )
                );
                assert(reserve_token.value() == start + sz);
                assume(granted_perms_map.len() == sz);
            }
        );


        let mut granted_buf: Vec<*mut u8> = Vec::new();
        let base_ptr = self.vbq.buffer;
        let end_offset = start + sz;

        proof {
            assert(base_ptr@.provenance == self.vbq.instance@.provenance());
            assert(base_ptr as nat == self.vbq.instance@.base_addr());
            assert(
                forall |j: nat|
                    j >= base_ptr as nat + start as nat && j < base_ptr as nat + start as nat + sz as nat
                        ==> (
                            granted_perms_map.contains_key(j)
                            //&& granted_perms_map.index(j as nat).ptr().addr() == j
                            //&& granted_perms_map.index(j as nat).ptr()@.provenance == self.vbq.instance@.provenance()
                        )
            );
            assert(granted_buf.len() == 0);
        }

        for idx in start..end_offset
            invariant
                granted_buf.len() == idx - start,
                idx <= end_offset,
                base_ptr as usize + end_offset <= usize::MAX + 1,
                base_ptr@.provenance == self.vbq.instance@.provenance(),
                forall |j: nat|
                    j >= base_ptr as nat + idx as nat && j < base_ptr as nat + end_offset as nat
                        ==> (
                            granted_perms_map.contains_key(j)
                            //&& granted_perms_map.index(j as nat).ptr().addr() as nat == j as nat
                            //&& granted_perms_map.index(j as nat).ptr()@.provenance == base_ptr@.provenance
                        ),
                forall |j: nat|
                    j >= base_ptr as nat + idx as nat && j < base_ptr as nat + end_offset as nat
                        ==> (
                            granted_perms_map.index(j as nat).ptr().addr() as nat == j as nat
                            //&& granted_perms_map.index(j as nat).ptr()@.provenance == base_ptr@.provenance
                        ),
                forall |j: nat|
                    j >= base_ptr as nat + idx as nat && j < base_ptr as nat + end_offset as nat
                        ==> (
                            granted_perms_map.index(j).ptr()@.provenance == base_ptr@.provenance
                        ),
                granted_buf.len() == (idx - start),
                forall |j: int|
                    0 <= j && j < (idx - start) as int
                        ==> (
                            equal(granted_buf[j], granted_perms_map.index(granted_buf[j] as nat).ptr())
                        ),
            decreases
                end_offset - idx,
        {
            let addr = base_ptr as usize + idx; // * size_of::<u8>();
            let ptr: *mut u8 = with_exposed_provenance(addr, expose_provenance(base_ptr));
            
            granted_buf.push(ptr);
            assert(granted_perms_map.contains_key(addr as nat));
            assert(ptr@.provenance == base_ptr@.provenance);
            assert(granted_perms_map.index(addr as nat).ptr()@.provenance == base_ptr@.provenance);
            assert(granted_perms_map.index(addr as nat).ptr()@.provenance == self.vbq.instance@.provenance());
            assert(equal(granted_perms_map.index(addr as nat).ptr(), ptr));
        }

        Ok (
            (
                GrantW {
                    buf: granted_buf,
                    vbq: self.vbq.clone(),
                    to_commit: sz,
                }, Tracked(granted_perms_map)
            )
        )
    }
}

fn main() {
    let (vbuf, Tracked(producer_token), Tracked(consumer_token)) = VBBuffer::new(6);
    let (mut prod, mut cons) = match vbuf.try_split(Tracked(&mut producer_token), Tracked(consumer_token)) {
        Ok((prod, cons)) => (prod, cons),
        Err(_) => {
            return;
        }
    };

    proof {
        assert(producer_token.instance_id() == prod.vbq.instance@.id());
    }

    // Request space for one byte
    match prod.grant_exact(2, Tracked(&mut producer_token)) {
        Ok((wgr, buf_perms)) => {
            let tracked buf_perms = buf_perms.get();
            let tracked points_to = buf_perms.tracked_remove(wgr.buf[0] as nat);
            
            ptr_mut_write(wgr.buf[0], Tracked(&mut points_to), 5);
            let val = ptr_ref(wgr.buf[0], Tracked(&points_to));
            assert(val == 5);
        },
        _ => {}
    }
}

}