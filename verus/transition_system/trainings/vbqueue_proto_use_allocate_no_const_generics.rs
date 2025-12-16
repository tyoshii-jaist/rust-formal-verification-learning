use state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
use vstd::raw_ptr::*;
use vstd::{prelude::*, *};
use vstd::layout::*;
use std::sync::Arc;

verus! {
global layout u8 is size == 1, align == 1;

spec fn range_set(base: nat, sz: nat) -> Set<nat> {
    Set::new(|i: nat| base <= i && i < base + sz)
}

// base から sz 分の集合の len が sz であることを示す補題
proof fn lemma_range_set_len(base: nat, sz: nat)
    ensures
        Set::new(|i: nat| base <= i && i < base + sz).len() == sz,
        Set::new(|i: nat| base <= i && i < base + sz).finite(),
    decreases sz
{
    let s_target = Set::new(|i: nat| base <= i && i < base + sz);

    if sz == 0 {
        assert(s_target =~= Set::empty()); 
    } else {
        lemma_range_set_len(base, (sz - 1) as nat);
        
        let s_prev = Set::new(|i: nat| base <= i && i < base + (sz - 1));
        // nat 同士の計算なので、sz >= 1 なら (base + sz - 1) は安全
        let last_elem = (base + sz - 1) as nat;

        assert(s_target =~= s_prev.insert(last_elem));
        assert(!s_prev.contains(last_elem));
    }
}

pub enum ProducerStep {
    Idle,
    GrantStarted,
    GrantWriteLoaded,
    GrantWriteAndReadLoaded,
    Reserved,
    CommitWriteLoaded,
    CommitReserveSubbed,
    CommitLastLoaded,
    CommitReserveLoaded,
    CommitWriteStored,
}

pub struct ProducerState {
    pub step: ProducerStep,
    pub write_in_progress: bool,
    pub write: Option<nat>,
    pub reserve: Option<nat>,
    pub last: Option<nat>,
    pub read_obs: Option<nat>,
}

pub enum ConsumerStep {
    Idle,
}

pub struct ConsumerState {
    pub step: ConsumerStep,
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

    #[invariant]
    pub fn no_write_in_progress(&self) -> bool {
        !self.write_in_progress <==> self.producer.step is Idle
    }

    #[invariant]
    pub fn valid_storage_all(&self) -> bool {
        let grant_start = if self.write < self.reserve {self.write} else {0};
        let grant_end = self.reserve;

        &&& grant_start as nat <= self.length
        &&& grant_end as nat <= self.length
        &&& forall |i: nat|
            ((i >= self.base_addr && i < self.base_addr + grant_start as nat) || 
            (i >= self.base_addr + grant_end && i < self.base_addr + self.length))
                <==> (
                    self.storage.contains_key(i)
                )
        &&& forall |i: nat|
            (i >= self.base_addr + grant_start as nat && i < self.base_addr + grant_end)
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
    }

    #[invariant]
    pub fn valid_producer_local_state(&self) -> bool {
        &&& self.producer.step is Idle <==> (self.producer.write_in_progress == false)
        &&& self.producer.write_in_progress == self.write_in_progress
        &&& match self.producer.write {Some(w) => w == self.write, None => true}
        &&& match self.producer.reserve {Some(res) => res == self.reserve, None => true}
        &&& match self.producer.last {Some(l) => l == self.last, None => true}
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

            init producer = ProducerState {
                step: ProducerStep::Idle,
                write_in_progress: false,
                write: None,
                reserve: None,
                last: None,
                read_obs: None,
            };
            init consumer = ConsumerState {
                step: ConsumerStep::Idle,
            };
        }
    }

    
    #[inductive(initialize)]
    fn initialize_inductive(post: Self, base_addr: nat, provenance: raw_ptr::Provenance, length: nat, storage: Map<nat, raw_ptr::PointsTo<u8>>, buffer_dealloc: raw_ptr::Dealloc) {
        assert(post.producer.step is Idle);
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
            require(pre.producer.step is Idle);
            require(pre.write_in_progress == false);

            update write_in_progress = true;
            update producer = ProducerState {
                step: ProducerStep::GrantStarted,
                write_in_progress: true,
                write: pre.producer.write,
                reserve: pre.producer.reserve,
                last: pre.producer.last,
                read_obs: pre.producer.read_obs,
            };
        }
    }

    transition!{
        grant_load_write() {
            require(pre.producer.step is GrantStarted);

            update producer = ProducerState{
                step: ProducerStep::GrantWriteLoaded,
                write: Some(pre.write),
                write_in_progress: pre.producer.write_in_progress,
                reserve: pre.producer.reserve,
                last: pre.producer.last,
                read_obs: pre.producer.read_obs,
            };
        }
    }

    transition!{
        grant_load_read() {
            require(pre.producer.step is GrantWriteLoaded);

            update producer = ProducerState{
                step: ProducerStep::GrantWriteAndReadLoaded,
                read_obs: Some(pre.read),
                write_in_progress: pre.producer.write_in_progress,
                write: pre.producer.write,
                reserve: pre.producer.reserve,
                last: pre.producer.last,
            };
        }
    }

    transition!{
        do_reserve(reserve: nat) {
            require(reserve <= pre.length);
            require(pre.producer.step is GrantWriteAndReadLoaded);

            update reserve = reserve;

            let start = pre.producer.write->Some_0;
            birds_eye let range_keys = Set::new(|i: nat| pre.base_addr + start <= i && i < pre.base_addr + reserve);
            // restrict を使わないとうまく pre.storage の情報が引き継がれない?
            birds_eye let withdraw_range_map = pre.storage.restrict(range_keys);

            withdraw storage -= (withdraw_range_map) by {
                assert(withdraw_range_map.submap_of(pre.storage)) by {
                    assert(withdraw_range_map.dom().subset_of(Set::new(|i: nat| i >= start + pre.base_addr && i < reserve + pre.base_addr)));
                    assert(pre.valid_storage_all());
                    assert(forall |j: nat| j >= pre.base_addr + start && j < pre.base_addr as nat + reserve ==> pre.storage.contains_key(j));
                    assert(forall |j: nat| j >= pre.base_addr + start && j < pre.base_addr as nat + reserve ==> pre.storage.index(j).ptr().addr() == j);
                    assert(forall |j: nat| j >= pre.base_addr + start && j < pre.base_addr as nat + reserve ==> pre.storage.index(j).ptr()@.provenance == pre.provenance);
                }
            };
            
            update producer = ProducerState{
                step: ProducerStep::Reserved,
                write: None,
                last: None,
                reserve: None,
                read_obs: None,
                write_in_progress: pre.producer.write_in_progress,
            };

            assert(
                withdraw_range_map.dom().subset_of(Set::new(|i: nat| i >= start + pre.base_addr && i < reserve + pre.base_addr))
            );
            assert(
                Set::new(|i: nat| i >= start + pre.base_addr && i < reserve + pre.base_addr).subset_of(withdraw_range_map.dom())
            );
            assert(forall |j: nat| j >= pre.base_addr + start && j < pre.base_addr as nat + reserve <==> withdraw_range_map.contains_key(j));
            assert(forall |j: nat| j >= pre.base_addr + start && j < pre.base_addr as nat + reserve ==> withdraw_range_map.index(j).ptr().addr() == j);
            assert(forall |j: nat| j >= pre.base_addr + start && j < pre.base_addr as nat + reserve ==> withdraw_range_map.index(j).ptr()@.provenance == pre.provenance);
        }
    }

    transition!{
        grant_fail() {
            require(pre.producer.step is GrantWriteAndReadLoaded);

            update write_in_progress = false;

            update producer = ProducerState{
                step: ProducerStep::Idle,
                write_in_progress: false,
                write: None,
                last: None,
                reserve: None,
                read_obs: None,
            };
        }
    }

    transition!{
        commit_start() {
            require(pre.producer.step is Idle || pre.producer.step is Reserved);
            //assert(!pre.write_in_progress ==> pre.producer.step is Idle && pre.producer.step is Idle ==> !pre.write_in_progress);
            if !pre.write_in_progress {
                assert(pre.producer.step is Idle);
            } else {
                assert(pre.producer.step is Reserved);
            }
        }
    }

    transition!{
        commit_load_write() {
            require(pre.producer.step is Reserved);

            update producer = ProducerState{
                step: ProducerStep::CommitWriteLoaded,
                write: Some(pre.write),
                write_in_progress: pre.producer.write_in_progress,
                reserve: pre.producer.reserve,
                last: pre.producer.last,
                read_obs: pre.producer.read_obs,
            };
        }
    }

    transition!{
        commit_sub_reserve(commited: nat) {
            require(pre.producer.step is CommitWriteLoaded);
            //assert(pre.reserve == pre.producer->CommitWriteLoaded_0.2); // 重要!
            require(pre.reserve >= commited);

            let new_reserve = (pre.reserve - commited) as nat;

            update reserve = new_reserve;
            
            // TODO: need deposit subbed area.
            update producer = ProducerState{
                step: ProducerStep::CommitReserveSubbed,
                reserve: Some(new_reserve),
                write_in_progress: pre.producer.write_in_progress,
                write: pre.producer.write,
                last: pre.producer.last,
                read_obs: pre.producer.read_obs,
            };
        }
    }    

    transition!{
        commit_load_last() {
            require(pre.producer.step is CommitReserveSubbed);

            update producer = ProducerState{
                step: ProducerStep::CommitLastLoaded,
                last: Some(pre.last),
                write_in_progress: pre.producer.write_in_progress,
                write: pre.producer.write,
                reserve: pre.producer.reserve,
                read_obs: pre.producer.read_obs,
            };
        }
    }

    transition!{
        commit_load_reserve() {
            require(pre.producer.step is CommitLastLoaded);

            update producer = ProducerState{
                step: ProducerStep::CommitReserveLoaded,
                //reserve: Some(pre.reserve),
                write_in_progress: pre.producer.write_in_progress,
                write: pre.producer.write,
                reserve: Some(pre.reserve),
                last: pre.producer.last,
                read_obs: pre.producer.read_obs,
            };
        }
    }

    transition!{
        commit_store_last(new_last: nat) {
            require(pre.producer.step is CommitReserveLoaded);

            update last = new_last;

            update producer = ProducerState{
                step: ProducerStep::CommitReserveLoaded,
                last: Some(new_last),
                write_in_progress: pre.producer.write_in_progress,
                write: pre.producer.write,
                reserve: pre.producer.reserve,
                read_obs: pre.producer.read_obs,
            };
        }
    }

    transition!{
        commit_store_write(new_write: nat, to_deposit: Map::<nat, vstd::raw_ptr::PointsTo<u8>>) {
            require(pre.producer.step is CommitReserveLoaded);
            let write = pre.producer.write->Some_0;
            let reserve = pre.producer.reserve->Some_0;
        
            let grant_start = if write < reserve {write} else {0};
            let grant_end = reserve;

            require(
                forall |j: nat| j >= pre.base_addr + grant_start && j < pre.base_addr + grant_end
                    <==> to_deposit.contains_key(j));
            require(
                forall |j: nat| j >= pre.base_addr + grant_start && j < pre.base_addr + grant_end
                     ==> to_deposit.index(j).ptr().addr() == j
            );
            require(
                forall |j: nat| j >= pre.base_addr + grant_start && j < pre.base_addr + grant_end
                    ==> to_deposit.index(j).ptr()@.provenance == pre.provenance
            );
            deposit storage += (to_deposit) by {
                assert(pre.valid_storage_all());
                assert(forall |i: nat| to_deposit.contains_key(i) ==> !pre.storage.contains_key(i));
            };

            update write = new_write;

            update producer = ProducerState{
                step: ProducerStep::CommitWriteStored,
                write: None,
                reserve: None,
                read_obs: None,
                last: None,
                write_in_progress: pre.producer.write_in_progress,
            };
        }
    }

    transition!{
        commit_end() {
            require(pre.producer.step is CommitWriteStored);

            update write_in_progress = false;
            update producer = ProducerState{
                step: ProducerStep::Idle,
                write_in_progress: false,
                write: pre.producer.write,
                reserve: pre.producer.reserve,
                last: pre.producer.last,
                read_obs: pre.producer.read_obs,
            };
        }
    }

    #[inductive(try_split)]
    fn try_split_inductive(pre: Self, post: Self) { }

    #[inductive(grant_start)]
    fn grant_start_inductive(pre: Self, post: Self) { }

    #[inductive(grant_load_write)]
    fn grant_load_write_inductive(pre: Self, post: Self) {
    }

    #[inductive(grant_load_read)]
    fn grant_load_read_inductive(pre: Self, post: Self) {
    }

    #[inductive(grant_fail)]
    fn grant_fail_inductive(pre: Self, post: Self) { }

    #[inductive(do_reserve)]
    fn do_reserve_inductive(pre: Self, post: Self, reserve: nat) {
    }

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self) {
    }

    #[inductive(commit_load_write)]
    fn commit_load_write_inductive(pre: Self, post: Self) {
    }

    #[inductive(commit_sub_reserve)]
    fn commit_sub_reserve_inductive(pre: Self, post: Self, commited: nat) {
    }

    #[inductive(commit_load_last)]
    fn commit_load_last_inductive(pre: Self, post: Self) { }

    #[inductive(commit_load_reserve)]
    fn commit_load_reserve_inductive(pre: Self, post: Self) { }

    #[inductive(commit_store_last)]
    fn commit_store_last_inductive(pre: Self, post: Self, new_last: nat) { }

    #[inductive(commit_store_write)]
    fn commit_store_write_inductive(pre: Self, post: Self, new_write: nat, to_deposit: Map::<nat, vstd::raw_ptr::PointsTo<u8>>) {
        assert(forall |i: nat| i >= post.base_addr && i < post.base_addr + post.length ==> post.storage.contains_key(i));

        let write = pre.producer.write->Some_0;
        let reserve = pre.producer.reserve->Some_0;

        let start = post.base_addr;
        let end = post.base_addr + post.length;
        let dep_start = pre.base_addr + write;
        let dep_end = pre.base_addr + reserve;

        // post.storage のキーはすべて範囲内であることを示す
        assert(forall |i: nat| post.storage.contains_key(i) ==> start <= i && i < end) 
        by {
            // ヒント1: 今回追加した分 (to_deposit) は範囲内である
            assert(forall |i: nat| to_deposit.contains_key(i) ==> start <= i && i < end) by {
                assert(start <= dep_start && dep_end <= end); 
            };

            // ヒント2: 元々あった分 (pre.storage) も範囲内であることを教える
            assert(forall |i: nat| pre.storage.contains_key(i) ==> start <= i && i < end) by {
                assert(pre.valid_storage_all());
            };

            // 「post は to_deposit と pre の和集合」であることを知っているため、
            // 上記2つのヒントがあれば、自動的に全体の証明が完了する
        };
        assert(forall |i: nat| i >= post.base_addr && i < post.base_addr + post.length ==> post.storage.index(i).ptr().addr() == i);
        assert(forall |i: nat| i >= post.base_addr && i < post.base_addr + post.length ==> post.storage.index(i).ptr()@.provenance == post.provenance);
    }

    #[inductive(commit_end)]
    fn commit_end_inductive(pre: Self, post: Self) {
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
    fn new(length: usize) -> (r:(Self, Tracked<VBQueue::producer>, Tracked<VBQueue::consumer>))
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
            r.1@.value().step is Idle,
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
            old(producer_token).value().step is Idle,
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
            old(producer_token).value().step is Idle,
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

impl Producer {
    fn grant_exact(&mut self, sz: usize, Tracked(producer_token): Tracked<&mut VBQueue::producer>) -> (r: Result<(GrantW, Tracked<Map<nat, PointsTo<u8>>>), &'static str>)
        requires
            old(self).wf(),
            old(producer_token).instance_id() == old(self).vbq.instance@.id(),
            old(producer_token).value().step is Idle,
        ensures
            match r {
                Ok((wgr, buf_perms)) => {
                    wgr.wf_with_buf_perms(buf_perms@) &&
                    wgr.buf.len() == sz &&
                    producer_token.value().step is Reserved
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
                        assert(producer_token.value().step is GrantStarted);
                        assert(ret == false);
                    } else {
                        assert(write_in_progress_token.value() == true);
                        assert(producer_token.value().step is Idle);
                        assert(ret == true);
                    };
                }
        );

        if is_write_in_progress {
            proof {
                assert(producer_token.value().step is Idle);
            }
            return Err("write in progress");
        }

        proof {
            assert(producer_token.value().step is GrantStarted);
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
        assert(
            (start == write && write < read && write + sz < read) ||
            (start == write && !(write < read) && write + sz <= max) ||
            (start == 0 && !(write < read) && (write + sz > max && sz < read))
        );
        assert(start + sz <= self.vbq.length);

        // Safe write, only viewed by this task

        let tracked mut granted_perms_map;
        atomic_with_ghost!(&self.vbq.reserve => store(start + sz);
            ghost reserve_token => {
                // (Ghost<Map<nat, PointsTo<u8>>>, Tracked<Map<nat, PointsTo<u8>>>) が返る
                let tracked ret = self.vbq.instance.borrow().do_reserve((start + sz) as nat, &mut reserve_token, producer_token);
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
                // lemma で set の数と len() が一致することを示す。
                let base = self.vbq.buffer as nat + start as nat;
                let expected_dom = range_set(base, sz as nat);
                assert(granted_perms_map.dom() =~= expected_dom);
                assert(granted_perms_map.len() == sz) by {
                    lemma_range_set_len(base, sz as nat);
                };

                assert(reserve_token.value() == start + sz);
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
                forall |i: int| 0 <= i && i < granted_buf.len() ==> granted_perms_map.contains_key(granted_buf[i] as nat),
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

struct GrantW {
    buf: Vec<*mut u8>,
    vbq: Arc<VBBuffer>,
    to_commit: usize,
}

impl GrantW {
    pub closed spec fn wf_with_buf_perms(&self, buf_perms: Map<nat, raw_ptr::PointsTo<u8>>) -> bool {
        &&& self.buf.len() == buf_perms.len()
        &&& forall |i: int| 0 <= i && i < self.buf.len() ==> buf_perms.contains_key(self.buf[i] as nat)
        &&& forall |i: int| 0 <= i && i < self.buf.len() ==> self.buf[i] == buf_perms.index(self.buf[i] as nat).ptr()
        &&& forall |i: int| 0 <= i && i < self.buf.len() ==> self.buf[i]@.provenance == buf_perms.index(self.buf[i] as nat).ptr()@.provenance
    }

    pub closed spec fn wf_with_producer(&self, producer_state: ProducerState, buf_perms: Map<nat, raw_ptr::PointsTo<u8>>) -> bool {
        &&& producer_state.step is Idle
        &&& match (producer_state.write, producer_state.reserve) {
            (Some(w), Some(res)) => {
                let grant_start = if w < res {w} else {0};
                let grant_end = res;

                &&& self.buf.len() == grant_end - grant_start
                &&& forall |i: int| 0 <= i && i < self.buf.len() ==> buf_perms.index(self.buf[i] as nat).ptr().addr() == self.vbq.instance@.base_addr() as nat + grant_start + i as nat
                &&& forall |j: nat| j >= self.vbq.buffer as nat + grant_start && j < self.vbq.buffer as nat + grant_end
                    <==> buf_perms.contains_key(j)
                &&& forall |j: nat| j >= self.vbq.buffer as nat + grant_start && j < self.vbq.buffer as nat + grant_end
                    ==> (
                        buf_perms.index(j).ptr().addr() == j
                    )
                &&& forall |j: nat| j >= self.vbq.buffer as nat + grant_start && j < self.vbq.buffer as nat + grant_end
                    ==> (
                        buf_perms.index(j).ptr()@.provenance == self.vbq.instance@.provenance()
                    )
            },
            _ => true,
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
            old(producer_token).value().step is Idle || old(producer_token).value().step is Reserved,
            old(self).wf_with_producer(old(producer_token).value(), buf_perms)
        ensures
            producer_token.value().step is Idle,
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
            old(producer_token).value().step is Idle || old(producer_token).value().step is Reserved,
            old(self).wf_with_producer(old(producer_token).value(), buf_perms)
        ensures
            producer_token.value().step is Idle,
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
                    assert(producer_token.value().step is Idle || producer_token.value().step is Reserved);
                    let _ = self.vbq.instance.borrow().commit_start(&write_in_progress_token, producer_token);
                    assert(self.wf_with_producer(producer_token.value(), buf_perms));
                }
        );

        if !is_write_in_progress {
            assert(producer_token.value().step is Idle);
            return;
        }

        // Writer component. Must never write to READ,
        // be careful writing to LAST

        // Saturate the grant commit
        let len = self.buf.len();
        let used = if len <= used { len } else { used }; // min の代用。

        proof {
            assert(used <= len);
            assert(producer_token.value().step is Reserved);
        }

        let write = atomic_with_ghost!(&self.vbq.write => load();
            ghost write_token => {
                let _ = self.vbq.instance.borrow().commit_load_write(&write_token, producer_token);
                assert(self.wf_with_producer(producer_token.value(), buf_perms));
            }
        );

        proof {
            assert(producer_token.value().step is CommitWriteLoaded);
            assert(self.wf_with_producer(producer_token.value(), buf_perms));
        }

        atomic_with_ghost!(&self.vbq.reserve => fetch_sub(len - used);
            update prev -> next;
            returning ret;
            ghost reserve_token => {
                let _ = self.vbq.instance.borrow().commit_sub_reserve((len - used) as nat, &mut reserve_token, producer_token);
                assert(self.wf_with_producer(producer_token.value(), buf_perms));
            }
        );

        let max = self.vbq.length as usize;
        let last = atomic_with_ghost!(&self.vbq.last => load();
            ghost last_token => {
                let _ = self.vbq.instance.borrow().commit_load_last(&last_token, producer_token);
                assert(self.wf_with_producer(producer_token.value(), buf_perms));
            }
        );
        
        let new_write = atomic_with_ghost!(&self.vbq.reserve => load();
            ghost reserve_token => {
                let _ = self.vbq.instance.borrow().commit_load_reserve(&reserve_token, producer_token);
                assert(self.wf_with_producer(producer_token.value(), buf_perms));
            }
        );

        if (new_write < write) && (write != max) {
            // We have already wrapped, but we are skipping some bytes at the end of the ring.
            // Mark `last` where the write pointer used to be to hold the line here
            atomic_with_ghost!(&self.vbq.last => store(write);
                ghost last_token => {
                    let _ = self.vbq.instance.borrow().commit_store_last(write as nat, &mut last_token, producer_token);
                    assert(self.wf_with_producer(producer_token.value(), buf_perms));
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
                    assert(self.wf_with_producer(producer_token.value(), buf_perms));
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
                assert(self.wf_with_producer(producer_token.value(), buf_perms));
                assert(self.vbq.buffer as nat == self.vbq.instance@.base_addr());
                let _ = self.vbq.instance.borrow().commit_store_write(new_write as nat, buf_perms, buf_perms, &mut write_token, producer_token);
                assert(self.wf_with_producer(producer_token.value(), buf_perms));
            }
        );

        // Allow subsequent grants
        atomic_with_ghost!(&self.vbq.write_in_progress => store(false);
            ghost write_in_progress_token => {
                let _ = self.vbq.instance.borrow().commit_end(&mut write_in_progress_token, producer_token);
                assert(write_in_progress_token.value() == false);
            }
        );
    }

    /// Configures the amount of bytes to be commited on drop.
    pub fn to_commit(&mut self, amt: usize) {
        self.to_commit = self.buf.len().min(amt);
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