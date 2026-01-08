use state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
use vstd::raw_ptr::*;
use vstd::{prelude::*, *};
use vstd::layout::*;
use std::sync::Arc;

verus! {
pub struct ProducerState {
    pub write_in_progress: bool,

    // 自身で管理するのは nat で持つ
    pub write: nat,
    pub reserve: nat,
    pub last: nat,

    // 観測して持つものは Option で持つ
    pub read_obs: Option<nat>,
}

impl ProducerState {
    pub open spec fn grant_start(&self) -> nat {
        if self.write <= self.reserve {
            self.write
        } else {
            0
        }
    }

    pub open spec fn grant_end(&self) -> nat {
        self.reserve
    }

    pub open spec fn grant_sz(&self) -> nat {
        (self.grant_end() - self.grant_start()) as nat
    }
}

pub struct ConsumerState {
    pub read_in_progress: bool,
    // 自分で管理するものは nat で持つ
    pub read: nat,
    // 観測して持つものは Option で持つ
    pub write_obs: Option<nat>,
    pub last_obs: Option<nat>,
}

impl ConsumerState {
    pub open spec fn grant_start(&self) -> nat {
        self.read
    }

    pub open spec fn grant_end(&self) -> nat {
        match (self.write_obs, self.last_obs) {
            (Some(w), Some(l)) => {
                if self.read <= w {
                    w // not inverted
                } else {
                    l // inverted
                }
            },
            _ => self.read // no area
        }
    }

    pub open spec fn grant_sz(&self) -> nat {
        (self.grant_end() - self.grant_start()) as nat
    }
}

tokenized_state_machine!{VBQueue {
    fields {
        #[sharding(constant)]
        pub length: nat,

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
    pub fn valid_no_write_in_progress_implies_no_read_obs(&self) -> bool {
        self.producer.write_in_progress == false ==> self.producer.read_obs is None
    }

    #[invariant]
    pub fn valid_read_obs_is_none_implies_no_grant(&self) -> bool {
        self.producer.read_obs is None ==> self.write == self.reserve
    }

    /*
    #[invariant]
    pub fn valid_write_max_implies_last_max(&self) -> bool {
        // write が終端(length)にいるなら、last も終端でなければならない
        self.write == self.length ==> self.last == self.length
    } */

    #[invariant]
    pub fn valid_producer_local_state(&self) -> bool {
        &&& self.producer.write_in_progress == self.write_in_progress
        &&& self.producer.write == self.write
        &&& self.producer.reserve == self.reserve
        &&& self.producer.last == self.last
        &&& self.producer.read_obs is None ==> self.producer.write == self.producer.reserve
    }

    #[invariant]
    pub fn valid_order_from_producer_view(&self) -> bool {
        match self.producer.read_obs {
            Some(read_obs) => {
                // not inverted & reserve not wrap
                ||| read_obs <= self.read <= self.write <= self.reserve <= self.length
                // not inverted & reserve wrap
                ||| self.reserve < read_obs <= self.read <= self.write <= self.length
                // inverted (write < read_obs) & read not wrap
                ||| self.write <= self.reserve < read_obs <= self.read <= self.last <= self.length
                // converted to not inverted by wrapping read 
                ||| self.read <= self.write <= self.reserve < read_obs <= self.last <= self.length
            },
            None => {
                // not inverted & reserve not wrap
                ||| self.read <= self.write <= self.reserve <= self.length
                // not inverted & reserve wrap
                ||| self.reserve < self.read <= self.write <= self.length
                // inverted (write < read_obs) & read not wrap
                ||| self.write <= self.reserve < self.read <= self.last <= self.length
            }
        }
    }

    #[invariant]
    pub fn valid_consumer_local_state(&self) -> bool {
        &&& self.consumer.read_in_progress == self.read_in_progress
        &&& self.consumer.read == self.read
    }

    #[invariant]
    pub fn valid_order_from_consumer_view(&self) -> bool {
        match (self.consumer.write_obs, self.consumer.last_obs) {
            (Some(write_obs), None) => {
                // not inverted (read <= write_obs) & reserve not wrap
                ||| self.read <= write_obs <= self.write <= self.reserve <= self.length
                // not inverted & reserve wrap
                ||| self.reserve < self.read <= write_obs <= self.write <= self.length
                // converted to inverted by wrapping reserve and write
                ||| self.write <= self.reserve < self.read <= write_obs <= self.last <= self.length
                // inverted (write_obs < read) & read not wrap
                ||| write_obs <= self.write <= self.reserve < self.read <= self.length
            },
            (Some(write_obs), Some(last_obs) ) => {
                // not inverted (read <= write_obs) & reserve not wrap
                ||| self.read <= write_obs <= self.write <= self.reserve <= self.length
                // not inverted & reserve wrap
                ||| self.reserve < self.read <= write_obs <= self.write <= self.length
                // converted to inverted by wrapping reserve and write
                ||| self.write <= self.reserve < self.read <= write_obs <= self.last <= self.length
                // inverted (write_obs < read) & read not wrap
                ||| write_obs <= self.write <= self.reserve < self.read <= last_obs == self.last <= self.length
            },
            (None, Some(_) ) => false, // last だけを知っていることはあり得ない
            (None, None) => {
                ||| self.read <= self.write <= self.reserve <= self.length
                // not inverted & reserve wrap
                ||| self.reserve < self.read <= self.write <= self.length
                // inverted (write < read_obs) & read not wrap
                ||| self.write <= self.reserve < self.read <= self.last <= self.length
            },
        }
    }

    init! {
        initialize(
            length: nat,
        )
        {
            require(
                {
                    &&& length > 0 // TODO: 元の BBQueue はこの制約は持っていない
                }
            );

            init length = length;
            init write = 0;
            init read = 0;
            init last = length;
            init reserve = 0;
            init read_in_progress = false;
            init write_in_progress = false;
            init already_split = false;
            
            init producer = ProducerState {
                write_in_progress: false,
                write: 0,
                reserve: 0,
                last: length,
                read_obs: None,
            };

            init consumer = ConsumerState {
                read_in_progress: false,
                read: 0,
                write_obs: None,
                last_obs: None,
            };
        }
    }
    
    #[inductive(initialize)]
    fn initialize_inductive(post: Self, length: nat) {}

    transition!{
        try_split() {
            require(pre.already_split == false);

            update already_split = true;
        }
    }

    transition!{
        start_grant() {
            assert(pre.write_in_progress == false ==> pre.producer.read_obs is None);
            require(pre.write_in_progress == false);

            update write_in_progress = true;
            update producer = ProducerState {
                write_in_progress: true,
                write: pre.producer.write,
                reserve: pre.producer.reserve,
                last: pre.producer.last,
                read_obs: pre.producer.read_obs,
            };
        }
    }

    transition!{
        load_write_at_grant() {
            require(pre.producer.write_in_progress == true);
            require(pre.producer.read_obs is None);
            assert(pre.producer.write == pre.producer.reserve);
            assert(pre.producer.write == pre.write);
        }
    }

    transition!{
        load_read_at_grant() {
            require(pre.producer.write_in_progress == true);
            require(pre.producer.read_obs is None);
            assert(pre.producer.write == pre.producer.reserve);

            update producer = ProducerState {
                write_in_progress: pre.producer.write_in_progress,
                write: pre.producer.write,
                reserve: pre.producer.reserve,
                last: pre.producer.last,
                read_obs: Some(pre.read),
            };
            assert(pre.read <= pre.length);
        }
    }

    transition!{
        do_reserve(start: nat, sz: nat) {
            require(pre.producer.write_in_progress == true);
            require(pre.producer.read_obs is Some);
            let new_reserve = start + sz;
            let read_obs = pre.producer.read_obs->Some_0;
            require(
                {
                    ||| start == pre.producer.write && pre.producer.write < read_obs && pre.producer.write + sz < read_obs
                    ||| start == pre.producer.write && !(pre.producer.write < read_obs) && pre.producer.write + sz <= pre.length
                    ||| start == 0 && !(pre.producer.write < read_obs) && (pre.producer.write + sz > pre.length && sz < read_obs)
                }
            );/*
            require(
                {
                    // not inverted & reserve not wrap
                    ||| read_obs <= pre.producer.write <= new_reserve <= pre.length
                    // not inverted & reserve wrap
                    ||| new_reserve < read_obs <= pre.producer.write <= pre.length
                    // inverted (write < read_obs) & read not wrap
                    ||| pre.producer.write <= new_reserve < read_obs /*<= pre.last */ <= pre.length
                }
            ); */

            update reserve = start + sz;

            update producer = ProducerState {
                write_in_progress: pre.producer.write_in_progress,
                write: pre.producer.write,
                reserve: start + sz,
                last: pre.producer.last,
                read_obs: pre.producer.read_obs,
            };
        }
    }

    transition!{
        grant_fail() {
            require(pre.producer.write_in_progress == true);
            require(pre.producer.write == pre.producer.reserve);

            update write_in_progress = false;

            update producer = ProducerState {
                write_in_progress: false,
                write: pre.producer.write,
                reserve: pre.producer.reserve,
                last: pre.producer.last,
                read_obs: None,
            };
        }
    }

    transition!{
        start_commit(sz: nat) {
            assert(pre.producer.write_in_progress == pre.write_in_progress);
            require(
                pre.producer.write_in_progress == true ==> 
                    pre.producer.read_obs is Some && pre.producer.grant_sz() == sz
            );
        }
    }

    transition!{
        load_write_at_commit() {
            assert(pre.producer.write == pre.write);
            require(pre.producer.read_obs is Some);
        }
    } 
 
    transition!{
        sub_reserve_at_commit(commited: nat) {
            require(pre.reserve >= commited);

            let grant_start = if pre.producer.write <= pre.producer.reserve {pre.producer.write} else {0};
            require(pre.producer.reserve - grant_start >= commited);

            let new_reserve = (pre.producer.reserve - commited) as nat;

            update reserve = new_reserve;
            update producer = ProducerState {
                write_in_progress: pre.producer.write_in_progress,
                write: pre.producer.write,
                reserve: new_reserve,
                last: pre.producer.last,
                read_obs: pre.producer.read_obs,
            };
        }
    }

    transition!{
        load_last_at_commit() {
            assert(pre.last == pre.producer.last);
        }
    }

    transition!{
        load_reserve_at_commit() {
            assert(pre.reserve == pre.producer.reserve);
        }
    }

    transition!{
        update_last_by_write_at_commit(write: nat) {
            require(pre.producer.read_obs is Some);
            require(pre.producer.write == write);
            require(pre.producer.reserve < write && write != pre.length);
            update last = write; // write で last を更新する

            update producer = ProducerState {
                write_in_progress: pre.producer.write_in_progress,
                write: pre.producer.write,
                reserve: pre.producer.reserve,
                last: write,
                read_obs: pre.producer.read_obs,
            };
        }
    }

    transition!{
        update_last_by_max_at_commit() {
            require(pre.producer.read_obs is Some);
            require(!((pre.producer.reserve < pre.producer.write) && (pre.producer.write != pre.length)));
            require(pre.producer.reserve > pre.producer.last);

            update last = pre.length; // max で last を更新する

            update producer = ProducerState {
                write_in_progress: pre.producer.write_in_progress,
                write: pre.producer.write,
                reserve: pre.producer.reserve,
                last: pre.length,
                read_obs: pre.producer.read_obs,
            };
        }
    }

    transition!{
        store_write_at_commit(new_write: nat) {
            require(pre.producer.read_obs is Some);
            let read_obs = pre.producer.read_obs->Some_0;
            // 以下の assert がないと
            // ||| self.reserve < read_obs <= self.read <= self.write <= self.length のケースで write が巻き戻ったあとの、
            // valid_producer_local_state_order の invariant が保たれることを示せない。
            require(pre.producer.reserve < pre.producer.write ==> pre.producer.write == pre.producer.last);
            require(new_write == pre.length ==> pre.producer.last == pre.length);
            require(
                {
                    // not inverted & reserve not wrap
                    ||| read_obs <= new_write == pre.producer.reserve <= pre.length
                    // inverted (write < read_obs) & read not wrap
                    ||| new_write == pre.producer.reserve < read_obs <= pre.producer.last <= pre.length
                }
            );
            update write = new_write;

            update producer = ProducerState {
                write_in_progress: pre.producer.write_in_progress,
                write: new_write,
                reserve: pre.producer.reserve,
                last: pre.producer.last,
                read_obs: pre.producer.read_obs,
            };
        }
    }

    transition!{
        end_commit() {
            require(pre.producer.write == pre.producer.reserve);
            update write_in_progress = false;

            update producer = ProducerState {
                write_in_progress: false,
                write: pre.producer.write,
                reserve: pre.producer.reserve,
                last: pre.producer.last,
                read_obs: None,
            };
        }
    }

    transition!{
        start_read() {
            require(pre.read_in_progress == false);

            update read_in_progress = true;

            update consumer = ConsumerState {
                read_in_progress: true,
                read: pre.consumer.read,
                write_obs: pre.consumer.write_obs,
                last_obs: pre.consumer.last_obs,
            };
        }
    }

    transition!{
        load_write_at_read() {
            require(pre.consumer.read_in_progress == true);
            require(pre.consumer.write_obs is None);
            require(pre.consumer.last_obs is None);

            update consumer = ConsumerState {
                read_in_progress: pre.consumer.read_in_progress,
                read: pre.consumer.read,
                write_obs: Some(pre.write),
                last_obs: pre.consumer.last_obs,
            };
        }
    }

    transition!{
        load_last_at_read() {
            require(pre.consumer.read_in_progress == true);
            require(pre.consumer.write_obs is Some);
            require(pre.consumer.last_obs is None);

            update consumer = ConsumerState {
                read_in_progress: pre.consumer.read_in_progress,
                read: pre.consumer.read,
                write_obs: pre.consumer.write_obs,
                last_obs: Some(pre.last),
            };
        }
    }

    transition!{
        load_read_at_read() {
            require(pre.consumer.read_in_progress == true);
            require(pre.consumer.write_obs is Some);
            require(pre.consumer.last_obs is Some);
            assert(pre.consumer.read == pre.read);
        }
    }
 
    transition!{
        wrap_read() {
            require(pre.consumer.read_in_progress == true);
            require(pre.consumer.write_obs is Some);
            require(pre.consumer.last_obs is Some);
            require((pre.read == pre.consumer.last_obs->Some_0) && (pre.consumer.write_obs->Some_0 < pre.read));

            update read = 0;
            update consumer = ConsumerState {
                read_in_progress: pre.consumer.read_in_progress,
                read: 0,
                write_obs: pre.consumer.write_obs,
                last_obs: pre.consumer.last_obs,
            };
        }
    }

    transition!{
        read_fail() {
            require(pre.read_in_progress == true);
            update read_in_progress = false;

            update consumer = ConsumerState {
                read_in_progress: false,
                read: pre.consumer.read,
                write_obs: None,
                last_obs: None,
            };
        }
    }

    transition!{
        start_release() {
            assert(pre.read_in_progress == pre.consumer.read_in_progress);
            require(pre.read_in_progress == true ==> pre.consumer.write_obs is Some && pre.consumer.last_obs is Some);
        }
    }

    transition!{
        add_read_at_release(used: nat) {
            require(pre.consumer.read_in_progress == true);
            require(pre.consumer.write_obs is Some);
            require(pre.consumer.last_obs is Some);

            let write_obs = pre.consumer.write_obs->Some_0;
            let last_obs = pre.consumer.last_obs->Some_0;
            let grant_end = if pre.read <= write_obs {
                    write_obs // not inverted
                } else {
                    last_obs // inverted
                };
            require(grant_end - pre.read >= used);
            require(pre.read + used <= pre.length);

            require(
                {
                    // not inverted (read <= write_obs) & reserve not wrap
                    ||| pre.read + used <= write_obs <= pre.length
                    // inverted (write_obs < read) & read not wrap
                    ||| write_obs < pre.read + used <= last_obs <= pre.length
                }
            );

            update read = pre.read + used;
            update consumer = ConsumerState {
                read_in_progress: pre.consumer.read_in_progress,
                read: pre.consumer.read + used,
                write_obs: pre.consumer.write_obs,
                last_obs: pre.consumer.last_obs,
            };
        }
    }
    
    transition!{
        end_release() {
            require(pre.read_in_progress == true);

            update read_in_progress = false;
            update consumer = ConsumerState {
                read_in_progress: false,
                read: pre.consumer.read,
                write_obs: None,
                last_obs: None,
            };
        }
    }

    transition!{
        check_write_equality() {
            assert(pre.producer.write == pre.write);
        }
    }

    transition!{
        check_reserve_equality() {
            assert(pre.producer.reserve == pre.reserve);
        }
    }

    transition!{
        check_last_equality() {
            assert(pre.producer.last == pre.last);
        }
    }

    transition!{
        check_read_equality() {
            assert(pre.consumer.read == pre.read);
        }
    }

    #[inductive(try_split)]
    fn try_split_inductive(pre: Self, post: Self) { }
    
    #[inductive(start_grant)]
    fn start_grant_inductive(pre: Self, post: Self) {
        assert(pre.write == pre.reserve);
    }
    
    #[inductive(load_write_at_grant)]
    fn load_write_at_grant_inductive(pre: Self, post: Self) { }
    
    #[inductive(load_read_at_grant)]
    fn load_read_at_grant_inductive(pre: Self, post: Self) {
        assert(pre.write == pre.reserve);
    }


    #[inductive(do_reserve)]
    fn do_reserve_inductive(pre: Self, post: Self, start: nat, sz: nat) {
    }
    
    #[inductive(grant_fail)]
    fn grant_fail_inductive(pre: Self, post: Self) {
    }
    
    #[inductive(start_commit)]
    fn start_commit_inductive(pre: Self, post: Self, sz: nat) { }
    
    #[inductive(load_write_at_commit)]
    fn load_write_at_commit_inductive(pre: Self, post: Self) { }
    

    #[inductive(sub_reserve_at_commit)]
    fn sub_reserve_at_commit_inductive(pre: Self, post: Self, commited: nat) { }
    
    #[inductive(load_last_at_commit)]
    fn load_last_at_commit_inductive(pre: Self, post: Self) { }
    
    #[inductive(load_reserve_at_commit)]
    fn load_reserve_at_commit_inductive(pre: Self, post: Self) { }
    
    #[inductive(update_last_by_write_at_commit)]
    fn update_last_by_write_at_commit_inductive(pre: Self, post: Self, write: nat) {
    }

    #[inductive(update_last_by_max_at_commit)]
    fn update_last_by_max_at_commit_inductive(pre: Self, post: Self) {
        assert(!((pre.producer.reserve < pre.producer.write) && (pre.producer.write != pre.length)));
        assert(pre.producer.reserve > pre.producer.last);
    }
    
    #[inductive(store_write_at_commit)]
    fn store_write_at_commit_inductive(pre: Self, post: Self, new_write: nat) {
    }
    
    #[inductive(end_commit)]
    fn end_commit_inductive(pre: Self, post: Self) { }
    
    #[inductive(start_read)]
    fn start_read_inductive(pre: Self, post: Self) { }
    
    #[inductive(load_write_at_read)]
    fn load_write_at_read_inductive(pre: Self, post: Self) { }
    
    #[inductive(load_last_at_read)]
    fn load_last_at_read_inductive(pre: Self, post: Self) { }
    
    #[inductive(load_read_at_read)]
    fn load_read_at_read_inductive(pre: Self, post: Self) { }
    
    #[inductive(wrap_read)]
    fn wrap_read_inductive(pre: Self, post: Self) { }
    
    #[inductive(read_fail)]
    fn read_fail_inductive(pre: Self, post: Self) { }
    
    #[inductive(start_release)]
    fn start_release_inductive(pre: Self, post: Self) { }
    
    #[inductive(add_read_at_release)]
    fn add_read_at_release_inductive(pre: Self, post: Self, used: nat) { }
    
    #[inductive(end_release)]
    fn end_release_inductive(pre: Self, post: Self) { }

    #[inductive(check_write_equality)]
    fn check_write_equality_inductive(pre: Self, post: Self) { }

    #[inductive(check_reserve_equality)]
    fn check_reserve_equality_inductive(pre: Self, post: Self) { }

    #[inductive(check_last_equality)]
    fn check_last_equality_inductive(pre: Self, post: Self) { }
    
    #[inductive(check_read_equality)]
    fn check_read_equality_inductive(pre: Self, post: Self) { }
}}

struct_with_invariants!{
    pub struct VBBuffer {
        length: usize,
        write: AtomicUsize<_, VBQueue::write, _>,
        read: AtomicUsize<_, VBQueue::read, _>,
        last: AtomicUsize<_, VBQueue::last, _>,
        reserve: AtomicUsize<_, VBQueue::reserve, _>,
        read_in_progress: AtomicBool<_, VBQueue::read_in_progress, _>,
        write_in_progress: AtomicBool<_, VBQueue::write_in_progress, _>, 
        already_split: AtomicBool<_, VBQueue::already_split, _>,

        instance: Tracked<VBQueue::Instance>,
        producer: Tracked<Option<VBQueue::producer>>,
        consumer: Tracked<Option<VBQueue::consumer>>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            &&& self.instance@.length() == self.length
            &&& match self.producer@ {
                    Some(prod) => prod.instance_id() == self.instance@.id(),
                    None => true,
                }
            &&& match self.consumer@ {
                    Some(cons) => cons.instance_id() == self.instance@.id(),
                    None => true,
                }
        }

        invariant on write with (instance) is (v: usize, g: VBQueue::write) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
        }

        invariant on read with (instance) is (v: usize, g: VBQueue::read) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
        }

        invariant on last with (instance) is (v: usize, g: VBQueue::last) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
        }

        invariant on reserve with (instance) is (v: usize, g: VBQueue::reserve) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
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

impl VBBuffer
{
    fn new(length: usize) -> (r: Self)
        requires
            valid_layout(length, 1),
            length > 0, // TODO: 元の BBQueue はこの制約は持っていない。0で使うことはないと思うが。
        ensures
            r.wf(),
            match (r.producer@, r.consumer@) {
                (Some(_), Some(_)) => true,
                _ => false,
            }
    {
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
            length as nat,
        );

        let tracked_inst: Tracked<VBQueue::Instance> = Tracked(instance.clone());
        let write_atomic = AtomicUsize::new(Ghost(tracked_inst), 0, Tracked(write_token));
        let read_atomic = AtomicUsize::new(Ghost(tracked_inst), 0, Tracked(read_token));
        let last_atomic = AtomicUsize::new(Ghost(tracked_inst), length, Tracked(last_token));
        let reserve_atomic = AtomicUsize::new(Ghost(tracked_inst), 0, Tracked(reserve_token));
        let read_in_progress_atomic = AtomicBool::new(Ghost(tracked_inst), false, Tracked(read_in_progress_token));
        let write_in_progress_atomic = AtomicBool::new(Ghost(tracked_inst), false, Tracked(write_in_progress_token));
        let already_split_atomic = AtomicBool::new(Ghost(tracked_inst), false, Tracked(already_split_token));

        // Initialize the queue
        Self {
            length,
            write: write_atomic,
            read: read_atomic,
            last: last_atomic,
            reserve: reserve_atomic,
            read_in_progress: read_in_progress_atomic,
            write_in_progress: write_in_progress_atomic,
            already_split: already_split_atomic,
            instance: Tracked(instance),
            producer: Tracked(Some(producer_token)),
            consumer: Tracked(Some(consumer_token)),
        }
    }

    fn try_split(self) -> (res: Result<(Producer, Consumer),  &'static str>)
        requires
            self.wf(),
            match (self.producer@, self.consumer@) {
                (Some(prod), Some(cons)) => prod.instance_id() == self.instance@.id() && cons.instance_id() == self.instance@.id(),
                _ => false,
            }
        ensures
            match res {
                Ok((prod, cons)) => {
                    &&& prod.wf()
                    &&& cons.wf()
                }, 
                Err(_) => true
            },
    {
        let mut slf = self;

        let already_splitted =
            atomic_with_ghost!(&slf.already_split => swap(true);
                update prev -> next;
                returning ret;
                ghost already_split_token => {
                    if !ret {
                        let _ = slf.instance.borrow().try_split(&mut already_split_token);
                    };
                }
        );

        if already_splitted {
            return Err("already splitted");
        }

        let tracked prod_token = slf.producer.borrow_mut().tracked_take();
        let tracked cons_token = slf.consumer.borrow_mut().tracked_take();
        // FIXME:元の実装は Arc は使っていない。
        // また、buffer のゼロ化もしているが、こちらは今はやっていない。
        let vbbuffer_arc = Arc::new(slf);
        Ok((
            Producer {
                vbq: vbbuffer_arc.clone(),
                producer: Tracked(Some(prod_token)),
            },
            Consumer {
                vbq: vbbuffer_arc.clone(),
                consumer: Tracked(Some(cons_token)),
            }
        ))
    }
}

pub struct Producer {
    vbq: Arc<VBBuffer>,
    producer: Tracked<Option<VBQueue::producer>>,
}

impl Producer {
    pub closed spec fn wf(&self) -> bool {
        &&& (*self.vbq).wf()
    }

    pub closed spec fn is_idle(&self) -> bool {
        &&& self.producer@ is Some
        &&& self.producer@->0.instance_id() == self.vbq.instance@.id()
        &&& (
            self.producer@->0.value().write_in_progress == false ==> 
                self.producer@->0.value().read_obs is None
        )
    }

    pub closed spec fn is_granted(&self, sz: nat) -> bool {
        &&& self.producer@ is Some
        &&& self.producer@->0.instance_id() == self.vbq.instance@.id()
        &&& (
            self.producer@->0.value().write_in_progress == true ==> 
                self.producer@->0.value().read_obs is Some && self.producer@->0.value().grant_sz() == sz
        )
    }
}

impl Producer {
    fn grant_exact(&mut self, sz: usize) -> (r: Result<GrantW, &'static str>)
        requires
            old(self).wf(),
            old(self).is_idle(),
            match old(self).producer@ {
                Some(prod) => true, //prod.instance_id() == old(self).vbq.instance@.id(),
                _ => false,
            }
        ensures
            self.wf(),
            match r {
                Ok(wgr) => {
                    &&& wgr.buf.len() == sz
                    &&& wgr.is_granted(sz as nat)
                    &&& match wgr.producer@ {
                        Some(prod) => prod.instance_id() == self.vbq.instance@.id(),
                        _ => false,
                    }
                },
                _ => true
            },
    {
        proof{
            assert(self.producer@->0.value().write_in_progress == false ==> 
                self.producer@->0.value().read_obs is None);
        }
        let tracked mut prod_token = self.producer.borrow_mut().tracked_take();
        let is_write_in_progress =
            atomic_with_ghost!(&self.vbq.write_in_progress => swap(true);
                update prev -> next;
                returning ret;
                ghost write_in_progress_token => {
                    if !ret {
                        let _ = self.vbq.instance.borrow().start_grant(&mut write_in_progress_token, &mut prod_token);
                        assert(write_in_progress_token.value() == true);
                        assert(ret == false);
                    } else {
                        assert(write_in_progress_token.value() == true);
                        assert(ret == true);
                    };
                }
        );

        if is_write_in_progress {
            return Err("write in progress");
        }

        let write = atomic_with_ghost!(&self.vbq.write => load();
            returning ret;
            ghost write_token => {
                let _ = self.vbq.instance.borrow().load_write_at_grant(&write_token, &prod_token);
            }
        );

        let read = atomic_with_ghost!(&self.vbq.read => load();
            ghost read_token => {
                let _ = self.vbq.instance.borrow().load_read_at_grant(&read_token, &mut prod_token);
                assert(prod_token.value().write_in_progress == true);
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
                        let _ = self.vbq.instance.borrow().grant_fail(&mut write_in_progress_token, &mut prod_token);
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
                            assert(prod_token.value().write_in_progress == true);
                            let _ = self.vbq.instance.borrow().grant_fail(&mut write_in_progress_token, &mut prod_token);
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
        // assert(start + sz <= self.vbq.length);

        // Safe write, only viewed by this task
        atomic_with_ghost!(&self.vbq.reserve => store(start + sz);
            ghost reserve_token => {
                let ghost new_reserve: nat = (start + sz) as nat;
                assert(
                    (start == write && write < read && write + sz < read) ||
                    (start == write && !(write < read) && write + sz <= max) ||
                    (start == 0 && !(write < read) && (write + sz > max && sz < read))
                );
                let tracked ret = self.vbq.instance.borrow().do_reserve(start as nat, sz as nat, &mut reserve_token, &mut prod_token);
                assert(reserve_token.value() == start + sz);
            }
        );


        let mut granted_buf: Vec<u8> = Vec::new();
        let end_offset = start + sz;

        for idx in start..end_offset
            invariant
                granted_buf.len() == idx - start,
                idx <= end_offset,
                granted_buf.len() == (idx - start),
            decreases
                end_offset - idx,
        {
            granted_buf.push(0); // dummy
        }

        proof {
            assert(granted_buf.len() == sz);
        }
        Ok (
            GrantW {
                buf: granted_buf,
                vbq: self.vbq.clone(),
                to_commit: sz,
                producer: Tracked(Some(prod_token)),
            }
        )
    }
}

struct GrantW {
    buf: Vec<u8>,//Vec<*mut u8>,
    vbq: Arc<VBBuffer>,
    to_commit: usize,
    producer: Tracked<Option<VBQueue::producer>>,
}

impl GrantW {
    pub closed spec fn is_granted(&self, sz: nat) -> bool {
        &&& self.producer@ is Some
        &&& self.producer@->0.instance_id() == self.vbq.instance@.id()
        &&& (
            self.producer@->0.value().write_in_progress == true ==> 
                self.producer@->0.value().read_obs is Some && self.producer@->0.value().grant_sz() == sz
        )
    }
}

impl GrantW {
    fn commit(&mut self, used: usize)
        requires
            old(self).vbq.wf(),
            used <= old(self).buf.len(),
            old(self).is_granted(old(self).buf.len() as nat),
            match old(self).producer@ {
                Some(prod) => prod.instance_id() == old(self).vbq.instance@.id(),
                _ => false,
            }
        ensures
            self.vbq.wf(),
            /*
            match self.producer@ {
                Some(prod) => prod.instance_id() == self.vbq.instance@.id(),
                _ => false,
            } */
    {
        // If there is no grant in progress, return early. This
        // generally means we are dropping the grant within a
        // wrapper structure
        let tracked prod_token = self.producer.borrow_mut().tracked_take();

        let is_write_in_progress =
            atomic_with_ghost!(&self.vbq.write_in_progress => load();
                update prev -> next;
                returning ret;
                ghost write_in_progress_token => {
                    let _ = self.vbq.instance.borrow().start_commit(self.buf.len() as nat, &mut write_in_progress_token, &prod_token);
                }
        );

        if !is_write_in_progress {
            return;
        }

        // Writer component. Must never write to READ,
        // be careful writing to LAST

        // Saturate the grant commit
        let len = self.buf.len();
        let used = if len <= used { len } else { used }; // min の代用。

        let write = atomic_with_ghost!(&self.vbq.write => load();
            ghost write_token => {
                self.vbq.instance.borrow().check_write_equality(&write_token, &prod_token);
                let _ = self.vbq.instance.borrow().load_write_at_commit(&write_token, &prod_token);
            }
        );

        atomic_with_ghost!(&self.vbq.reserve => fetch_sub(len - used);
            update prev -> next;
            returning ret;
            ghost reserve_token => {
                self.vbq.instance.borrow().check_reserve_equality(&reserve_token, &prod_token);
                assert(prod_token.value().grant_sz() == len as int);
                assert(prod_token.value().reserve >= len as int);
                assert(prod_token.value().reserve == reserve_token.value());
                assert(prod_token.value().reserve == prev);
                assert(usize::MIN as int <= prod_token.value().reserve - (len - used));
                assert(usize::MIN as int <= prev - (len - used));
                let _ = self.vbq.instance.borrow().sub_reserve_at_commit((len - used) as nat, &mut reserve_token, &mut prod_token);
            }
        );

        let max = self.vbq.length as usize;
        let last = atomic_with_ghost!(&self.vbq.last => load();
            ghost last_token => {
                let _ = self.vbq.instance.borrow().load_last_at_commit(&last_token, &prod_token);
            }
        );

        let new_write = atomic_with_ghost!(&self.vbq.reserve => load();
            ghost reserve_token => {
                let _ = self.vbq.instance.borrow().load_reserve_at_commit(&reserve_token, &prod_token);
                assert(reserve_token.value() == prod_token.value().reserve);
            }
        );

        if (new_write < write) && (write != max) {
            // We have already wrapped, but we are skipping some bytes at the end of the ring.
            // Mark `last` where the write pointer used to be to hold the line here
            atomic_with_ghost!(&self.vbq.last => store(write);
                ghost last_token => {
                    self.vbq.instance.borrow().check_last_equality(&last_token, &prod_token);
                    let _ = self.vbq.instance.borrow().update_last_by_write_at_commit(write as nat, &mut last_token, &mut prod_token);
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
                    let _ = self.vbq.instance.borrow().update_last_by_max_at_commit(&mut last_token, &mut prod_token);
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
                let _ = self.vbq.instance.borrow().store_write_at_commit(new_write as nat, &mut write_token, &mut prod_token);
            }
        );

        // Allow subsequent grants
        atomic_with_ghost!(&self.vbq.write_in_progress => store(false);
            ghost write_in_progress_token => {
                let _ = self.vbq.instance.borrow().end_commit(&mut write_in_progress_token, &mut prod_token);
                assert(write_in_progress_token.value() == false);
            }
        );
    }

    /// Configures the amount of bytes to be commited on drop.
    pub fn to_commit(&mut self, amt: usize) {
        self.to_commit = self.buf.len().min(amt);
    }
}

pub struct Consumer {
    vbq: Arc<VBBuffer>,
    consumer: Tracked<Option<VBQueue::consumer>>,
}

impl Consumer {
    pub closed spec fn wf(&self) -> bool {
        (*self.vbq).wf()
    }

    pub closed spec fn is_idle(&self) -> bool {
        &&& self.consumer@ is Some
        &&& self.consumer@->0.instance_id() == self.vbq.instance@.id()
        &&& self.consumer@->0.value().write_obs is None
        &&& self.consumer@->0.value().last_obs is None  
    }
}

impl Consumer {
    fn read(&mut self) ->  (r: Result<GrantR, &'static str>)
        requires
            old(self).wf(),
            old(self).is_idle(),
        ensures
            match r {
                Ok(rgr) => {
                    true//&&& rgr.buf.len() == consumer_token.value().grant_sz()
                },
                _ => true
            },
    {
        let tracked mut cons_token = self.consumer.borrow_mut().tracked_take();

        let is_read_in_progress =
            atomic_with_ghost!(&self.vbq.read_in_progress => swap(true);
                update prev -> next;
                returning ret;
                ghost read_in_progress_token => {
                    if !ret {
                        let _ = self.vbq.instance.borrow().start_read(&mut read_in_progress_token, &mut cons_token);
                        assert(read_in_progress_token.value() == true);
                    } else {
                        assert(read_in_progress_token.value() == true);
                        assert(ret == true);
                    };
                }
        );

        if is_read_in_progress {
            return Err("read in progress");
        }

        let write = atomic_with_ghost!(&self.vbq.write => load();
            ghost write_token => {
                let _ = self.vbq.instance.borrow().load_write_at_read(&write_token, &mut cons_token);
            }
        );

        let last = atomic_with_ghost!(&self.vbq.last => load();
            ghost last_token => {
                let _ = self.vbq.instance.borrow().load_last_at_read(&last_token, &mut cons_token);
            }
        );
        
        let tracked mut read_perms_map:Map<nat, PointsTo<u8>> = Map::tracked_empty();
        let mut read = atomic_with_ghost!(&self.vbq.read => load();
            ghost read_token => {
                let tracked ret = self.vbq.instance.borrow().load_read_at_read(&read_token, &cons_token);
            }
        );

        // Resolve the inverted case or end of read
        if (read == last) && (write < read) {
            read = 0;
            // This has some room for error, the other thread reads this
            // Impact to Grant:
            //   Grant checks if read < write to see if inverted. If not inverted, but
            //     no space left, Grant will initiate an inversion, but will not trigger it
            // Impact to Commit:
            //   Commit does not check read, but if Grant has started an inversion,
            //   grant could move Last to the prior write position
            // MOVING READ BACKWARDS!
            atomic_with_ghost!(&self.vbq.read => store(0);
                ghost read_token => {
                    // ここで read が wrap する。
                    // read == last の状態で、かつ、write < read なので、inverted 状態になる。
                    let _ = self.vbq.instance.borrow().wrap_read(&mut read_token, &mut cons_token);
                    // ↑をまたぐと
                    // read == 0 になるので not inverted に切り替わる
                    // この瞬間に producer はまだ inverted
                    // read == 0 read_obs == 9 write == 9 で last は 10 のとき、not inverted 判断になる。
                }
            );
        }

        let sz = if write < read {
            // Inverted, only believe last
            assume(last >= read);
            last
        } else {
            // Not inverted, only believe write
            assume(write >= read);
            write
        } - read;

        if sz == 0 {
            atomic_with_ghost!(&self.vbq.read_in_progress => store(false);
                ghost read_in_progress_token => {
                    let _ = self.vbq.instance.borrow().read_fail(&mut read_in_progress_token, &mut cons_token);
                    assert(read_in_progress_token.value() == false);
                }
            );
            return Err("Insufficient size");
        }

        // This is sound, as UnsafeCell, MaybeUninit, and GenericArray
        // are all `#[repr(Transparent)]
        //let start_of_buf_ptr = inner.buf.get().cast::<u8>();
        //let grant_slice = unsafe { from_raw_parts_mut(start_of_buf_ptr.offset(read as isize), sz) };
        let mut granted_buf: Vec<u8> = Vec::new();

        for idx in read..(read + sz)
            invariant
                granted_buf.len() == idx - read,
                idx <= (read + sz),
                granted_buf.len() == (idx - read),
            decreases
                (read + sz) - idx,
        {
            granted_buf.push(0);
        }
        assert(granted_buf.len() == sz);

        Ok(
            GrantR {
                buf: granted_buf,
                vbq: self.vbq.clone(),
                to_release: 0,
                consumer: Tracked(Some(cons_token)),
            }
        )
    }
}

struct GrantR {
    buf: Vec<u8>,//Vec<*mut u8>,
    vbq: Arc<VBBuffer>,
    to_release: usize,
    consumer: Tracked<Option<VBQueue::consumer>>,
}

impl GrantR {
    pub closed spec fn is_granted(&self, sz: nat) -> bool {
        &&& self.consumer@ is Some
        &&& self.consumer@->0.instance_id() == self.vbq.instance@.id()
        &&& (
            self.consumer@->0.value().read_in_progress == true ==> 
                self.consumer@->0.value().write_obs is Some && self.consumer@->0.value().last_obs is Some && self.consumer@->0.value().grant_sz() == sz
        )
    }
}

impl GrantR {
    fn release(&mut self,
        used: usize
    )
        requires
            used <= old(self).buf.len(),
            //old(self).wf_with_buf_perms(buf_perms),
            old(self).vbq.wf(),
            old(self).is_granted(old(self).buf.len() as nat),
        ensures
            self.vbq.wf(),

    {
        let tracked mut cons_token = self.consumer.borrow_mut().tracked_take();

        // If there is no grant in progress, return early. This
        // generally means we are dropping the grant within a
        // wrapper structure
        let is_read_in_progress =
            atomic_with_ghost!(&self.vbq.read_in_progress => load();
                ghost read_in_progress_token => {
                    let _ = self.vbq.instance.borrow().start_release(&mut read_in_progress_token, &mut cons_token);
                }
        );

        if !is_read_in_progress {
            return;
        }

        // This should always be checked by the public interfaces
        // debug_assert!(used <= self.buf.len());

        // This should be fine, purely incrementing
        let _ = atomic_with_ghost!(&self.vbq.read => fetch_add(used);
            update prev -> next;
            returning ret;
            ghost read_token => {
                let _ = self.vbq.instance.borrow().add_read_at_release(used as nat, &mut read_token, &mut cons_token);
            }
        );

        atomic_with_ghost!(&self.vbq.read_in_progress => store(false);
            ghost read_in_progress_token => {
                let _ = self.vbq.instance.borrow().end_release(&mut read_in_progress_token, &mut cons_token);
                assert(read_in_progress_token.value() == false);
            }
        );
    }

    /// Configures the amount of bytes to be released on drop.
    pub fn to_release(&mut self, amt: usize) {
        self.to_release = self.buf.len().min(amt);
    }
}


fn main() {
    /*
    let vbuf = VBBuffer::new(6);
    let (mut prod, mut cons) = match vbuf.try_split() {
        Ok((prod, cons)) => (prod, cons),
        Err(_) => {
            return;
        }
    };

    // Request space for one byte
    match prod.grant_exact(2) {
        Ok(wgr) => {
            wgr.commit(2);
        },
        _ => {}
    }
     */
}
}
