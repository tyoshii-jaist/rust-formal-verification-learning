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

pub struct ConsumerState {
    pub read_in_progress: bool,
    // 自分で管理するものは nat で持つ
    pub read: nat,
    // 観測して持つものは Option で持つ
    pub write_obs: Option<nat>,
    pub last_obs: Option<nat>,
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
    pub fn valid_read_obs_is_none_implies_no_grant(&self) -> bool {
        self.producer.read_obs is None ==> self.write == self.reserve
    }

    #[invariant]
    pub fn valid_write_max_implies_last_max(&self) -> bool {
        // write が終端(length)にいるなら、last も終端でなければならない
        self.write == self.length ==> self.last == self.length
    }

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
            require(pre.write_in_progress == false);
            require(pre.producer.read_obs is None);

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
            require(pre.producer.read_obs is None);
            assert(pre.producer.write == pre.write);
        }
    }

    transition!{
        load_read_at_grant() {
            require(pre.producer.read_obs is None);

            update producer = ProducerState {
                write_in_progress: pre.producer.write_in_progress,
                write: pre.producer.write,
                reserve: pre.producer.reserve,
                last: pre.producer.last,
                read_obs: Some(pre.read),
            };
        }
    }

    transition!{
        do_reserve(start: nat, sz: nat) {
            require(pre.producer.read_obs is Some);
            let new_reserve = start + sz;
            let read_obs = pre.producer.read_obs->Some_0;
            require(
                {
                    // not inverted & reserve not wrap
                    ||| read_obs <= pre.producer.write <= new_reserve <= pre.length
                    // not inverted & reserve wrap
                    ||| new_reserve < read_obs <= pre.producer.write <= pre.length
                    // inverted (write < read_obs) & read not wrap
                    ||| pre.producer.write <= new_reserve < read_obs /*<= pre.last */ <= pre.length
                }
            );

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
            require(pre.write_in_progress == true);
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
        start_commit() {
            require(pre.write_in_progress == true);
        }
    }

    transition!{
        load_write_at_commit() {
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
        }
    }

    transition!{
        load_reserve_at_commit() {
        }
    }

    transition!{
        update_last_by_write_at_commit(new_write: nat) {
            require(pre.producer.reserve < new_write && new_write != pre.length);
            update last = new_write; // write で last を更新する

            update producer = ProducerState {
                write_in_progress: pre.producer.write_in_progress,
                write: pre.producer.write,
                reserve: pre.producer.reserve,
                last: new_write,
                read_obs: pre.producer.read_obs,
            };
        }
    }

    transition!{
        update_last_by_max_at_commit() {
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
            require(pre.consumer.write_obs is None);

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
        }
    }
 
    transition!{
        wrap_read() {
            //require((pre.read == pre.consumer.last_obs->Some_0) && (pre.consumer.write_obs->Some_0 < pre.read));

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
            //require(pre.read_in_progress == true);
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
            require(pre.read_in_progress == true);
            require(pre.consumer.write_obs is Some);
            require(pre.consumer.last_obs is Some);
        }
    }

    transition!{
        add_read_at_release(used: nat) {
            /*require(pre.consumer.write_obs is Some);
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
            */
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
            // require(pre.read_in_progress == true);

            update read_in_progress = false;
            update consumer = ConsumerState {
                read_in_progress: false,
                read: pre.consumer.read,
                write_obs: None,
                last_obs: None,
            };
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
    fn start_commit_inductive(pre: Self, post: Self) { }
    
    #[inductive(load_write_at_commit)]
    fn load_write_at_commit_inductive(pre: Self, post: Self) { }
    
    #[inductive(sub_reserve_at_commit)]
    fn sub_reserve_at_commit_inductive(pre: Self, post: Self, commited: nat) { }
    
    #[inductive(load_last_at_commit)]
    fn load_last_at_commit_inductive(pre: Self, post: Self) { }
    
    #[inductive(load_reserve_at_commit)]
    fn load_reserve_at_commit_inductive(pre: Self, post: Self) { }
    
    #[inductive(update_last_by_write_at_commit)]
    fn update_last_by_write_at_commit_inductive(pre: Self, post: Self, new_write: nat) {
        assume(post.valid_write_max_implies_last_max());
    }
    
    #[inductive(update_last_by_max_at_commit)]
    fn update_last_by_max_at_commit_inductive(pre: Self, post: Self) {
    }
    
    #[inductive(store_write_at_commit)]
    fn store_write_at_commit_inductive(pre: Self, post: Self, new_write: nat) {
        // 以下の assert がないと
        // ||| self.reserve < read_obs <= self.read <= self.write <= self.length のケースで write が巻き戻ったあとの、
        // valid_producer_local_state_order の invariant が保たれることを示せない。
        assert(pre.reserve < pre.write ==> pre.write == pre.last);
        let read_obs = pre.producer.read_obs->Some_0;

        assert(new_write == pre.length ==> pre.last == pre.length);

        assert(
            {
                // not inverted & reserve not wrap
                ||| read_obs <= new_write == pre.reserve <= pre.length
                // inverted (write < read_obs) & read not wrap
                ||| new_write == pre.reserve < read_obs <= pre.last <= pre.length
            }
        );
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
                (Some(_), Some(_)) => true,
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
        (*self.vbq).wf()
    }
}

impl Producer {
    fn grant_exact(&mut self, sz: usize) -> (r: Result<GrantW, &'static str>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            match r {
                Ok(wgr) => {
                    &&& wgr.buf.len() == sz
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
                        let tracked mut prod_token = self.producer.borrow_mut().tracked_take();
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
                let tracked prod_token = self.producer.borrow_mut().tracked_take();
                let _ = self.vbq.instance.borrow().load_write_at_grant(&write_token, &prod_token);
            }
        );

        let read = atomic_with_ghost!(&self.vbq.read => load();
            ghost read_token => {
                let tracked mut prod_token = self.producer.borrow_mut().tracked_take();
                let _ = self.vbq.instance.borrow().load_read_at_grant(&read_token, &mut prod_token);
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
                        let tracked mut prod_token = self.producer.borrow_mut().tracked_take();
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
                            let tracked mut prod_token = self.producer.borrow_mut().tracked_take();
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
        assert(start + sz <= self.vbq.length);

        // Safe write, only viewed by this task

        atomic_with_ghost!(&self.vbq.reserve => store(start + sz);
            ghost reserve_token => {
                let ghost new_reserve: nat = (start + sz) as nat;
                assert({
                    // not inverted & reserve not wrap
                    ||| read <= write <= new_reserve <= max
                    // not inverted & reserve wrap
                    ||| new_reserve < read <= write <= max
                    // inverted (write < read_obs) & read not wrap
                    ||| write <= new_reserve < read <= max
                });
                let tracked mut prod_token = self.producer.borrow_mut().tracked_take();
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
                producer: Tracked(Some(self.producer.borrow_mut().tracked_take())),
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
    fn commit(&mut self,used: usize)
        requires
            old(self).vbq.wf(),
            used <= old(self).buf.len(),
        ensures
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
                    let _ = self.vbq.instance.borrow().start_commit(&mut write_in_progress_token);
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
                let tracked prod_token = self.producer.borrow_mut().tracked_take();
                let _ = self.vbq.instance.borrow().load_write_at_commit(&prod_token);
            }
        );

        atomic_with_ghost!(&self.vbq.reserve => fetch_sub(len - used);
            update prev -> next;
            returning ret;
            ghost reserve_token => {
                //assume(usize::MIN as int <= prev - (len - used));
                let tracked mut prod_token = self.producer.borrow_mut().tracked_take();
                let _ = self.vbq.instance.borrow().sub_reserve_at_commit((len - used) as nat, &mut reserve_token, &mut prod_token);
            }
        );

        let max = self.vbq.length as usize;
        let last = atomic_with_ghost!(&self.vbq.last => load();
            ghost last_token => {
                let _ = self.vbq.instance.borrow().load_last_at_commit();//(&last_token);
            }
        );
        
        let new_write = atomic_with_ghost!(&self.vbq.reserve => load();
            ghost reserve_token => {
                let _ = self.vbq.instance.borrow().load_reserve_at_commit();//(&reserve_token);
            }
        );

        if (new_write < write) && (write != max) {
            // We have already wrapped, but we are skipping some bytes at the end of the ring.
            // Mark `last` where the write pointer used to be to hold the line here
            atomic_with_ghost!(&self.vbq.last => store(write);
                ghost last_token => {
                    let tracked mut prod_token = self.producer.borrow_mut().tracked_take();
                    let _ = self.vbq.instance.borrow().update_last_by_write_at_commit(new_write as nat, &mut last_token, &mut prod_token);
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
                    let tracked mut prod_token = self.producer.borrow_mut().tracked_take();
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
                let tracked mut prod_token = self.producer.borrow_mut().tracked_take();
                let _ = self.vbq.instance.borrow().store_write_at_commit(new_write as nat, &mut write_token, &mut prod_token);
            }
        );

        // Allow subsequent grants
        atomic_with_ghost!(&self.vbq.write_in_progress => store(false);
            ghost write_in_progress_token => {
                let tracked mut prod_token = self.producer.borrow_mut().tracked_take();
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
}

impl Consumer {
    fn read(&mut self) ->  (r: Result<GrantR, &'static str>)
        requires
            old(self).wf(),
        ensures
            match r {
                Ok(rgr) => {
                    true//&&& rgr.buf.len() == consumer_token.value().grant_sz()
                },
                _ => true
            },
    {
        let is_read_in_progress =
            atomic_with_ghost!(&self.vbq.read_in_progress => swap(true);
                update prev -> next;
                returning ret;
                ghost read_in_progress_token => {
                    if !ret {
                        let tracked mut cons_token = self.consumer.borrow_mut().tracked_take();
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
                let tracked mut cons_token = self.consumer.borrow_mut().tracked_take();
                let _ = self.vbq.instance.borrow().load_write_at_read(&write_token, &mut cons_token);
            }
        );

        let last = atomic_with_ghost!(&self.vbq.last => load();
            ghost last_token => {
                let tracked mut cons_token = self.consumer.borrow_mut().tracked_take();
                let _ = self.vbq.instance.borrow().load_last_at_read(&last_token, &mut cons_token);
            }
        );
        
        let tracked mut read_perms_map:Map<nat, PointsTo<u8>> = Map::tracked_empty();
        let mut read = atomic_with_ghost!(&self.vbq.read => load();
            ghost read_token => {
                let tracked ret = self.vbq.instance.borrow().load_read_at_read();//(&read_token);
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
                    let tracked mut cons_token = self.consumer.borrow_mut().tracked_take();
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
                    let tracked mut cons_token = self.consumer.borrow_mut().tracked_take();
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
                consumer: Tracked(Some(self.consumer.borrow_mut().tracked_take())),
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
    fn release(&mut self,
        used: usize
    )
        requires
            used <= old(self).buf.len(),
            //old(self).wf_with_buf_perms(buf_perms),
            old(self).vbq.wf(),
        ensures
            self.vbq.wf(),

    {
        // If there is no grant in progress, return early. This
        // generally means we are dropping the grant within a
        // wrapper structure
        let is_read_in_progress =
            atomic_with_ghost!(&self.vbq.read_in_progress => load();
                ghost read_in_progress_token => {
                    let tracked mut cons_token = self.consumer.borrow_mut().tracked_take();
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
                let tracked mut cons_token = self.consumer.borrow_mut().tracked_take();
                let _ = self.vbq.instance.borrow().add_read_at_release(used as nat, &mut read_token, &mut cons_token);
            }
        );

        atomic_with_ghost!(&self.vbq.read_in_progress => store(false);
            ghost read_in_progress_token => {
                let tracked mut cons_token = self.consumer.borrow_mut().tracked_take();
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
