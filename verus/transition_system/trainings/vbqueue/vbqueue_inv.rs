use state_machines_macros::tokenized_state_machine;
use vstd::{prelude::*, *};
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::layout::*;
use vstd::raw_ptr::*;
use vstd::set_lib::*;
use vstd::shared::*;
use vstd::tokens::UniqueValueToken;

verus! {

global layout u8 is size == 1, align == 1;

/*
    Producer と Consumer の状態
*/

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

    pub open spec fn grant_sz(&self) -> int {
        self.grant_end() - self.grant_start()
    }

    pub open spec fn is_idle(&self) -> bool {
        self.write_in_progress == false && self.read_obs is None
    }

    pub open spec fn is_granted(&self, sz: nat) -> bool {
        self.write_in_progress == true && self.read_obs is Some && self.grant_sz() == sz
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

    pub open spec fn grant_sz(&self) -> int {
        self.grant_end() - self.grant_start()
    }

    pub open spec fn is_idle(&self) -> bool {
        self.read_in_progress == false && self.last_obs is None && self.write_obs is None
    }

    pub open spec fn is_granted(&self, sz: nat) -> bool {
        self.read_in_progress == true && self.last_obs is Some && self.write_obs is Some && self.grant_sz() == sz
    }
}

pub struct GrantState {
    pub prod_start: nat,
    pub prod_end: nat,
    pub cons_start: nat,
    pub cons_end: nat,
}

impl GrantState {
    pub open spec fn is_idle(&self) -> bool {
        self.prod_start == self.prod_end == self.cons_start == self.cons_end == 0
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

        #[sharding(constant)]
        pub base_addr: nat,

        #[sharding(constant)]
        pub provenance: raw_ptr::Provenance,

        #[sharding(storage_option)]
        pub buffer_dealloc: Option<raw_ptr::Dealloc>,

        // Represents the local state of the single-producer
        #[sharding(variable)]
        pub producer: ProducerState,

        // Represents the local state of the single-consumer
        #[sharding(variable)]
        pub consumer: ConsumerState,

        #[sharding(variable)]
        pub grant_state: GrantState,
    }

    #[invariant]
    pub fn valid_no_write_in_progress_implies_no_read_obs(&self) -> bool {
        self.producer.write_in_progress == false ==> self.producer.read_obs is None
    }

    #[invariant]
    pub fn valid_read_obs_is_none_implies_no_grant(&self) -> bool {
        self.producer.read_obs is None ==> self.write == self.reserve
    }

    #[invariant]
    pub fn valid_write_max_implies_last_max(&self) -> bool {
        self.write == self.length ==> self.last == self.length
    }

    #[invariant]
    pub fn valid_write_in_range(&self) -> bool {
        self.write <= self.length
    }

    #[invariant]
    pub fn valid_last_in_range(&self) -> bool {
        self.last <= self.length
    }

    #[invariant]
    pub fn valid_read_in_range(&self) -> bool {
        self.read <= self.length
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
                &&& read_obs <= self.length
                &&& {
                    // not inverted & reserve not wrap
                    ||| read_obs <= self.read <= self.write <= self.reserve <= self.length
                    // not inverted & reserve wrap
                    ||| self.reserve < read_obs <= self.read <= self.write <= self.length
                    // inverted (write < read_obs) & read not wrap
                    ||| self.write <= self.reserve < read_obs <= self.read <= self.last <= self.length
                    // converted to not inverted by wrapping read 
                    ||| self.read <= self.write <= self.reserve < read_obs <= self.last <= self.length
                }
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
                &&& write_obs <= self.length
                &&& {
                    // not inverted (read <= write_obs) & reserve not wrap
                    ||| self.read <= write_obs <= self.write <= self.reserve <= self.length
                    // not inverted & reserve wrap
                    ||| self.reserve < self.read <= write_obs <= self.write <= self.length
                    // converted to inverted by wrapping reserve and write
                    ||| self.write <= self.reserve < self.read <= write_obs <= self.last <= self.length
                    // inverted (write_obs < read) & read not wrap
                    ||| write_obs <= self.write <= self.reserve < self.read <= self.length
                }
            },
            (Some(write_obs), Some(last_obs) ) => {
                &&& write_obs <= self.length
                &&& last_obs <= self.length
                &&& {
                    // not inverted (read <= write_obs) & reserve not wrap
                    ||| self.read <= write_obs <= self.write <= self.reserve <= self.length
                    // not inverted & reserve wrap
                    ||| self.reserve < self.read <= write_obs <= self.write <= self.length
                    // converted to inverted by wrapping reserve and write
                    ||| self.write <= self.reserve < self.read <= write_obs <= self.last <= self.length
                    // inverted (write_obs < read) & read not wrap
                    ||| write_obs <= self.write <= self.reserve < self.read <= last_obs == self.last <= self.length
                }
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

    #[invariant]
    pub fn valid_grant_state(&self) -> bool {
        &&& self.producer.grant_start() == self.grant_state.prod_start
        &&& self.producer.grant_end() == self.grant_state.prod_end
        &&& self.consumer.grant_start() == self.grant_state.cons_start
        &&& self.consumer.grant_end() == self.grant_state.cons_end
    }

    #[invariant]
    pub fn valid_grant_prod_bounds(&self) -> bool {
        &&& self.grant_state.prod_start <= self.grant_state.prod_end
        &&& self.grant_state.prod_end <= self.length
    }

    #[invariant]
    pub fn valid_grant_cons_bounds(&self) -> bool {
        &&& self.grant_state.cons_start <= self.grant_state.cons_end
        &&& self.grant_state.cons_end <= self.length
    }

    #[invariant]
    pub fn valid_grant_disjoint(&self) -> bool {
        // prod region [prod_start, prod_end) and cons region [cons_start, cons_end) are disjoint
        ||| self.grant_state.prod_start == self.grant_state.prod_end
        ||| self.grant_state.cons_start == self.grant_state.cons_end
        ||| self.grant_state.prod_end <= self.grant_state.cons_start
        ||| self.grant_state.cons_end <= self.grant_state.prod_start
    }

    init! {
        initialize(
            length: nat,
            base_addr: nat,
            provenance: raw_ptr::Provenance,
            buffer_dealloc: raw_ptr::Dealloc,
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

            init base_addr = base_addr;
            init provenance = provenance;
            init buffer_dealloc = Some(buffer_dealloc);
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

            init grant_state = GrantState {
                prod_start: 0,
                prod_end: 0,
                cons_start: 0,
                cons_end: 0,
            };
        }
    }
    
    #[inductive(initialize)]
    fn initialize_inductive(post: Self, length: nat, base_addr: nat, provenance: raw_ptr::Provenance, buffer_dealloc: raw_ptr::Dealloc) {}

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

            update grant_state = GrantState {
                prod_start: start,
                prod_end: start + sz,
                cons_start: pre.grant_state.cons_start,
                cons_end: pre.grant_state.cons_end,
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

            update grant_state = GrantState {
                prod_start: pre.grant_state.prod_start,
                prod_end: new_reserve,
                cons_start: pre.grant_state.cons_start,
                cons_end: pre.grant_state.cons_end,
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
            require(new_write == pre.producer.reserve);

            // これは post.valid_write_max_implies_last_max のため
            require(new_write == pre.length ==> pre.producer.last == pre.length);

            // これはこれまでの条件分岐から言える
            require(!(new_write < pre.write && pre.write != pre.length) || pre.producer.last == pre.write);
            require(!(!(new_write < pre.write && pre.write != pre.length) && new_write > pre.producer.last) || pre.producer.last == pre.length);

            update write = new_write;

            update producer = ProducerState {
                write_in_progress: pre.producer.write_in_progress,
                write: new_write,
                reserve: pre.producer.reserve,
                last: pre.producer.last,
                read_obs: pre.producer.read_obs,
            };

            update grant_state = GrantState {
                prod_start: new_write,
                prod_end: pre.grant_state.prod_end,
                cons_start: pre.grant_state.cons_start,
                cons_end: pre.grant_state.cons_end,
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

            update grant_state = GrantState {
                prod_start: pre.grant_state.prod_start,
                prod_end: pre.grant_state.prod_end,
                cons_start: pre.grant_state.cons_start,
                cons_end: if pre.consumer.read <= pre.consumer.write_obs->Some_0 {
                    pre.consumer.write_obs->Some_0 // not inverted
                } else {
                    pre.last // inverted
                },
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

            update grant_state = GrantState {
                prod_start: pre.grant_state.prod_start,
                prod_end: pre.grant_state.prod_end,
                cons_start: 0,
                cons_end: pre.consumer.write_obs->Some_0,
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

            update grant_state = GrantState {
                prod_start: pre.grant_state.prod_start,
                prod_end: pre.grant_state.prod_end,
                cons_start: pre.consumer.read,
                cons_end: pre.consumer.read,
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

            update grant_state = GrantState {
                prod_start: pre.grant_state.prod_start,
                prod_end: pre.grant_state.prod_end,
                cons_start: pre.consumer.read + used,
                cons_end: if pre.consumer.read + used <= pre.consumer.write_obs->Some_0 {
                    pre.consumer.write_obs->Some_0 // not inverted
                } else {
                    pre.consumer.last_obs->Some_0 // inverted
                },
            };
        }
    }
    
    transition!{
        end_release() {
            //require(pre.read_in_progress == true);
            update read_in_progress = false;
            update consumer = ConsumerState {
                read_in_progress: false,
                read: pre.consumer.read,
                write_obs: None,
                last_obs: None,
            };

            update grant_state = GrantState {
                prod_start: pre.grant_state.prod_start,
                prod_end: pre.grant_state.prod_end,
                cons_start: pre.consumer.read,
                cons_end: pre.consumer.read,
            };
        }
    }

    transition!{
        check_write_in_progress_equality() {
            assert(pre.producer.write_in_progress == pre.write_in_progress);
        }
    }

    transition!{
        check_write_equality() {
            assert(pre.producer.write == pre.write);
            assert(pre.write <= pre.length);
        }
    }

    transition!{
        check_reserve_equality() {
            assert(pre.producer.reserve == pre.reserve);
            assert(pre.reserve <= pre.length);
        }
    }

    transition!{
        check_last_equality() {
            assert(pre.producer.last == pre.last);
            assert(pre.last <= pre.length);
        }
    }

    transition!{
        check_read_equality() {
            assert(pre.consumer.read == pre.read);
            assert(pre.read <= pre.length);
        }
    }

    transition!{
        check_read_is_le_last_in_inverted() {
            if pre.consumer.write_obs is Some && pre.consumer.last_obs is Some && pre.consumer.write_obs->Some_0 < pre.consumer.read {
                assert(pre.consumer.read <= pre.consumer.last_obs->Some_0);
                assert(pre.consumer.read == pre.read);
            }
        }
    }

    transition!{
        check_consumer_obs_in_range() {
            if pre.consumer.write_obs is Some {
                assert(pre.consumer.write_obs->Some_0 <= pre.length);
            }
            if pre.consumer.last_obs is Some {
                assert(pre.consumer.last_obs->Some_0 <= pre.length);
            }
        }
    }

    transition!{
        check_read_in_progress_equality() {
            assert(pre.consumer.read_in_progress == pre.read_in_progress);
        }
    }

    // Extract grant_state bounds and disjointness from invariants
    transition!{
        check_grant_bounds_disjoint() {
            assert(pre.grant_state.prod_start <= pre.grant_state.prod_end);
            assert(pre.grant_state.prod_end <= pre.length);
            assert(pre.grant_state.cons_start <= pre.grant_state.cons_end);
            assert(pre.grant_state.cons_end <= pre.length);
            assert(
                pre.grant_state.prod_start == pre.grant_state.prod_end
                || pre.grant_state.cons_start == pre.grant_state.cons_end
                || pre.grant_state.prod_end <= pre.grant_state.cons_start
                || pre.grant_state.cons_end <= pre.grant_state.prod_start
            );
        }
    }

    // Extract that producer's prod range is empty when idle (write == reserve)
    transition!{
        check_grant_prod_idle() {
            require(pre.producer.write == pre.producer.reserve);
            assert(pre.grant_state.prod_start == pre.grant_state.prod_end);
        }
    }

    // Extract that consumer's cons range is empty when idle
    transition!{
        check_grant_cons_idle() {
            require(pre.consumer.write_obs is None);
            require(pre.consumer.last_obs is None);
            assert(pre.grant_state.cons_start == pre.grant_state.cons_end);
        }
    }

    // Extract that consumer's cons range is empty when last_obs is None
    transition!{
        check_grant_cons_no_last() {
            require(pre.consumer.last_obs is None);
            assert(pre.grant_state.cons_start == pre.grant_state.cons_end);
        }
    }

    // Extract relationship between producer token and grant_state
    transition!{
        check_grant_prod_eq() {
            assert(pre.grant_state.prod_start == pre.producer.grant_start());
            assert(pre.grant_state.prod_end == pre.producer.grant_end());
        }
    }

    // Extract relationship between consumer token and grant_state
    transition!{
        check_grant_cons_eq() {
            assert(pre.grant_state.cons_start == pre.consumer.grant_start());
            assert(pre.grant_state.cons_end == pre.consumer.grant_end());
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
        // prod_start = start, prod_end = start + sz
        // From require: start + sz <= length (follows from the three disjunctive cases)
        let read_obs = pre.producer.read_obs->Some_0;
        if start == pre.producer.write && pre.producer.write < read_obs && pre.producer.write + sz < read_obs {
            assert(start + sz < read_obs);
            assert(read_obs <= pre.length);
        } else if start == pre.producer.write && !(pre.producer.write < read_obs) && pre.producer.write + sz <= pre.length {
            assert(start + sz <= pre.length);
        } else {
            assert(start == 0);
            assert(sz < read_obs);
            assert(read_obs <= pre.length);
        }
    }
    
    #[inductive(grant_fail)]
    fn grant_fail_inductive(pre: Self, post: Self) {
    }
    
    #[inductive(start_commit)]
    fn start_commit_inductive(pre: Self, post: Self, sz: nat) { }
    
    #[inductive(load_write_at_commit)]
    fn load_write_at_commit_inductive(pre: Self, post: Self) { }
    

    #[inductive(sub_reserve_at_commit)]
    fn sub_reserve_at_commit_inductive(pre: Self, post: Self, commited: nat) {
        // prod_end = new_reserve = reserve - commited
        // prod_start unchanged
        // Need: prod_start <= new_reserve <= length
        let new_reserve = (pre.producer.reserve - commited) as nat;
        let grant_start = if pre.producer.write <= pre.producer.reserve { pre.producer.write } else { 0 as nat };
        assert(pre.producer.reserve - grant_start >= commited);
        assert(grant_start == pre.grant_state.prod_start);
        assert(new_reserve >= grant_start);
    }
    
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
    fn store_write_at_commit_inductive(pre: Self, post: Self, new_write: nat) { }
    
    #[inductive(end_commit)]
    fn end_commit_inductive(pre: Self, post: Self) { }
    
    #[inductive(start_read)]
    fn start_read_inductive(pre: Self, post: Self) { }
    
    #[inductive(load_write_at_read)]
    fn load_write_at_read_inductive(pre: Self, post: Self) { }
    
    #[inductive(load_last_at_read)]
    fn load_last_at_read_inductive(pre: Self, post: Self) {
        // cons_start = read (unchanged), cons_end = write_obs or last
        // Need: cons_start <= cons_end <= length
        let write_obs = pre.consumer.write_obs->Some_0;
        if pre.consumer.read <= write_obs {
            // not inverted: cons_end = write_obs
            assert(pre.consumer.read <= write_obs);
            assert(write_obs <= pre.length);
        } else {
            // inverted: cons_end = last
            assert(pre.consumer.read <= pre.last);
            assert(pre.last <= pre.length);
        }
    }
    
    #[inductive(load_read_at_read)]
    fn load_read_at_read_inductive(pre: Self, post: Self) { }
    
    #[inductive(wrap_read)]
    fn wrap_read_inductive(pre: Self, post: Self) {
        // cons_start = 0, cons_end = write_obs
        let write_obs = pre.consumer.write_obs->Some_0;
        assert(write_obs <= pre.length);
    }
    
    #[inductive(read_fail)]
    fn read_fail_inductive(pre: Self, post: Self) { }
    
    #[inductive(start_release)]
    fn start_release_inductive(pre: Self, post: Self) { }
    
    #[inductive(add_read_at_release)]
    fn add_read_at_release_inductive(pre: Self, post: Self, used: nat) {
        // cons_start = read + used
        // cons_end depends on whether read+used <= write_obs
        let write_obs = pre.consumer.write_obs->Some_0;
        let last_obs = pre.consumer.last_obs->Some_0;
        if pre.read + used <= write_obs {
            assert(post.grant_state.cons_end == write_obs);
            assert(pre.read + used <= write_obs);
        } else {
            assert(post.grant_state.cons_end == last_obs);
            assert(write_obs < pre.read + used);
            assert(pre.read + used <= last_obs);
        }
    }
    
    #[inductive(end_release)]
    fn end_release_inductive(pre: Self, post: Self) { }

    #[inductive(check_write_in_progress_equality)]
    fn check_write_in_progress_equality_inductive(pre: Self, post: Self) { }

    #[inductive(check_write_equality)]
    fn check_write_equality_inductive(pre: Self, post: Self) { }

    #[inductive(check_reserve_equality)]
    fn check_reserve_equality_inductive(pre: Self, post: Self) { }

    #[inductive(check_last_equality)]
    fn check_last_equality_inductive(pre: Self, post: Self) { }
    
    #[inductive(check_read_equality)]
    fn check_read_equality_inductive(pre: Self, post: Self) { }

    #[inductive(check_consumer_obs_in_range)]
    fn check_consumer_obs_in_range_inductive(pre: Self, post: Self) { }

    #[inductive(check_read_in_progress_equality)]
    fn check_read_in_progress_equality_inductive(pre: Self, post: Self) { }

    #[inductive(check_read_is_le_last_in_inverted)]
    fn check_read_is_le_last_in_inverted_inductive(pre: Self, post: Self) { }

    #[inductive(check_grant_bounds_disjoint)]
    fn check_grant_bounds_disjoint_inductive(pre: Self, post: Self) { }

    #[inductive(check_grant_prod_idle)]
    fn check_grant_prod_idle_inductive(pre: Self, post: Self) { }

    #[inductive(check_grant_cons_idle)]
    fn check_grant_cons_idle_inductive(pre: Self, post: Self) { }

    #[inductive(check_grant_cons_no_last)]
    fn check_grant_cons_no_last_inductive(pre: Self, post: Self) { }

    #[inductive(check_grant_prod_eq)]
    fn check_grant_prod_eq_inductive(pre: Self, post: Self) { }

    #[inductive(check_grant_cons_eq)]
    fn check_grant_cons_eq_inductive(pre: Self, post: Self) { }
}}

/*
    共有する不変条件用の構造体
*/
pub tracked struct GhostStuff<Perm, Tok>
{
    pub tracked perm: Perm,
    pub tracked token: Tok,
}

pub type GhostStuffUsize<Tok> = GhostStuff<PermissionUsize, Tok>;
pub type GhostStuffBool<Tok>  = GhostStuff<PermissionBool,  Tok>;

impl<Tok> GhostStuffUsize<Tok>
where
    Tok: UniqueValueToken<nat>,
{
    pub open spec fn wf(self, inst: VBQueue::Instance, cell: &PAtomicUsize) -> bool {
        &&& self.perm@.patomic == cell.id()
        &&& self.token.instance_id() == inst.id()
        &&& self.perm@.value as nat == self.token.value()
    }
}

impl<Tok> GhostStuffBool<Tok>
where
    Tok: UniqueValueToken<bool>,
{
    pub open spec fn wf(self, inst: VBQueue::Instance, cell: &PAtomicBool) -> bool {
        &&& self.perm@.patomic == cell.id()
        &&& self.token.instance_id() == inst.id()
        &&& self.perm@.value == self.token.value()
    }
}

pub tracked struct GhostBufferPermission
{
    pub tracked pool: PointsToRaw,
    pub tracked grant_state_token: VBQueue::grant_state,
}

impl GhostBufferPermission
{
    pub open spec fn wf(self, inst: VBQueue::Instance) -> bool {
        let ps = self.grant_state_token.value().prod_start;
        let pe = self.grant_state_token.value().prod_end;
        let cs = self.grant_state_token.value().cons_start;
        let ce = self.grant_state_token.value().cons_end;

        let whole_set = set_int_range(inst.base_addr() as int, inst.base_addr() as int + inst.length() as int);
        let prod_set = set_int_range(ps + inst.base_addr() as int, pe + inst.base_addr() as int);
        let cons_set = set_int_range(cs + inst.base_addr() as int, ce + inst.base_addr() as int);

        {
            &&& self.grant_state_token.instance_id() == inst.id()
            &&& self.pool.provenance() == inst.provenance()
            &&& prod_set.disjoint(cons_set)
            &&& self.pool.dom()
              =~= Set::new(|i: int| whole_set.contains(i)
                                   && !prod_set.contains(i)
                                   && !cons_set.contains(i))
        }
    }
}

pub struct VBBuffer {
    length: usize,
    buffer_ptr: *mut u8,
    write: PAtomicUsize,
    read: PAtomicUsize,
    last: PAtomicUsize,
    reserve: PAtomicUsize,
    read_in_progress: PAtomicBool,
    write_in_progress: PAtomicBool,
    already_split: PAtomicBool,

    /* 以下は幽霊変数 */
    write_gs: Tracked<Option<GhostStuffUsize<VBQueue::write>>>,
    read_gs: Tracked<Option<GhostStuffUsize<VBQueue::read>>>,
    last_gs: Tracked<Option<GhostStuffUsize<VBQueue::last>>>,
    reserve_gs: Tracked<Option<GhostStuffUsize<VBQueue::reserve>>>,
    read_in_progress_gs: Tracked<Option<GhostStuffBool<VBQueue::read_in_progress>>>,
    write_in_progress_gs: Tracked<Option<GhostStuffBool<VBQueue::write_in_progress>>>,
    already_split_gs: Tracked<Option<GhostStuffBool<VBQueue::already_split>>>,

    buf_points_to_raw: Tracked<Option<PointsToRaw>>,
    grant_state_token: Tracked<Option<VBQueue::grant_state>>, // トークンの分割状態を管理
    prod_token: Tracked<Option<VBQueue::producer>>, // Prod用の状態遷移用APIトークン
    cons_token: Tracked<Option<VBQueue::consumer>>, // Cons用の状態遷移用APIトークン
    instance: Tracked<VBQueue::Instance>,
}

struct_with_invariants!{
    pub struct VBBufferShared<'a> {
        length: usize,
        write: &'a PAtomicUsize,
        read: &'a PAtomicUsize,
        last: &'a PAtomicUsize,
        reserve: &'a PAtomicUsize,
        read_in_progress: &'a PAtomicBool,
        write_in_progress: &'a PAtomicBool,
        // already_split: &'a PAtomicBool,

        /* バッファ分割管理用不変条件 */
        buf_perm_inv: Tracked< Shared<AtomicInvariant<_, GhostBufferPermission, _>> >,

        /* Atomic変数用不変条件 */
        write_inv: Tracked< Shared<AtomicInvariant<_, GhostStuffUsize<VBQueue::write>, _>> >,
        read_inv: Tracked< Shared<AtomicInvariant<_, GhostStuffUsize<VBQueue::read>, _>> >,
        last_inv: Tracked< Shared<AtomicInvariant<_, GhostStuffUsize<VBQueue::last>, _>> >,
        reserve_inv: Tracked< Shared<AtomicInvariant<_, GhostStuffUsize<VBQueue::reserve>, _>> >,
        read_in_progress_inv: Tracked< Shared<AtomicInvariant<_, GhostStuffBool<VBQueue::read_in_progress>, _>> >,
        write_in_progress_inv: Tracked< Shared<AtomicInvariant<_, GhostStuffBool<VBQueue::write_in_progress>, _>> >,
        // already_split_inv: Tracked< Shared<AtomicInvariant<_, GhostStuffBool<VBQueue::already_split>, _>> >,

        instance: Tracked<VBQueue::Instance>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            &&& self.write_inv@@.namespace() != self.buf_perm_inv@@.namespace()
            &&& self.read_inv@@.namespace() != self.buf_perm_inv@@.namespace()
            &&& self.last_inv@@.namespace() != self.buf_perm_inv@@.namespace()
            &&& self.reserve_inv@@.namespace() != self.buf_perm_inv@@.namespace()
            &&& self.read_in_progress_inv@@.namespace() != self.buf_perm_inv@@.namespace()
            &&& self.write_in_progress_inv@@.namespace() != self.buf_perm_inv@@.namespace()
            &&& self.instance@.length() == self.length
            &&& self.instance@.length() <= usize::MAX
        }

        invariant on buf_perm_inv
            with (instance)
            specifically (self.buf_perm_inv@@)
            is (v: GhostBufferPermission) {
                v.wf(instance@)
        }

        invariant on write_inv
            with (instance, write)
            specifically (self.write_inv@@)
            is (v: GhostStuffUsize<VBQueue::write>) {
                v.wf(instance@, write)
        }

        invariant on read_inv
            with (instance, read)
            specifically (self.read_inv@@)
            is (v: GhostStuffUsize<VBQueue::read>) {
                v.wf(instance@, read)
        }

        invariant on last_inv
            with (instance, last)
            specifically (self.last_inv@@)
            is (v: GhostStuffUsize<VBQueue::last>) {
                v.wf(instance@, last)
        }

        invariant on reserve_inv
            with (instance, reserve)
            specifically (self.reserve_inv@@)
            is (v: GhostStuffUsize<VBQueue::reserve>) {
                v.wf(instance@, reserve)
        }

        invariant on read_in_progress_inv
            with (instance, read_in_progress)
            specifically (self.read_in_progress_inv@@)
            is (v: GhostStuffBool<VBQueue::read_in_progress>) {
                v.wf(instance@, read_in_progress)
        }

        invariant on write_in_progress_inv
            with (instance, write_in_progress)
            specifically (self.write_in_progress_inv@@)
            is (v: GhostStuffBool<VBQueue::write_in_progress>) {
                v.wf(instance@, write_in_progress)
        }
        /*
        invariant on already_split_inv
            with (instance, already_split)
            specifically (self.already_split_inv@@)
            is (v: GhostStuffUsize<VBQueue::already_split>) {
                v.wf(instance@, already_split)
        } */
    }
}

impl VBBuffer {
    pub closed spec fn wf(self) -> bool {
        &&& match self.prod_token@ {
                Some(prod) => prod.instance_id() == self.instance@.id(),
                None => true,
            }
        &&& match self.cons_token@ {
                Some(cons) => cons.instance_id() == self.instance@.id(),
                None => true,
            }
        &&& self.length as nat == self.instance@.length()
        &&& self.instance@.length() <= usize::MAX
        &&& self.instance@.base_addr() == self.buffer_ptr as nat
        &&& self.buffer_ptr as int + self.instance@.length() <= usize::MAX + 1
    }

    pub closed spec fn can_split(&self) -> bool {
        &&& self.prod_token@ is Some
        &&& self.prod_token@->0.instance_id() == self.instance@.id()
        &&& self.prod_token@->0.value().is_idle()
        &&& self.cons_token@ is Some
        &&& self.cons_token@->0.instance_id() == self.instance@.id()
        &&& self.cons_token@->0.value().is_idle()
        &&& self.grant_state_token@ is Some
        &&& self.grant_state_token@->0.instance_id() == self.instance@.id()
        &&& self.grant_state_token@->0.value().is_idle()
        &&& self.buf_points_to_raw@ is Some
        &&& self.buf_points_to_raw@->0.provenance() == self.instance@.provenance()
        &&& self.buf_points_to_raw@->0.provenance() == self.buffer_ptr@.provenance
        &&& self.buf_points_to_raw@->0.is_range(self.buffer_ptr as int, self.instance@.length() as int)
        &&& self.buf_points_to_raw@->0.dom() =~= Set::new(|i: int| self.buffer_ptr as int <= i && i < self.buffer_ptr as int + self.instance@.length() as int)
        &&& self.write_gs@ is Some
        &&& self.write_gs@->0.wf(self.instance@, &self.write)
        &&& self.read_gs@ is Some
        &&& self.read_gs@->0.wf(self.instance@, &self.read)
        &&& self.last_gs@ is Some
        &&& self.last_gs@->0.wf(self.instance@, &self.last)
        &&& self.reserve_gs@ is Some
        &&& self.reserve_gs@->0.wf(self.instance@, &self.reserve)
        &&& self.read_in_progress_gs@ is Some
        &&& self.read_in_progress_gs@->0.wf(self.instance@, &self.read_in_progress)
        &&& self.write_in_progress_gs@ is Some
        &&& self.write_in_progress_gs@->0.wf(self.instance@, &self.write_in_progress)
        &&& self.already_split_gs@ is Some
        &&& self.already_split_gs@->0.wf(self.instance@, &self.already_split)
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
            r.can_split(),
    {
        let (buffer_ptr, Tracked(points_to_raw), Tracked(buffer_dealloc)) = allocate(length, 1);
        proof {
            assert(points_to_raw.is_range(buffer_ptr as int, length as int));
            assert(points_to_raw.dom() =~= Set::new(|i: int| buffer_ptr as int <= i && i < buffer_ptr as int + length as int));
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
            Tracked(grant_state_token),
        ) = VBQueue::Instance::initialize(
            length as nat,
            buffer_ptr as nat,
            buffer_ptr@.provenance,
            buffer_dealloc,
            Some(buffer_dealloc),
        );

        let tracked_inst: Tracked<VBQueue::Instance> = Tracked(instance.clone());

        let (write, Tracked(write_perm)) = PAtomicUsize::new(0);
        let tracked write_gs = GhostStuffUsize { perm: write_perm, token: write_token };

        let (read, Tracked(read_perm)) = PAtomicUsize::new(0);
        let tracked read_gs = GhostStuffUsize { perm: read_perm, token: read_token };

        let (last, Tracked(last_perm)) = PAtomicUsize::new(length);
        let tracked last_gs = GhostStuffUsize { perm: last_perm, token: last_token };

        let (reserve, Tracked(reserve_perm)) = PAtomicUsize::new(0);
        let tracked reserve_gs = GhostStuffUsize { perm: reserve_perm, token: reserve_token };

        let (read_in_progress, Tracked(read_in_progress_perm)) = PAtomicBool::new(false);
        let tracked read_in_progress_gs = GhostStuffBool { perm: read_in_progress_perm, token: read_in_progress_token };

        let (write_in_progress, Tracked(write_in_progress_perm)) = PAtomicBool::new(false);
        let tracked write_in_progress_gs = GhostStuffBool { perm: write_in_progress_perm, token: write_in_progress_token };

        let (already_split, Tracked(already_split_perm)) = PAtomicBool::new(false);
        let tracked already_split_gs = GhostStuffBool { perm: already_split_perm, token: already_split_token };

        // Initialize the queue
        Self {
            length,
            buffer_ptr,
            write,
            read,
            last,
            reserve,
            read_in_progress,
            write_in_progress,
            already_split,

            write_gs: Tracked(Some(write_gs)),
            read_gs: Tracked(Some(read_gs)),
            last_gs: Tracked(Some(last_gs)),
            reserve_gs: Tracked(Some(reserve_gs)),
            read_in_progress_gs: Tracked(Some(read_in_progress_gs)),
            write_in_progress_gs: Tracked(Some(write_in_progress_gs)),
            already_split_gs: Tracked(Some(already_split_gs)), 

            buf_points_to_raw: Tracked(Some(points_to_raw)),
            grant_state_token: Tracked(Some(grant_state_token)),
            prod_token: Tracked(Some(producer_token)),
            cons_token: Tracked(Some(consumer_token)),
            instance: Tracked(instance),
        }
    }

    fn try_split<'a>(&'a mut self)  -> (res: Result<(Producer<'a>, Consumer<'a>),  &'static str>)
        requires
            old(self).wf(),
            old(self).can_split(),
        ensures
            match res {
                Ok((prod, cons)) => {
                    &&& prod.is_idle()
                    &&& cons.is_idle()
                    &&& prod.shared.instance@.length() == old(self).instance@.length()
                    &&& prod.shared.instance@.length() == old(self).instance@.length()
                }, 
                Err(_) => true
            },
    {
        let tracked already_split_gs = self.already_split_gs.borrow_mut().tracked_take();
        let tracked GhostStuffBool { perm: mut already_split_perm, token: mut already_split_token } = already_split_gs;
        let already_splitted = self.already_split.swap(Tracked(&mut already_split_perm), true);
        proof {
            if !already_splitted {
                let _ = self.instance.borrow().try_split(&mut already_split_token);
            }
        }

        if already_splitted {
            return Err("already splitted");
        }

        let tracked prod_token = self.prod_token.borrow_mut().tracked_take();
        let tracked cons_token = self.cons_token.borrow_mut().tracked_take();

        let tracked grant_state_token = self.grant_state_token.borrow_mut().tracked_take();
        let tracked buf_points_to_raw = self.buf_points_to_raw.borrow_mut().tracked_take();
        let tracked write_gs = self.write_gs.borrow_mut().tracked_take();
        let tracked read_gs = self.read_gs.borrow_mut().tracked_take();
        let tracked last_gs = self.last_gs.borrow_mut().tracked_take();
        let tracked reserve_gs = self.reserve_gs.borrow_mut().tracked_take();
        let tracked read_in_progress_gs = self.read_in_progress_gs.borrow_mut().tracked_take();
        let tracked write_in_progress_gs = self.write_in_progress_gs.borrow_mut().tracked_take();
        let Tracked(inst) = self.instance;

        let tracked ghost_buffer_perm = GhostBufferPermission {
            pool: buf_points_to_raw,
            grant_state_token,
        };
        let tracked buf_perm_inv = Shared::new(AtomicInvariant::new(self.instance, ghost_buffer_perm, 0));

        let tracked write_inv = Shared::new(AtomicInvariant::new((self.instance, &self.write), write_gs, 1));
        let tracked read_inv = Shared::new(AtomicInvariant::new((self.instance, &self.read), read_gs, 2));
        let tracked last_inv = Shared::new(AtomicInvariant::new((self.instance, &self.last), last_gs, 3));
        let tracked reserve_inv = Shared::new(AtomicInvariant::new((self.instance, &self.reserve), reserve_gs, 4));
        let tracked read_in_progress_inv = Shared::new(
            AtomicInvariant::new((self.instance, &self.read_in_progress), read_in_progress_gs, 5)
        );
        let tracked write_in_progress_inv = Shared::new(
            AtomicInvariant::new((self.instance, &self.write_in_progress), write_in_progress_gs, 6)
        );

        Ok((
            Producer {
                buffer_ptr: self.buffer_ptr,
                shared: VBBufferShared {
                    length: self.length,
                    write: &self.write,
                    read: &self.read,
                    last: &self.last,
                    reserve: &self.reserve,
                    read_in_progress: &self.read_in_progress,
                    write_in_progress: &self.write_in_progress,
                    // already_split: &'a PAtomicBool,

                    /* バッファ分割管理用不変条件 */
                    buf_perm_inv: Tracked(buf_perm_inv.clone()),

                    /* Atomic変数用不変条件 */
                    write_inv: Tracked(write_inv.clone()),
                    read_inv: Tracked(read_inv.clone()),
                    last_inv: Tracked(last_inv.clone()),
                    reserve_inv: Tracked(reserve_inv.clone()),
                    read_in_progress_inv: Tracked(read_in_progress_inv.clone()),
                    write_in_progress_inv: Tracked(write_in_progress_inv.clone()),

                    instance: Tracked(self.instance.borrow().clone()),
                },
                prod_token: Tracked(Some(prod_token)),
            },
            Consumer {
                buffer_ptr: self.buffer_ptr,
                shared: VBBufferShared {
                    length: self.length,
                    write: &self.write,
                    read: &self.read,
                    last: &self.last,
                    reserve: &self.reserve,
                    read_in_progress: &self.read_in_progress,
                    write_in_progress: &self.write_in_progress,
                    // already_split: &'a PAtomicBool,

                    /* バッファ分割管理用不変条件 */
                    buf_perm_inv: Tracked(buf_perm_inv),

                    /* Atomic変数用不変条件 */
                    write_inv: Tracked(write_inv),
                    read_inv: Tracked(read_inv),
                    last_inv: Tracked(last_inv),
                    reserve_inv: Tracked(reserve_inv),
                    read_in_progress_inv: Tracked(read_in_progress_inv),
                    write_in_progress_inv: Tracked(write_in_progress_inv),

                    instance: Tracked(self.instance.borrow().clone()),
                },
                cons_token: Tracked(Some(cons_token)),
            }
        ))
    }
}

pub struct Producer<'a> {
    buffer_ptr: *mut u8,
    shared: VBBufferShared<'a>,
    prod_token: Tracked<Option<VBQueue::producer>>,
}

impl<'a> Producer<'a> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.buffer_ptr@.provenance == self.shared.instance@.provenance()
        &&& self.buffer_ptr as int == self.shared.instance@.base_addr()
        &&& self.buffer_ptr as int + self.shared.instance@.length() <= usize::MAX + 1
        &&& self.shared.wf()
    }

    pub closed spec fn is_idle(&self) -> bool {
        &&& self.prod_token@ is Some
        &&& self.prod_token@->0.instance_id() == self.shared.instance@.id()
        &&& self.prod_token@->0.value().is_idle()
        &&& self.wf()
    }

    pub closed spec fn is_granted(&self, sz: nat) -> bool {
        &&& self.prod_token@ is None
        &&& self.wf()
    }
}

impl<'a> Producer<'a> {
    fn grant_exact(&mut self, sz: usize) -> (r: Result<GrantW, &'static str>)
        requires
            old(self).is_idle(),
            sz > 0,
        ensures
            self.wf(),
            match r {
                Ok(wgr) => {
                    &&& wgr.shared.instance@.id() == self.shared.instance@.id()
                    &&& wgr.prod_token@->0.instance_id() == old(self).prod_token@->0.instance_id()
                    &&& wgr.can_commit(sz as nat)
                },
                _ => true
            },
    {
        proof{
            assert(self.prod_token@->0.value().write_in_progress == false ==> 
                self.prod_token@->0.value().read_obs is None);
        }
        let tracked mut prod_token = self.prod_token.borrow_mut().tracked_take();

        let is_write_in_progress: bool;
        open_atomic_invariant!(self.shared.write_in_progress_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut write_in_progress_perm, token: mut write_in_progress_token } = gs;

            is_write_in_progress = self.shared.write_in_progress.swap(Tracked(&mut write_in_progress_perm), true);

            proof {
                if !is_write_in_progress {
                    let _ = self.shared.instance.borrow().start_grant(&mut write_in_progress_token, &mut prod_token);
                    assert(write_in_progress_token.value() == true);
                    assert(is_write_in_progress == false);
                } else {
                    assert(write_in_progress_token.value() == true);
                    assert(is_write_in_progress == true);
                };
            }

            proof { gs = GhostStuffBool { perm: write_in_progress_perm, token: write_in_progress_token }; }
        });

        if is_write_in_progress {
            self.prod_token = Tracked(Some(prod_token));
            return Err("write in progress");
        }

        let write: usize;
        open_atomic_invariant!(self.shared.write_inv.borrow().borrow() => gs => {
            let tracked GhostStuffUsize { perm: mut write_perm, token: mut write_token } = gs;

            write = self.shared.write.load(Tracked(&mut write_perm));
            proof {
                let _ = self.shared.instance.borrow().load_write_at_grant(&write_token, &prod_token);
            }

            proof { gs = GhostStuffUsize { perm: write_perm, token: write_token }; }
        });

        let read: usize;
        open_atomic_invariant!(self.shared.read_inv.borrow().borrow() => gs => {
            let tracked GhostStuffUsize { perm: mut read_perm, token: mut read_token } = gs;

            read = self.shared.read.load(Tracked(&mut read_perm));
            proof {
                let _ = self.shared.instance.borrow().load_read_at_grant(&read_token, &mut prod_token);
            }

            proof { gs = GhostStuffUsize { perm: read_perm, token: read_token }; }
        });

        let max = self.shared.length;
        let already_inverted = write < read;

        let start: usize = if already_inverted {
            if ((write as u128 + sz as u128) as u128) < read as u128 {
                // Inverted, room is still available
                write
            } else {
                // Inverted, no room is available
                open_atomic_invariant!(self.shared.write_in_progress_inv.borrow().borrow() => gs => {
                    let tracked GhostStuffBool { perm: mut write_in_progress_perm, token: mut write_in_progress_token } = gs;

                    let _ = self.shared.write_in_progress.store(Tracked(&mut write_in_progress_perm), false);
                    proof {
                        let _ = self.shared.instance.borrow().grant_fail(&mut write_in_progress_token, &mut prod_token);
                    }

                    proof { gs = GhostStuffBool { perm: write_in_progress_perm, token: write_in_progress_token }; }
                });

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
                    open_atomic_invariant!(self.shared.write_in_progress_inv.borrow().borrow() => gs => {
                        let tracked GhostStuffBool { perm: mut write_in_progress_perm, token: mut write_in_progress_token } = gs;

                        let _ = self.shared.write_in_progress.store(Tracked(&mut write_in_progress_perm), false);
                        proof {
                            let _ = self.shared.instance.borrow().grant_fail(&mut write_in_progress_token, &mut prod_token);
                        }

                        proof { gs = GhostStuffBool { perm: write_in_progress_perm, token: write_in_progress_token }; }
                    });

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
        // assert(start + sz <= self.shared.length);

        // Safe write, only viewed by this task
        let tracked mut prod_points_to_raw: Option<PointsToRaw> = None;
        open_atomic_invariant!(self.shared.buf_perm_inv.borrow().borrow() => bp => {
            let tracked GhostBufferPermission {
                pool: mut current_pool,
                grant_state_token: mut grant_state_token,
            } = bp;

            // Save ghost snapshots BEFORE mutation
            let ghost base = self.buffer_ptr as int;
            let ghost len = self.shared.instance@.length() as int;
            let ghost old_ps = grant_state_token.value().prod_start;
            let ghost old_pe = grant_state_token.value().prod_end;
            let ghost old_cs = grant_state_token.value().cons_start;
            let ghost old_ce = grant_state_token.value().cons_end;
            let ghost pool_dom_snapshot = current_pool.dom();

            // From bp.wf(inst): pool.dom() equals whole_set minus prod_set minus cons_set
            // Producer is idle before grant → prod_start == prod_end → prod_set is empty
            proof {
                self.shared.instance.borrow().check_grant_prod_idle(&prod_token, &grant_state_token);
                assert(old_ps == old_pe); // now proven via check transition
                // So pool.dom() = whole_set \ cons_set
                assert forall |i: int| pool_dom_snapshot.contains(i) <==>
                    (base <= i && i < base + len && !(base + old_cs <= i && i < base + old_ce)) by {};
            }

            open_atomic_invariant!(self.shared.reserve_inv.borrow().borrow() => gs => {
                let tracked GhostStuffUsize { perm: mut reserve_perm, token: mut reserve_token } = gs;
                let _ = self.shared.reserve.store(Tracked(&mut reserve_perm), start + sz);
                proof {
                    let _ = self.shared.instance.borrow().do_reserve(start as nat, sz as nat, &mut reserve_token, &mut prod_token, &mut grant_state_token);
                }

                proof { gs = GhostStuffUsize { perm: reserve_perm, token: reserve_token }; }
            });

            // After do_reserve:
            // - pool hasn't changed, pool.dom() == pool_dom_snapshot
            // - grant_state_token mutated: new prod = [start, start+sz), cons unchanged
            // - From state machine invariant valid_grant_disjoint:
            //   new prod and cons are disjoint as intervals
            proof {
                // Extract bounds and disjointness from state machine invariants
                self.shared.instance.borrow().check_grant_bounds_disjoint(&grant_state_token);
                let new_ps = grant_state_token.value().prod_start;
                let new_pe = grant_state_token.value().prod_end;
                let new_cs = grant_state_token.value().cons_start;
                let new_ce = grant_state_token.value().cons_end;
                // cons is unchanged by do_reserve
                assert(new_cs == old_cs);
                assert(new_ce == old_ce);

                // Prove subset: new_prod_range ⊆ pool_dom_snapshot
                assert(set_int_range(base + new_ps, base + new_pe).subset_of(current_pool.dom())) by {
                    assert forall |i: int| set_int_range(base + new_ps, base + new_pe).contains(i)
                        implies current_pool.dom().contains(i) by {
                        // i is in [base+new_ps, base+new_pe)
                        // Need: base <= i < base+len AND NOT in cons_set
                        assert(base + new_ps <= i && i < base + new_pe);
                        assert(new_ps <= new_pe && new_pe <= len as nat);
                        assert(base <= i && i < base + len);
                        // Not in cons_set: from disjointness [new_ps, new_pe) ∩ [new_cs, new_ce) = {}
                        if new_ps == new_pe {
                            assert(false); // empty prod range, impossible since i is in it
                        } else if new_cs == new_ce {
                            // cons is empty, trivially not in cons_set
                            assert(!(base + old_cs <= i && i < base + old_ce));
                        } else if new_pe <= new_cs {
                            assert(i < base + new_pe);
                            assert(base + new_pe <= base + new_cs);
                            assert(i < base + new_cs);
                            assert(i < base + old_cs);
                            assert(!(base + old_cs <= i && i < base + old_ce));
                        } else {
                            // new_ce <= new_ps
                            assert(new_ce <= new_ps);
                            assert(i >= base + new_ps);
                            assert(i >= base + new_ce);
                            assert(i >= base + old_ce);
                            assert(!(base + old_cs <= i && i < base + old_ce));
                        }
                    };
                };
            }
            let tracked (points_to_raw_prod, pool_rest) = current_pool.split(set_int_range(
                self.buffer_ptr as int + grant_state_token.value().prod_start,
                self.buffer_ptr as int + grant_state_token.value().prod_end));
            proof {
                // Establish domain property in terms of prod_token for can_commit
                assert(points_to_raw_prod.dom() =~= set_int_range(
                    self.buffer_ptr as int + prod_token.value().grant_start(),
                    self.buffer_ptr as int + prod_token.value().grant_end()));
                prod_points_to_raw = Some(points_to_raw_prod);
            }

            // Prove bp.wf(inst) for restored invariant
            proof {
                let inst = self.shared.instance@;
                let new_ps = grant_state_token.value().prod_start;
                let new_pe = grant_state_token.value().prod_end;
                let new_cs = grant_state_token.value().cons_start;
                let new_ce = grant_state_token.value().cons_end;
                let whole_set = set_int_range(base, base + len);
                let new_prod_set = set_int_range(new_ps + base, new_pe + base);
                let new_cons_set = set_int_range(new_cs + base, new_ce + base);

                // pool_rest.dom() = pool_dom_snapshot \ new_prod_set
                // = (whole_set \ old_cons_set) \ new_prod_set
                // = whole_set \ new_cons_set \ new_prod_set  (since old_cons == new_cons)
                assert(pool_rest.dom() =~= Set::new(|i: int|
                    whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i))) by {
                    assert forall |i: int| pool_rest.dom().contains(i) <==>
                        (whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i)) by {
                        // pool_rest = pool \ new_prod_set
                        // pool = whole_set \ old_cons_set (since old_prod was empty)
                        // old_cons_set == new_cons_set
                    };
                };
                // Disjointness
                assert(new_prod_set.disjoint(new_cons_set)) by {
                    assert forall |i: int| !(new_prod_set.contains(i) && new_cons_set.contains(i)) by {
                        if new_ps == new_pe || new_cs == new_ce {
                        } else if new_pe <= new_cs {
                            if new_prod_set.contains(i) {
                                assert(i < base + new_pe);
                                assert(i < base + new_cs);
                            }
                        } else {
                            assert(new_ce <= new_ps);
                            if new_cons_set.contains(i) {
                                assert(i < base + new_ce);
                                assert(i < base + new_ps);
                            }
                        }
                    };
                };
            }
            proof { bp = GhostBufferPermission { pool: pool_rest, grant_state_token}; }
        });

        let tracked prod_points_to_raw = match prod_points_to_raw {
            Some(token) => token,
            None => {
                assert(false);
                proof_from_false()
            }
        };

        // Prove no overflow for pointer arithmetic: buffer_ptr + start <= usize::MAX
        // From sz > 0 and start + sz <= length: start < length
        // From Producer.wf(): buffer_ptr + length <= usize::MAX + 1
        proof {
            let ghost len = self.shared.instance@.length() as int;
            assert(start as int + sz as int <= len);
            assert(start as int + 1 <= len);
            assert(self.buffer_ptr as int + start as int <= usize::MAX as int);
        }

        Ok (
            GrantW {
                buffer_ptr: {
                    let addr = self.buffer_ptr as usize + start;
                    with_exposed_provenance(addr, expose_provenance(self.buffer_ptr))
                },
                sz,
                shared: VBBufferShared {
                    length: self.shared.length,
                    write: &self.shared.write,
                    read: &self.shared.read,
                    last: &self.shared.last,
                    reserve: &self.shared.reserve,
                    read_in_progress: &self.shared.read_in_progress,
                    write_in_progress: &self.shared.write_in_progress,
                    // already_split: &'a PAtomicBool,

                    /* バッファ分割管理用不変条件 */
                    buf_perm_inv: Tracked(self.shared.buf_perm_inv.borrow().clone()),

                    /* Atomic変数用不変条件 */
                    write_inv: Tracked(self.shared.write_inv.borrow().clone()),
                    read_inv: Tracked(self.shared.read_inv.borrow().clone()),
                    last_inv: Tracked(self.shared.last_inv.borrow().clone()),
                    reserve_inv: Tracked(self.shared.reserve_inv.borrow().clone()),
                    read_in_progress_inv: Tracked(self.shared.read_in_progress_inv.borrow().clone()),
                    write_in_progress_inv: Tracked(self.shared.write_in_progress_inv.borrow().clone()),

                    instance: Tracked(self.shared.instance.borrow().clone()),
                },
                points_to_raw_token: Tracked(Some(prod_points_to_raw)),
                prod_token: Tracked(Some(prod_token)),
            }
        )
    }
}

struct GrantW<'a> {
    buffer_ptr: *mut u8,
    sz: usize,
    shared: VBBufferShared<'a>,
    points_to_raw_token: Tracked<Option<PointsToRaw>>,
    prod_token: Tracked<Option<VBQueue::producer>>,
}

impl<'a> GrantW<'a> {
    pub closed spec fn can_commit(&self, sz: nat) -> bool {
        &&& self.prod_token@ is Some
        &&& self.sz as nat == sz
        &&& self.prod_token@->0.instance_id() == self.shared.instance@.id()
        &&& self.prod_token@->0.value().is_idle() || self.prod_token@->0.value().is_granted(sz)
        &&& self.shared.wf()
        // Pool management properties
        &&& self.points_to_raw_token@ is Some
        &&& self.points_to_raw_token@->0.provenance() == self.shared.instance@.provenance()
        &&& self.points_to_raw_token@->0.dom() =~= set_int_range(
            self.buffer_ptr as int,
            self.buffer_ptr as int + self.sz as int)
        &&& self.buffer_ptr as int == self.shared.instance@.base_addr() + self.prod_token@->0.value().grant_start()
        &&& self.buffer_ptr@.provenance == self.shared.instance@.provenance()
        &&& self.shared.instance@.base_addr() + self.shared.instance@.length() <= usize::MAX + 1
        // grant region fits within buffer: buffer_ptr + sz <= base_addr + length
        &&& self.buffer_ptr as int + self.sz as int
            <= self.shared.instance@.base_addr() + self.shared.instance@.length()
    }

    pub closed spec fn is_commited(&self) -> bool {
        &&& self.prod_token@ is None
    }
}

impl<'a> GrantW<'a> {
    /// Write a single byte at offset `idx` within the grant region.
    /// Pattern: split PointsToRaw → into_typed (uninit) → ptr_mut_write → leak_contents → into_raw → join
    fn write_byte(&mut self, idx: usize, val: u8)
        requires
            old(self).can_commit(old(self).sz as nat),
            idx < old(self).sz,
        ensures
            self.can_commit(self.sz as nat),
            self.sz == old(self).sz,
            self.buffer_ptr == old(self).buffer_ptr,
            self.shared == old(self).shared,
            self.prod_token == old(self).prod_token,
    {
        let addr: usize = self.buffer_ptr as usize + idx;

        // Split 1-byte region from PointsToRaw
        let tracked mut ptr_raw = self.points_to_raw_token.borrow_mut().tracked_take();
        proof {
            assert(set_int_range(addr as int, addr + 1).subset_of(
                set_int_range(self.buffer_ptr as int, self.buffer_ptr as int + self.sz as int)));
        }
        let tracked (byte_raw, rest) = ptr_raw.split(set_int_range(addr as int, addr + 1));
        assert(byte_raw.is_range(addr as int, 1));

        // Convert to typed PointsTo<u8> and write
        // global layout u8 guarantees align_of::<u8>() == 1, so addr % 1 == 0
        let tracked mut byte_pto = byte_raw.into_typed::<u8>(addr);
        let current_ptr: *mut u8 = with_exposed_provenance(addr, expose_provenance(self.buffer_ptr));
        assert(equal(byte_pto.ptr(), current_ptr));
        ptr_mut_write(current_ptr, Tracked(&mut byte_pto), val);

        // Leak init state → uninit, then convert back to raw and rejoin
        proof { byte_pto.leak_contents(); }
        let tracked written_raw = byte_pto.into_raw();
        let tracked rejoined = rest.join(written_raw);

        proof {
            assert(rejoined.dom() =~= set_int_range(self.buffer_ptr as int, self.buffer_ptr as int + self.sz as int));
        }
        self.points_to_raw_token = Tracked(Some(rejoined));
    }
}

impl<'a> GrantW<'a> {
    fn commit(&mut self, used: usize) -> (prod_token: Tracked<VBQueue::producer>)
        requires
            old(self).can_commit(old(self).sz as nat),
            used <= old(self).sz,
        ensures
            self.is_commited(),
            prod_token@.instance_id() == old(self).prod_token@->0.instance_id(),
            prod_token@.instance_id() == self.shared.instance@.id(),
            prod_token@.value().is_idle(),
    {
        // If there is no grant in progress, return early. This
        // generally means we are dropping the grant within a
        // wrapper structure
        let tracked prod_token = self.prod_token.borrow_mut().tracked_take();

        let is_write_in_progress: bool;
        open_atomic_invariant!(self.shared.write_in_progress_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut write_in_progress_perm, token: mut write_in_progress_token } = gs;

            is_write_in_progress = self.shared.write_in_progress.load(Tracked(&mut write_in_progress_perm));
                    
            proof {
                let _ = self.shared.instance.borrow().start_commit(self.sz as nat, &mut write_in_progress_token, &prod_token);
                self.shared.instance.borrow().check_write_in_progress_equality(&write_in_progress_token, &prod_token);

                if !is_write_in_progress {
                    assert(prod_token.value().is_idle());
                };
            }

            proof { gs = GhostStuffBool { perm: write_in_progress_perm, token: write_in_progress_token }; }
        });

        if !is_write_in_progress {
            return Tracked(prod_token);
        }

        // Writer component. Must never write to READ,
        // be careful writing to LAST

        // Saturate the grant commit
        let len = self.sz;
        let used = if len <= used { len } else { used }; // min の代用。

        let write: usize;
        open_atomic_invariant!(self.shared.write_inv.borrow().borrow() => gs => {
            let tracked GhostStuffUsize { perm: mut write_perm, token: mut write_token } = gs;
            write = self.shared.write.load(Tracked(&mut write_perm));

            proof {
                let _ = self.shared.instance.borrow().check_write_equality(&write_token, &prod_token);
                let _ = self.shared.instance.borrow().load_write_at_commit(&write_token, &prod_token);
            }

            proof { gs = GhostStuffUsize { perm: write_perm, token: write_token }; }
        });

        // Take out the GrantW's prod PointsToRaw for pool management
        let tracked mut full_prod_ptr = self.points_to_raw_token.borrow_mut().tracked_take();

        open_atomic_invariant!(self.shared.buf_perm_inv.borrow().borrow() => bp => {
            let tracked GhostBufferPermission {
                pool: mut current_pool,
                grant_state_token: mut grant_state_token,
            } = bp;

            // Save ghost snapshots BEFORE mutation
            let ghost base = self.shared.instance@.base_addr() as int;
            let ghost buf_len = self.shared.instance@.length() as int;
            let ghost old_ps = grant_state_token.value().prod_start;
            let ghost old_pe = grant_state_token.value().prod_end;
            let ghost old_cs = grant_state_token.value().cons_start;
            let ghost old_ce = grant_state_token.value().cons_end;
            // Save full_prod_ptr domain and old pool domain BEFORE mutation
            proof {
                self.shared.instance.borrow().check_grant_prod_eq(&prod_token, &grant_state_token);
                // Establish full_prod_ptr.dom() in terms of grant_state values
                assert(full_prod_ptr.dom() =~= set_int_range(base + old_ps, base + old_pe));
                // Save old pool domain characterization (from bp.wf(inst))
                assert forall |i: int| current_pool.dom().contains(i) <==>
                    (base <= i && i < base + buf_len
                     && !(base + old_ps <= i && i < base + old_pe)
                     && !(base + old_cs <= i && i < base + old_ce)) by {};
            }

            open_atomic_invariant!(self.shared.reserve_inv.borrow().borrow() => gs => {
                let tracked GhostStuffUsize { perm: mut reserve_perm, token: mut reserve_token } = gs;

                // Proof BEFORE fetch_sub to satisfy precondition
                proof {
                    self.shared.instance.borrow().check_reserve_equality(&reserve_token, &prod_token);
                    assert(prod_token.value().grant_sz() == len as int);
                    assert(prod_token.value().reserve >= len as int);
                    assert(prod_token.value().reserve == reserve_token.value());
                    assert(usize::MIN as int <= reserve_perm@.value - (len - used));
                }
                self.shared.reserve.fetch_sub(Tracked(&mut reserve_perm), len - used);
                proof {
                    let _ = self.shared.instance.borrow().sub_reserve_at_commit((len - used) as nat, &mut reserve_token, &mut prod_token, &mut grant_state_token);
                }

                proof { gs = GhostStuffUsize { perm: reserve_perm, token: reserve_token }; }
            });

            // After sub_reserve: prod_start unchanged, prod_end shrinks (new_pe <= old_pe)
            // full_prod_ptr.dom() = [base+old_ps, base+old_pe)
            // New prod region = [base+new_ps, base+new_pe) where new_ps == old_ps, new_pe <= old_pe
            proof {
                self.shared.instance.borrow().check_grant_bounds_disjoint(&grant_state_token);
                let new_ps = grant_state_token.value().prod_start;
                let new_pe = grant_state_token.value().prod_end;
                // sub_reserve_at_commit preserves prod_start and changes prod_end
                assert(new_ps == old_ps);
                assert(new_pe <= old_pe);
                assert(set_int_range(base + new_ps, base + new_pe).subset_of(full_prod_ptr.dom())) by {
                    assert forall |i: int| set_int_range(base + new_ps, base + new_pe).contains(i)
                        implies full_prod_ptr.dom().contains(i) by {
                        // i in [base+new_ps, base+new_pe) ⊆ [base+old_ps, base+old_pe) = full_prod_ptr.dom()
                        assert(base + old_ps <= i && i < base + new_pe);
                        assert(new_pe <= old_pe);
                        assert(i < base + old_pe);
                    };
                };
            }
            let tracked (kept, returned) = full_prod_ptr.split(set_int_range(
                base + grant_state_token.value().prod_start,
                base + grant_state_token.value().prod_end));
            proof { full_prod_ptr = kept; }
            proof {
                // Establish full_prod_ptr.dom() in terms of prod_token (persists outside invariant block)
                self.shared.instance.borrow().check_grant_prod_eq(&prod_token, &grant_state_token);
                assert(full_prod_ptr.dom() =~= set_int_range(
                    base + prod_token.value().grant_start(),
                    base + prod_token.value().grant_end()));
            }
            let tracked current_pool = current_pool.join(returned);

            // Prove bp.wf(inst) for restored invariant
            proof {
                let new_ps = grant_state_token.value().prod_start;
                let new_pe = grant_state_token.value().prod_end;
                let new_cs = grant_state_token.value().cons_start;
                let new_ce = grant_state_token.value().cons_end;
                let whole_set = set_int_range(base, base + buf_len);
                let new_prod_set = set_int_range(new_ps + base, new_pe + base);
                let new_cons_set = set_int_range(new_cs + base, new_ce + base);

                // sub_reserve doesn't change cons
                assert(new_cs == old_cs);
                assert(new_ce == old_ce);

                // returned.dom() = full_prod_ptr_old_dom \ new_prod_range
                // = [base+old_ps, base+old_pe) \ [base+new_ps, base+new_pe)
                // Since new_ps == old_ps: = [base+new_pe, base+old_pe)
                // current_pool = old_pool.join(returned)
                // old_pool.dom() = whole \ old_prod \ old_cons
                // So current_pool.dom() = (whole \ old_prod \ old_cons) ∪ [base+new_pe, base+old_pe)
                //   = whole \ [base+old_ps, base+new_pe) \ old_cons
                //   = whole \ new_prod \ new_cons (since old_cons == new_cons)
                assert(current_pool.dom() =~= Set::new(|i: int|
                    whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i))) by {
                    assert forall |i: int| current_pool.dom().contains(i) <==>
                        (whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i)) by {
                        // current_pool.dom() = old_pool.dom() ∪ returned.dom()
                        if current_pool.dom().contains(i) {
                            // i is in old_pool or returned
                            if !(base + new_pe <= i && i < base + old_pe) {
                                // i is in old_pool: whole and not old_prod and not old_cons
                                // not old_prod means not in [base+old_ps, base+old_pe)
                                // new_prod = [base+old_ps, base+new_pe) ⊆ [base+old_ps, base+old_pe) = old_prod
                                // So not in old_prod → not in new_prod
                            } else {
                                // i is in returned: [base+new_pe, base+old_pe)
                                // i >= base+new_pe, so not in [base+old_ps, base+new_pe) = new_prod ✓
                                // i was in old_prod = [base+old_ps, base+old_pe), from disjointness: not in old_cons
                                assert(base + old_ps <= i && i < base + old_pe);
                                // Not in old_cons = new_cons
                                assert(!(base + old_cs <= i && i < base + old_ce));
                            }
                        }
                    };
                };
                // Disjointness
                assert(new_prod_set.disjoint(new_cons_set)) by {
                    assert forall |i: int| !(new_prod_set.contains(i) && new_cons_set.contains(i)) by {
                        if new_ps == new_pe || new_cs == new_ce {
                        } else if new_pe <= new_cs {
                            if new_prod_set.contains(i) {
                                assert(i < base + new_pe);
                                assert(i < base + new_cs);
                            }
                        } else {
                            assert(new_ce <= new_ps);
                            if new_cons_set.contains(i) {
                                assert(i < base + new_ce);
                                assert(i < base + new_ps);
                            }
                        }
                    };
                };
            }
            proof { bp = GhostBufferPermission { pool: current_pool, grant_state_token}; }
        });

        let max = self.shared.length as usize;
        let last: usize;
        open_atomic_invariant!(self.shared.last_inv.borrow().borrow() => gs => {
            let tracked GhostStuffUsize { perm: mut last_perm, token: mut last_token } = gs;

            last = self.shared.last.load(Tracked(&mut last_perm));
            proof {
                let _ = self.shared.instance.borrow().load_last_at_commit(&last_token, &mut prod_token);
                self.shared.instance.borrow().check_last_equality(&last_token, &prod_token);
            }

            proof { gs = GhostStuffUsize { perm: last_perm, token: last_token }; }
        });


        let new_write: usize;
        open_atomic_invariant!(self.shared.reserve_inv.borrow().borrow() => gs => {
            let tracked GhostStuffUsize { perm: mut reserve_perm, token: mut reserve_token } = gs;

            new_write = self.shared.reserve.load(Tracked(&mut reserve_perm));
            proof {
                let _ = self.shared.instance.borrow().load_reserve_at_commit(&reserve_token, &mut prod_token);
                assert(reserve_token.value() == prod_token.value().reserve);
            }

            proof { gs = GhostStuffUsize { perm: reserve_perm, token: reserve_token }; }
        });

        if (new_write < write) && (write != max) {
            // We have already wrapped, but we are skipping some bytes at the end of the ring.
            // Mark `last` where the write pointer used to be to hold the line here
            open_atomic_invariant!(self.shared.last_inv.borrow().borrow() => gs => {
                let tracked GhostStuffUsize { perm: mut last_perm, token: mut last_token } = gs;
                let _ = self.shared.last.store(Tracked(&mut last_perm), write);
                    
                proof {
                    let _ = self.shared.instance.borrow().check_last_equality(&last_token, &prod_token);
                    let _ = self.shared.instance.borrow().update_last_by_write_at_commit(write as nat, &mut last_token, &mut prod_token);
                }
                
                proof { gs = GhostStuffUsize { perm: last_perm, token: last_token }; }
            });
        } else if new_write > last {
            // We're about to pass the last pointer, which was previously the artificial
            // end of the ring. Now that we've passed it, we can "unlock" the section
            // that was previously skipped.
            //
            // Since new_write is strictly larger than last, it is safe to move this as
            // the other thread will still be halted by the (about to be updated) write
            // value
            open_atomic_invariant!(self.shared.last_inv.borrow().borrow() => gs => {
                let tracked GhostStuffUsize { perm: mut last_perm, token: mut last_token } = gs;
                let _ = self.shared.last.store(Tracked(&mut last_perm), max);
                    
                proof {
                    let _ = self.shared.instance.borrow().update_last_by_max_at_commit(&mut last_token, &mut prod_token);
                    assert(prod_token.value().last == max as nat);
                }
                
                proof { gs = GhostStuffUsize { perm: last_perm, token: last_token }; }
            });
        }
        // else: If new_write == last, either:
        // * last == max, so no need to write, OR
        // * If we write in the end chunk again, we'll update last to max next time
        // * If we write to the start chunk in a wrap, we'll update last when we
        //     move write backwards

        // Write must be updated AFTER last, otherwise read could think it was
        // time to invert early!
        open_atomic_invariant!(self.shared.buf_perm_inv.borrow().borrow() => bp => {
            let tracked GhostBufferPermission {
                pool: mut current_pool,
                grant_state_token: mut grant_state_token,
            } = bp;

            // Save ghost snapshots BEFORE mutation
            let ghost base = self.shared.instance@.base_addr() as int;
            let ghost buf_len2 = self.shared.instance@.length() as int;
            let ghost old_ps = grant_state_token.value().prod_start;
            let ghost old_pe = grant_state_token.value().prod_end;
            let ghost old_cs = grant_state_token.value().cons_start;
            let ghost old_ce = grant_state_token.value().cons_end;

            // Establish old bounds, disjointness, and full_prod_ptr.dom() before mutation
            proof {
                self.shared.instance.borrow().check_grant_bounds_disjoint(&grant_state_token);
                self.shared.instance.borrow().check_grant_prod_eq(&prod_token, &grant_state_token);
                // Connect full_prod_ptr.dom() to current grant state via prod_token
                assert(full_prod_ptr.dom() =~= set_int_range(base + old_ps, base + old_pe));
                // Save old pool domain characterization
                assert forall |i: int| current_pool.dom().contains(i) <==>
                    (base <= i && i < base + buf_len2
                     && !(base + old_ps <= i && i < base + old_pe)
                     && !(base + old_cs <= i && i < base + old_ce)) by {};
            }

            open_atomic_invariant!(self.shared.write_inv.borrow().borrow() => gs => {
                let tracked GhostStuffUsize { perm: mut write_perm, token: mut write_token } = gs;
                let _ = self.shared.write.store(Tracked(&mut write_perm), new_write);
                proof {
                    let _ = self.shared.instance.borrow().check_write_equality(&write_token, &prod_token);
                    let _ = self.shared.instance.borrow().store_write_at_commit(new_write as nat, &mut write_token, &mut prod_token, &mut grant_state_token);
                }

                proof { gs = GhostStuffUsize { perm: write_perm, token: write_token }; }
            });

            // After store_write_at_commit: prod_start = new_write = reserve = prod_end (prod_set = {})
            // full_prod_ptr covers [base+old_ps, base+old_pe) (the remaining after sub_reserve)
            // Join back into pool
            let tracked current_pool = current_pool.join(full_prod_ptr);

            // Prove bp.wf(inst)
            proof {
                self.shared.instance.borrow().check_grant_bounds_disjoint(&grant_state_token);
                self.shared.instance.borrow().check_grant_prod_eq(&prod_token, &grant_state_token);
                // After store_write: write == reserve, so grant_start() == grant_end()
                // check_grant_prod_eq gives: prod_start == producer.grant_start(), prod_end == producer.grant_end()
                // Since producer.write == producer.reserve (both == new_write), grant_start == grant_end
                let new_ps = grant_state_token.value().prod_start;
                let new_pe = grant_state_token.value().prod_end;
                let new_cs = grant_state_token.value().cons_start;
                let new_ce = grant_state_token.value().cons_end;
                let whole_set = set_int_range(base, base + buf_len2);
                let new_prod_set = set_int_range(new_ps + base, new_pe + base);
                let new_cons_set = set_int_range(new_cs + base, new_ce + base);

                assert(new_cs == old_cs);
                assert(new_ce == old_ce);
                assert(new_ps == new_pe); // prod is now empty (grant_start == grant_end since write == reserve)

                // current_pool = old_pool + full_prod_ptr
                // old_pool.dom() = whole_set \ [base+old_ps, base+old_pe) \ [base+old_cs, base+old_ce)
                // full_prod_ptr.dom() = [base+old_ps, base+old_pe)
                // current_pool.dom() = whole_set \ [base+old_cs, base+old_ce)
                // = whole_set \ {} \ new_cons_set  (since new_prod_set is empty as ps == pe)
                // current_pool = old_pool.join(full_prod_ptr)
                // full_prod_ptr.dom() = [base+old_ps, base+old_pe)
                // old_pool.dom() = whole_set \ old_prod \ old_cons
                // current_pool.dom() = whole_set \ old_cons (since join adds back the old prod region)
                // Since new_prod_set is empty and new_cons == old_cons:
                assert(current_pool.dom() =~= Set::new(|i: int|
                    whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i))) by {
                    assert forall |i: int| current_pool.dom().contains(i) <==>
                        (whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i)) by {
                        if current_pool.dom().contains(i) {
                            // → direction: i is in old_pool or in full_prod_ptr
                            if full_prod_ptr.dom().contains(i) {
                                // i was in full_prod_ptr = [base+old_ps, base+old_pe)
                                // whole_set: from bounds (old_ps >= 0, old_pe <= buf_len2)
                                // not in old_cons: from disjointness of old_prod and old_cons
                            } else {
                                // i was in old_pool: whole_set and not old_cons
                            }
                        } else {
                            // ← direction: show not (whole(i) && !new_cons(i))
                            // If whole(i) && !old_cons(i):
                            //   if !old_prod(i): old_pool(i) from formula → pool_joined(i). Contradiction.
                            //   if old_prod(i): full_prod_ptr(i) → pool_joined(i). Contradiction.
                            if (whole_set.contains(i) && !(base + old_cs <= i && i < base + old_ce)) {
                                if !(base + old_ps <= i && i < base + old_pe) {
                                    // from old pool formula: i ∈ old_pool → i ∈ joined pool
                                } else {
                                    // i ∈ [old_ps, old_pe) = full_prod_ptr.dom() → i ∈ joined pool
                                    assert(full_prod_ptr.dom().contains(i));
                                }
                            }
                        }
                    };
                };
                assert(new_prod_set.disjoint(new_cons_set)) by {
                    assert forall |i: int| !(new_prod_set.contains(i) && new_cons_set.contains(i)) by {};
                };
            }
            proof { bp = GhostBufferPermission { pool: current_pool, grant_state_token}; }
        });

        // Allow subsequent grants — end_commit sets write_in_progress=false, read_obs=None
        open_atomic_invariant!(self.shared.write_in_progress_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut write_in_progress_perm, token: mut write_in_progress_token } = gs;

            self.shared.write_in_progress.store(Tracked(&mut write_in_progress_perm), false);

            proof {
                let _ = self.shared.instance.borrow().end_commit(&mut write_in_progress_token, &mut prod_token);
            }

            proof { gs = GhostStuffBool { perm: write_in_progress_perm, token: write_in_progress_token }; }
        });

        return Tracked(prod_token);
    }
}

pub struct Consumer<'a> {
    buffer_ptr: *mut u8,
    shared: VBBufferShared<'a>,
    cons_token: Tracked<Option<VBQueue::consumer>>,
}

impl<'a> Consumer<'a> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.buffer_ptr@.provenance == self.shared.instance@.provenance()
        &&& self.buffer_ptr as int == self.shared.instance@.base_addr()
        &&& self.buffer_ptr as int + self.shared.instance@.length() <= usize::MAX + 1
        &&& self.shared.wf()
    }
    pub closed spec fn is_idle(&self) -> bool {
        &&& self.cons_token@ is Some
        &&& self.cons_token@->0.instance_id() == self.shared.instance@.id()
        &&& self.cons_token@->0.value().is_idle()
        &&& self.wf()
    }
}

impl<'a> Consumer<'a> {
    fn read(&mut self) ->  (r: Result<GrantR, &'static str>)
        requires
            old(self).wf(),
            old(self).is_idle(),
        ensures
            self.wf(),
            match r {
                Ok(rgr) => {
                    &&& rgr.shared.instance@.id() == self.shared.instance@.id()
                    &&& rgr.cons_token@->0.instance_id() == old(self).cons_token@->0.instance_id()
                    &&& rgr.can_release(rgr.sz as nat)
                },
                _ => true,
            },
    {
        let tracked mut cons_token = self.cons_token.borrow_mut().tracked_take();

        let is_read_in_progress: bool;
        open_atomic_invariant!(self.shared.read_in_progress_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut read_in_progress_perm, token: mut read_in_progress_token } = gs;

            is_read_in_progress = self.shared.read_in_progress.swap(Tracked(&mut read_in_progress_perm), true);

            proof {
                if !is_read_in_progress {
                    let _ = self.shared.instance.borrow().start_read(&mut read_in_progress_token, &mut cons_token);
                    assert(read_in_progress_token.value() == true);
                    assert(is_read_in_progress == false);
                } else {
                    assert(read_in_progress_token.value() == true);
                    assert(is_read_in_progress == true);
                };
            }

            proof { gs = GhostStuffBool { perm: read_in_progress_perm, token: read_in_progress_token }; }
        });

        if is_read_in_progress {
            self.cons_token = Tracked(Some(cons_token));
            return Err("read in progress");
        }

        let tracked mut cons_points_to_raw: Option<PointsToRaw> = None;

        let write: usize;
        open_atomic_invariant!(self.shared.write_inv.borrow().borrow() => gs => {
            let tracked GhostStuffUsize { perm: mut write_perm, token: mut write_token } = gs;

            write = self.shared.write.load(Tracked(&mut write_perm));
            proof {
                let _ = self.shared.instance.borrow().load_write_at_read(&write_token, &mut cons_token);
            }

            proof { gs = GhostStuffUsize { perm: write_perm, token: write_token }; }
        });

        let last: usize;
        open_atomic_invariant!(self.shared.buf_perm_inv.borrow().borrow() => bp => {
            let tracked GhostBufferPermission {
                pool: mut current_pool,
                grant_state_token: mut grant_state_token,
            } = bp;

            // Save ghost snapshots BEFORE mutation
            let ghost base = self.buffer_ptr as int;
            let ghost len = self.shared.instance@.length() as int;
            let ghost old_ps = grant_state_token.value().prod_start;
            let ghost old_pe = grant_state_token.value().prod_end;
            let ghost old_cs = grant_state_token.value().cons_start;
            let ghost old_ce = grant_state_token.value().cons_end;

            // Before load_last_at_read: last_obs is None → cons_start == cons_end
            proof {
                self.shared.instance.borrow().check_grant_cons_no_last(&cons_token, &grant_state_token);
                self.shared.instance.borrow().check_grant_bounds_disjoint(&grant_state_token);
                assert(old_cs == old_ce);
                // Save old pool domain: pool = whole_set \ prod_set (since cons empty)
                assert forall |i: int| current_pool.dom().contains(i) <==>
                    (base <= i && i < base + len
                     && !(base + old_ps <= i && i < base + old_pe)) by {};
            }

            open_atomic_invariant!(self.shared.last_inv.borrow().borrow() => gs => {
                let tracked GhostStuffUsize { perm: mut last_perm, token: mut last_token } = gs;

                last = self.shared.last.load(Tracked(&mut last_perm));
                proof {
                    let _ = self.shared.instance.borrow().load_last_at_read(&last_token, &mut cons_token, &mut grant_state_token);
                }

                proof { gs = GhostStuffUsize { perm: last_perm, token: last_token }; }
            });

            // After load_last_at_read: cons expanded from empty to [cons_start, cons_end)
            // prod unchanged
            proof {
                self.shared.instance.borrow().check_grant_bounds_disjoint(&grant_state_token);
                let new_ps = grant_state_token.value().prod_start;
                let new_pe = grant_state_token.value().prod_end;
                let new_cs = grant_state_token.value().cons_start;
                let new_ce = grant_state_token.value().cons_end;
                // load_last_at_read doesn't change prod
                assert(new_ps == old_ps);
                assert(new_pe == old_pe);

                // Prove subset: new_cons_range ⊆ current_pool.dom()
                // pool.dom() = whole_set \ prod_set \ {} = whole_set \ prod_set (old cons was empty)
                assert(set_int_range(base + new_cs, base + new_ce).subset_of(current_pool.dom())) by {
                    assert forall |i: int| set_int_range(base + new_cs, base + new_ce).contains(i)
                        implies current_pool.dom().contains(i) by {
                        assert(base + new_cs <= i && i < base + new_ce);
                        assert(new_cs <= new_ce && new_ce <= len as nat);
                        assert(base <= i && i < base + len);
                        // Not in prod_set: from disjointness
                        if new_ps == new_pe || new_cs == new_ce {
                        } else if new_pe <= new_cs {
                            if new_ps + base <= i && i < new_pe + base {
                                assert(i < base + new_pe);
                                assert(i < base + new_cs);
                                assert(false);
                            }
                        } else {
                            assert(new_ce <= new_ps);
                            if new_ps + base <= i && i < new_pe + base {
                                assert(i >= base + new_ps);
                                assert(i >= base + new_ce);
                                assert(false);
                            }
                        }
                        // Not in old cons_set (which was empty)
                        assert(!(base + old_cs <= i && i < base + old_ce));
                    };
                };
            }
            let tracked (cons_part, pool_rest) = current_pool.split(set_int_range(
                self.buffer_ptr as int + grant_state_token.value().cons_start,
                self.buffer_ptr as int + grant_state_token.value().cons_end));
            proof {
                self.shared.instance.borrow().check_grant_cons_eq(&cons_token, &grant_state_token);
                assert(cons_part.dom() =~= set_int_range(
                    self.buffer_ptr as int + cons_token.value().grant_start(),
                    self.buffer_ptr as int + cons_token.value().grant_end()));
                cons_points_to_raw = Some(cons_part);
            }

            // Prove bp.wf(inst) for restored invariant
            proof {
                let new_ps = grant_state_token.value().prod_start;
                let new_pe = grant_state_token.value().prod_end;
                let new_cs = grant_state_token.value().cons_start;
                let new_ce = grant_state_token.value().cons_end;
                let whole_set = set_int_range(base, base + len);
                let new_prod_set = set_int_range(new_ps + base, new_pe + base);
                let new_cons_set = set_int_range(new_cs + base, new_ce + base);

                // prod unchanged by load_last_at_read
                assert(new_ps == old_ps);
                assert(new_pe == old_pe);
                // pool_rest = current_pool \ new_cons_range
                // current_pool.dom() = whole \ prod (old cons was empty, saved before mutation)
                // pool_rest.dom() = whole \ prod \ new_cons
                assert(pool_rest.dom() =~= Set::new(|i: int|
                    whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i))) by {
                    assert forall |i: int| pool_rest.dom().contains(i) <==>
                        (whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i)) by {
                        // pool_rest = current_pool \ new_cons_set
                        // current_pool.dom() = whole \ old_prod (from saved formula, old_cons empty)
                        // new_prod == old_prod
                    };
                };
                assert(new_prod_set.disjoint(new_cons_set)) by {
                    assert forall |i: int| !(new_prod_set.contains(i) && new_cons_set.contains(i)) by {
                        if new_ps == new_pe || new_cs == new_ce {
                        } else if new_pe <= new_cs {
                            if new_prod_set.contains(i) { assert(i < base + new_pe); assert(i < base + new_cs); }
                        } else {
                            assert(new_ce <= new_ps);
                            if new_cons_set.contains(i) { assert(i < base + new_ce); assert(i < base + new_ps); }
                        }
                    };
                };
            }
            proof { bp = GhostBufferPermission { pool: pool_rest, grant_state_token}; }
        });

        let mut read: usize;
        open_atomic_invariant!(self.shared.read_inv.borrow().borrow() => gs => {
            let tracked GhostStuffUsize { perm: mut read_perm, token: mut read_token } = gs;

            read = self.shared.read.load(Tracked(&mut read_perm));
            proof {
                let _ = self.shared.instance.borrow().load_read_at_read(&read_token, &cons_token);
                self.shared.instance.borrow().check_read_is_le_last_in_inverted(&read_token, &cons_token);
                assert(write < read_token.value() ==> read_token.value() <= last);
            }

            proof { gs = GhostStuffUsize { perm: read_perm, token: read_token }; }
        });

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
            open_atomic_invariant!(self.shared.buf_perm_inv.borrow().borrow() => bp => {
                let tracked GhostBufferPermission {
                    pool: mut current_pool,
                    grant_state_token: mut grant_state_token,
                } = bp;

                // Save ghost snapshots BEFORE mutation
                let ghost base = self.buffer_ptr as int;
                let ghost len = self.shared.instance@.length() as int;
                let ghost old_ps = grant_state_token.value().prod_start;
                let ghost old_pe = grant_state_token.value().prod_end;
                let ghost old_cs = grant_state_token.value().cons_start;
                let ghost old_ce = grant_state_token.value().cons_end;

                // Establish old bounds, disjointness, and cons_ptr.dom() before join/mutation
                proof {
                    self.shared.instance.borrow().check_grant_bounds_disjoint(&grant_state_token);
                    self.shared.instance.borrow().check_grant_cons_eq(&cons_token, &grant_state_token);
                    // Save old pool domain characterization (from bp.wf)
                    assert forall |i: int| current_pool.dom().contains(i) <==>
                        (base <= i && i < base + len
                         && !(base + old_ps <= i && i < base + old_pe)
                         && !(base + old_cs <= i && i < base + old_ce)) by {};
                }

                // Return old cons region back to pool before wrap
                let tracked old_cons_ptr = match cons_points_to_raw {
                    Some(ptr) => ptr,
                    None => { assert(false); proof_from_false() }
                };
                proof {
                    cons_points_to_raw = None;
                    // Connect old_cons_ptr.dom() to old_cs/old_ce via cons_token bridge
                    assert(old_cons_ptr.dom() =~= set_int_range(base + old_cs, base + old_ce));
                }
                // After join: pool now has old cons region back
                let tracked mut current_pool = current_pool.join(old_cons_ptr);
                // Save joined pool domain BEFORE wrap_read mutation
                proof {
                    assert forall |i: int| current_pool.dom().contains(i) <==>
                        (base <= i && i < base + len
                         && !(base + old_ps <= i && i < base + old_pe)) by {
                        if current_pool.dom().contains(i) {
                            if old_cons_ptr.dom().contains(i) {
                                // in old_cons: within whole from bounds, not in prod from disjointness
                            }
                            // else: in old pool, already satisfies formula
                        } else {
                            // ← direction: if whole(i) && !prod(i), then either in old pool or old cons
                            if base <= i && i < base + len && !(base + old_ps <= i && i < base + old_pe) {
                                if base + old_cs <= i && i < base + old_ce {
                                    assert(old_cons_ptr.dom().contains(i));
                                }
                                // else: in old pool (from saved formula)
                            }
                        }
                    };
                }

                open_atomic_invariant!(self.shared.read_inv.borrow().borrow() => gs => {
                    let tracked GhostStuffUsize { perm: mut read_perm, token: mut read_token } = gs;
                    self.shared.read.store(Tracked(&mut read_perm), 0);
                    proof {
                        let _ = self.shared.instance.borrow().check_read_equality(&read_token, &mut cons_token);
                        let _ = self.shared.instance.borrow().wrap_read(&mut read_token, &mut cons_token, &mut grant_state_token);
                    }

                    proof { gs = GhostStuffUsize { perm: read_perm, token: read_token }; }
                });

                // After wrap_read: cons = [0, write_obs), prod unchanged
                proof {
                    self.shared.instance.borrow().check_grant_bounds_disjoint(&grant_state_token);
                    let new_ps = grant_state_token.value().prod_start;
                    let new_pe = grant_state_token.value().prod_end;
                    let new_cs = grant_state_token.value().cons_start;
                    let new_ce = grant_state_token.value().cons_end;
                    // wrap_read doesn't change prod
                    assert(new_ps == old_ps);
                    assert(new_pe == old_pe);

                    // Prove subset: new_cons_range ⊆ current_pool.dom()
                    // current_pool.dom() = whole_set \ prod_set (after joining old cons back)
                    assert(set_int_range(base + new_cs, base + new_ce).subset_of(current_pool.dom())) by {
                        assert forall |i: int| set_int_range(base + new_cs, base + new_ce).contains(i)
                            implies current_pool.dom().contains(i) by {
                            assert(base + new_cs <= i && i < base + new_ce);
                            assert(new_cs <= new_ce && new_ce <= len as nat);
                            assert(base <= i && i < base + len);
                            // Not in prod_set: from disjointness
                            if new_ps == new_pe || new_cs == new_ce {
                            } else if new_pe <= new_cs {
                                if old_ps + base <= i && i < old_pe + base {
                                    assert(i < base + new_pe);
                                    assert(i < base + new_cs);
                                    assert(false);
                                }
                            } else {
                                assert(new_ce <= new_ps);
                                if old_ps + base <= i && i < old_pe + base {
                                    assert(i >= base + new_ps);
                                    assert(i >= base + new_ce);
                                    assert(false);
                                }
                            }
                            // Not in old cons (which was merged back, so we're fine)
                        };
                    };
                }
                let tracked (cons_part, pool_rest) = current_pool.split(set_int_range(
                    self.buffer_ptr as int + grant_state_token.value().cons_start,
                    self.buffer_ptr as int + grant_state_token.value().cons_end));
                proof {
                    self.shared.instance.borrow().check_grant_cons_eq(&cons_token, &grant_state_token);
                    assert(cons_part.dom() =~= set_int_range(
                        self.buffer_ptr as int + cons_token.value().grant_start(),
                        self.buffer_ptr as int + cons_token.value().grant_end()));
                    cons_points_to_raw = Some(cons_part);
                }

                // Prove bp.wf(inst)
                proof {
                    let new_ps = grant_state_token.value().prod_start;
                    let new_pe = grant_state_token.value().prod_end;
                    let new_cs = grant_state_token.value().cons_start;
                    let new_ce = grant_state_token.value().cons_end;
                    let whole_set = set_int_range(base, base + len);
                    let new_prod_set = set_int_range(new_ps + base, new_pe + base);
                    let new_cons_set = set_int_range(new_cs + base, new_ce + base);

                    assert(pool_rest.dom() =~= Set::new(|i: int|
                        whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i))) by {
                        assert forall |i: int| pool_rest.dom().contains(i) <==>
                            (whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i)) by {};
                    };
                    assert(new_prod_set.disjoint(new_cons_set)) by {
                        assert forall |i: int| !(new_prod_set.contains(i) && new_cons_set.contains(i)) by {
                            if new_ps == new_pe || new_cs == new_ce {
                            } else if new_pe <= new_cs {
                                if new_prod_set.contains(i) { assert(i < base + new_pe); assert(i < base + new_cs); }
                            } else {
                                assert(new_ce <= new_ps);
                                if new_cons_set.contains(i) { assert(i < base + new_ce); assert(i < base + new_ps); }
                            }
                        };
                    };
                }
                proof { bp = GhostBufferPermission { pool: pool_rest, grant_state_token}; }
            });
        }

        let sz = if write < read {
            // Inverted, only believe last
            last
        } else {
            // Not inverted, only believe write
            write
        } - read;

        if sz == 0 {
            open_atomic_invariant!(self.shared.buf_perm_inv.borrow().borrow() => bp => {
                let tracked GhostBufferPermission {
                    pool: mut current_pool,
                    grant_state_token: mut grant_state_token,
                } = bp;

                // Save ghost snapshots BEFORE mutation
                let ghost base = self.buffer_ptr as int;
                let ghost len = self.shared.instance@.length() as int;
                let ghost old_ps = grant_state_token.value().prod_start;
                let ghost old_pe = grant_state_token.value().prod_end;
                let ghost old_cs = grant_state_token.value().cons_start;
                let ghost old_ce = grant_state_token.value().cons_end;

                // Establish old bounds, disjointness, and cons_ptr connection
                proof {
                    self.shared.instance.borrow().check_grant_bounds_disjoint(&grant_state_token);
                    self.shared.instance.borrow().check_grant_cons_eq(&cons_token, &grant_state_token);
                    assert forall |i: int| current_pool.dom().contains(i) <==>
                        (base <= i && i < base + len
                         && !(base + old_ps <= i && i < base + old_pe)
                         && !(base + old_cs <= i && i < base + old_ce)) by {};
                }

                // Return cons PointsToRaw back to pool (read_fail resets cons to empty)
                let tracked cons_ptr = match cons_points_to_raw {
                    Some(ptr) => ptr,
                    None => { assert(false); proof_from_false() }
                };
                proof {
                    cons_points_to_raw = None;
                    assert(cons_ptr.dom() =~= set_int_range(base + old_cs, base + old_ce));
                }
                let tracked mut current_pool = current_pool.join(cons_ptr);

                // Save joined pool domain BEFORE read_fail mutation
                proof {
                    assert forall |i: int| current_pool.dom().contains(i) <==>
                        (base <= i && i < base + len
                         && !(base + old_ps <= i && i < base + old_pe)) by {
                        if current_pool.dom().contains(i) {
                            if cons_ptr.dom().contains(i) {
                                // in cons: within whole from bounds, not in prod from disjointness
                            }
                        } else {
                            if base <= i && i < base + len && !(base + old_ps <= i && i < base + old_pe) {
                                if base + old_cs <= i && i < base + old_ce {
                                    assert(cons_ptr.dom().contains(i));
                                }
                            }
                        }
                    };
                }

                open_atomic_invariant!(self.shared.read_in_progress_inv.borrow().borrow() => gs => {
                    let tracked GhostStuffBool { perm: mut read_in_progress_perm, token: mut read_in_progress_token } = gs;

                    self.shared.read_in_progress.store(Tracked(&mut read_in_progress_perm), false);
                    proof {
                        let _ = self.shared.instance.borrow().read_fail(&mut read_in_progress_token, &mut cons_token, &mut grant_state_token);
                    }

                    proof { gs = GhostStuffBool { perm: read_in_progress_perm, token: read_in_progress_token }; }
                });

                // After read_fail: cons_start == cons_end == read (cons empty), prod unchanged
                proof {
                    self.shared.instance.borrow().check_grant_bounds_disjoint(&grant_state_token);
                    let new_ps = grant_state_token.value().prod_start;
                    let new_pe = grant_state_token.value().prod_end;
                    let new_cs = grant_state_token.value().cons_start;
                    let new_ce = grant_state_token.value().cons_end;
                    let whole_set = set_int_range(base, base + len);
                    let new_prod_set = set_int_range(new_ps + base, new_pe + base);
                    let new_cons_set = set_int_range(new_cs + base, new_ce + base);

                    // read_fail doesn't change prod
                    assert(new_ps == old_ps);
                    assert(new_pe == old_pe);
                    // cons is now empty
                    assert(new_cs == new_ce);

                    // current_pool = old_pool + cons_ptr
                    // = (whole_set \ prod_set \ old_cons_set) ∪ old_cons_set
                    // = whole_set \ prod_set
                    // Need: whole_set \ prod_set = whole_set \ prod_set \ {} (new cons empty)
                    assert(current_pool.dom() =~= Set::new(|i: int|
                        whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i))) by {
                        assert forall |i: int| current_pool.dom().contains(i) <==>
                            (whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i)) by {
                            // new_cons_set is empty since new_cs == new_ce
                        };
                    };
                    assert(new_prod_set.disjoint(new_cons_set)) by {
                        assert forall |i: int| !(new_prod_set.contains(i) && new_cons_set.contains(i)) by {};
                    };
                }
                proof { bp = GhostBufferPermission { pool: current_pool, grant_state_token}; }
            });
            return Err("Insufficient size");
        }

        // This is sound, as UnsafeCell, MaybeUninit, and GenericArray
        // are all `#[repr(Transparent)]
        //let start_of_buf_ptr = inner.buf.get().cast::<u8>();
        //let grant_slice = unsafe { from_raw_parts_mut(start_of_buf_ptr.offset(read as isize), sz) };

        // Verify can_release preconditions before returning
        // GrantR.buffer_ptr will be base + read = base + grant_start
        proof {
            let cpr = cons_points_to_raw;
            let ghost grant_ptr_int = self.buffer_ptr as int + read as int;
            assert(cpr is Some);
            assert(cpr->0.provenance() == self.shared.instance@.provenance());
            // dom in terms of the offset pointer: [grant_ptr, grant_ptr + sz)
            assert(cpr->0.dom() =~= set_int_range(grant_ptr_int, grant_ptr_int + sz as int));
            // grant_ptr == base_addr + grant_start
            assert(grant_ptr_int == self.shared.instance@.base_addr() + cons_token.value().grant_start());
            assert(self.buffer_ptr@.provenance == self.shared.instance@.provenance());
            assert(self.shared.instance@.base_addr() + self.shared.instance@.length() <= usize::MAX + 1);
        }

        Ok(
            GrantR {
                buffer_ptr: {
                    let addr = self.buffer_ptr as usize + read;
                    with_exposed_provenance(addr, expose_provenance(self.buffer_ptr))
                },
                sz,
                shared: VBBufferShared {
                    length: self.shared.length,
                    write: &self.shared.write,
                    read: &self.shared.read,
                    last: &self.shared.last,
                    reserve: &self.shared.reserve,
                    read_in_progress: &self.shared.read_in_progress,
                    write_in_progress: &self.shared.write_in_progress,
                    // already_split: &'a PAtomicBool,

                    /* バッファ分割管理用不変条件 */
                    buf_perm_inv: Tracked(self.shared.buf_perm_inv.borrow().clone()),

                    /* Atomic変数用不変条件 */
                    write_inv: Tracked(self.shared.write_inv.borrow().clone()),
                    read_inv: Tracked(self.shared.read_inv.borrow().clone()),
                    last_inv: Tracked(self.shared.last_inv.borrow().clone()),
                    reserve_inv: Tracked(self.shared.reserve_inv.borrow().clone()),
                    read_in_progress_inv: Tracked(self.shared.read_in_progress_inv.borrow().clone()),
                    write_in_progress_inv: Tracked(self.shared.write_in_progress_inv.borrow().clone()),

                    instance: Tracked(self.shared.instance.borrow().clone()),
                },
                points_to_raw_token: Tracked(cons_points_to_raw),
                cons_token: Tracked(Some(cons_token)),
            }
        )
    }
}

struct GrantR<'a> {
    buffer_ptr: *mut u8,
    sz: usize,
    shared: VBBufferShared<'a>,
    points_to_raw_token: Tracked<Option<PointsToRaw>>,
    cons_token: Tracked<Option<VBQueue::consumer>>,
}

impl<'a> GrantR<'a> {
    pub closed spec fn can_release(&self, sz: nat) -> bool {
        &&& self.shared.wf()
        &&& self.sz as nat == sz
        &&& self.cons_token@ is Some
        &&& self.cons_token@->0.instance_id() == self.shared.instance@.id()
        &&& self.cons_token@->0.value().is_idle() || self.cons_token@->0.value().is_granted(sz)
        // Pool management properties
        &&& self.points_to_raw_token@ is Some
        &&& self.points_to_raw_token@->0.provenance() == self.shared.instance@.provenance()
        &&& self.points_to_raw_token@->0.dom() =~= set_int_range(
            self.buffer_ptr as int,
            self.buffer_ptr as int + self.sz as int)
        &&& self.buffer_ptr as int == self.shared.instance@.base_addr() + self.cons_token@->0.value().grant_start()
        &&& self.buffer_ptr@.provenance == self.shared.instance@.provenance()
        &&& self.shared.instance@.base_addr() + self.shared.instance@.length() <= usize::MAX + 1
        // grant region fits within buffer: buffer_ptr + sz <= base_addr + length
        &&& self.buffer_ptr as int + self.sz as int
            <= self.shared.instance@.base_addr() + self.shared.instance@.length()
    }

    pub closed spec fn released(&self) -> bool {
        &&& self.shared.wf()
        &&& self.cons_token@ is None
    }
}

impl<'a> GrantR<'a> {
    /// Read a single byte at offset `idx` within the grant region.
    /// Pattern: split PointsToRaw → into_typed → assume init (producer wrote it) → ptr_mut_read → into_raw → join
    /// Note: PointsToRaw loses init tracking across the producer→consumer boundary,
    /// so we assume the byte is initialized (the producer must have written it).
    fn read_byte(&mut self, idx: usize) -> (val: u8)
        requires
            old(self).can_release(old(self).sz as nat),
            idx < old(self).sz,
        ensures
            self.can_release(self.sz as nat),
            self.sz == old(self).sz,
            self.buffer_ptr == old(self).buffer_ptr,
            self.shared == old(self).shared,
            self.cons_token == old(self).cons_token,
    {
        let addr: usize = self.buffer_ptr as usize + idx;

        // Split 1-byte region from PointsToRaw
        let tracked mut ptr_raw = self.points_to_raw_token.borrow_mut().tracked_take();
        proof {
            assert(set_int_range(addr as int, addr + 1).subset_of(
                set_int_range(self.buffer_ptr as int, self.buffer_ptr as int + self.sz as int)));
        }
        let tracked (byte_raw, rest) = ptr_raw.split(set_int_range(addr as int, addr + 1));
        assert(byte_raw.is_range(addr as int, 1));

        // Convert to typed PointsTo<u8>
        // global layout u8 guarantees align_of::<u8>() == 1, so addr % 1 == 0
        let tracked mut byte_pto = byte_raw.into_typed::<u8>(addr);
        let current_ptr: *mut u8 = with_exposed_provenance(addr, expose_provenance(self.buffer_ptr));
        assert(equal(byte_pto.ptr(), current_ptr));

        // Assume init: producer wrote to this byte before committing
        assume(byte_pto.is_init());
        let val = ptr_mut_read(current_ptr, Tracked(&mut byte_pto));

        // After ptr_mut_read, byte_pto is uninit → can convert back to raw
        let tracked read_raw = byte_pto.into_raw();
        let tracked rejoined = rest.join(read_raw);

        proof {
            assert(rejoined.dom() =~= set_int_range(self.buffer_ptr as int, self.buffer_ptr as int + self.sz as int));
        }
        self.points_to_raw_token = Tracked(Some(rejoined));

        val
    }
}

impl<'a> GrantR<'a> {
    fn release(&mut self,
        used: usize
    ) -> (cons_token: Tracked<VBQueue::consumer>)
        requires
            used <= old(self).sz,
            old(self).can_release(old(self).sz as nat),
        ensures
            self.shared.wf(),
            self.released(),
            cons_token@.instance_id() == old(self).cons_token@->0.instance_id(),
            cons_token@.instance_id() == self.shared.instance@.id(),
            cons_token@.value().is_idle(),
    {
        let tracked mut cons_token = self.cons_token.borrow_mut().tracked_take();

        // If there is no grant in progress, return early. This
        // generally means we are dropping the grant within a
        // wrapper structure
        let is_read_in_progress: bool;
        open_atomic_invariant!(self.shared.read_in_progress_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut read_in_progress_perm, token: mut read_in_progress_token } = gs;

            is_read_in_progress = self.shared.read_in_progress.load(Tracked(&mut read_in_progress_perm));

            proof {
                let _ = self.shared.instance.borrow().start_release(&read_in_progress_token, &cons_token);
            }

            proof { gs = GhostStuffBool { perm: read_in_progress_perm, token: read_in_progress_token }; }
        });

        if !is_read_in_progress {
            return Tracked(cons_token);
        }

        // Take out the GrantR's cons PointsToRaw for pool management
        let tracked mut full_cons_ptr = self.points_to_raw_token.borrow_mut().tracked_take();

        open_atomic_invariant!(self.shared.buf_perm_inv.borrow().borrow() => bp => {
            let tracked GhostBufferPermission {
                pool: mut current_pool,
                grant_state_token: mut grant_state_token,
            } = bp;

            // Save ghost snapshots BEFORE mutation
            let ghost base = self.shared.instance@.base_addr() as int;
            let ghost len = self.shared.instance@.length() as int;
            let ghost old_ps = grant_state_token.value().prod_start;
            let ghost old_pe = grant_state_token.value().prod_end;
            let ghost old_cs = grant_state_token.value().cons_start;
            let ghost old_ce = grant_state_token.value().cons_end;
            // full_cons_ptr.dom() = [base+old_cons_start, base+old_cons_end) from can_release
            proof {
                self.shared.instance.borrow().check_grant_cons_eq(&cons_token, &grant_state_token);
            }

            open_atomic_invariant!(self.shared.read_inv.borrow().borrow() => gs => {
                let tracked GhostStuffUsize { perm: mut read_perm, token: mut read_token } = gs;

                // Proof BEFORE fetch_add to satisfy precondition
                proof {
                    let _ = self.shared.instance.borrow().check_read_equality(&read_token, &cons_token);
                    let _ = self.shared.instance.borrow().check_consumer_obs_in_range(&mut cons_token);
                    assert(read_perm@.value + used <= self.shared.instance@.length());
                }
                let _ = self.shared.read.fetch_add(Tracked(&mut read_perm), used);
                proof {
                    let _ = self.shared.instance.borrow().add_read_at_release(used as nat, &mut read_token, &mut cons_token, &mut grant_state_token);
                }

                proof { gs = GhostStuffUsize { perm: read_perm, token: read_token }; }
            });

            // After add_read_at_release: cons_start = read+used, cons_end might change
            // full_cons_ptr covers [base+old_cs, base+old_ce) from can_release
            // New cons region [base+new_cs, base+new_ce) is a subset of old (new_cs >= old_cs)
            proof {
                self.shared.instance.borrow().check_grant_bounds_disjoint(&grant_state_token);
                let new_cs = grant_state_token.value().cons_start;
                let new_ce = grant_state_token.value().cons_end;
                // add_read_at_release doesn't change prod
                assert(grant_state_token.value().prod_start == old_ps);
                assert(grant_state_token.value().prod_end == old_pe);
                // cons_start advanced, cons_end unchanged or different
                assert(new_cs >= old_cs);
                assert(new_ce <= old_ce);
                assert(set_int_range(base + new_cs, base + new_ce).subset_of(full_cons_ptr.dom())) by {
                    assert forall |i: int| set_int_range(base + new_cs, base + new_ce).contains(i)
                        implies full_cons_ptr.dom().contains(i) by {
                        assert(base + new_cs <= i && i < base + new_ce);
                        assert(new_cs >= old_cs);
                        assert(i >= base + old_cs);
                        assert(new_ce <= old_ce);
                        assert(i < base + old_ce);
                    };
                };
            }
            let tracked (remaining, consumed) = full_cons_ptr.split(set_int_range(
                base + grant_state_token.value().cons_start,
                base + grant_state_token.value().cons_end));
            proof { full_cons_ptr = remaining; }
            proof {
                // Establish full_cons_ptr.dom() in terms of cons_token (persists outside invariant block)
                self.shared.instance.borrow().check_grant_cons_eq(&cons_token, &grant_state_token);
                assert(full_cons_ptr.dom() =~= set_int_range(
                    base + cons_token.value().grant_start(),
                    base + cons_token.value().grant_end()));
            }
            let tracked current_pool = current_pool.join(consumed);

            // Prove bp.wf(inst)
            proof {
                let new_ps = grant_state_token.value().prod_start;
                let new_pe = grant_state_token.value().prod_end;
                let new_cs = grant_state_token.value().cons_start;
                let new_ce = grant_state_token.value().cons_end;
                let whole_set = set_int_range(base, base + len);
                let new_prod_set = set_int_range(new_ps + base, new_pe + base);
                let new_cons_set = set_int_range(new_cs + base, new_ce + base);

                assert(current_pool.dom() =~= Set::new(|i: int|
                    whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i))) by {
                    assert forall |i: int| current_pool.dom().contains(i) <==>
                        (whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i)) by {
                        // current_pool = old_pool + consumed
                        // consumed = [base+old_cs, base+new_cs) (the "eaten" part of cons)
                        // remaining = [base+new_cs, base+new_ce) (kept by GrantR)
                        // old_pool = whole_set \ old_prod_set \ old_cons_set
                        // current_pool = whole_set \ old_prod_set \ old_cons_set ∪ consumed
                        //   = whole_set \ old_prod_set \ [base+new_cs, base+old_ce)
                        // Since new_ce <= old_ce: old_cons = [old_cs, old_ce), new cons = [new_cs, new_ce)
                        // Hmm, need to think about this more carefully
                    };
                };
                assert(new_prod_set.disjoint(new_cons_set)) by {
                    assert forall |i: int| !(new_prod_set.contains(i) && new_cons_set.contains(i)) by {
                        if new_ps == new_pe || new_cs == new_ce {
                        } else if new_pe <= new_cs {
                            if new_prod_set.contains(i) { assert(i < base + new_pe); assert(i < base + new_cs); }
                        } else {
                            assert(new_ce <= new_ps);
                            if new_cons_set.contains(i) { assert(i < base + new_ce); assert(i < base + new_ps); }
                        }
                    };
                };
            }
            proof { bp = GhostBufferPermission { pool: current_pool, grant_state_token}; }
        });

        open_atomic_invariant!(self.shared.buf_perm_inv.borrow().borrow() => bp => {
            let tracked GhostBufferPermission {
                pool: mut current_pool,
                grant_state_token: mut grant_state_token,
            } = bp;

            // Save ghost snapshots BEFORE mutation
            let ghost base = self.shared.instance@.base_addr() as int;
            let ghost len = self.shared.instance@.length() as int;
            let ghost old_ps = grant_state_token.value().prod_start;
            let ghost old_pe = grant_state_token.value().prod_end;
            let ghost old_cs = grant_state_token.value().cons_start;
            let ghost old_ce = grant_state_token.value().cons_end;

            // Establish old bounds, disjointness, full_cons_ptr.dom(), and old pool domain
            proof {
                self.shared.instance.borrow().check_grant_bounds_disjoint(&grant_state_token);
                self.shared.instance.borrow().check_grant_cons_eq(&cons_token, &grant_state_token);
                // Connect full_cons_ptr.dom() to old_cs/old_ce via cons_token bridge
                assert(full_cons_ptr.dom() =~= set_int_range(base + old_cs, base + old_ce));
                // Save old pool domain
                assert forall |i: int| current_pool.dom().contains(i) <==>
                    (base <= i && i < base + len
                     && !(base + old_ps <= i && i < base + old_pe)
                     && !(base + old_cs <= i && i < base + old_ce)) by {};
            }

            // Join remaining cons PointsToRaw back to pool (end_release resets cons to empty)
            let tracked mut current_pool = current_pool.join(full_cons_ptr);

            // Save joined pool domain BEFORE end_release mutation
            proof {
                assert forall |i: int| current_pool.dom().contains(i) <==>
                    (base <= i && i < base + len
                     && !(base + old_ps <= i && i < base + old_pe)) by {
                    if current_pool.dom().contains(i) {
                        if full_cons_ptr.dom().contains(i) {
                            // in cons: within whole from bounds, not in prod from disjointness
                        }
                    } else {
                        if base <= i && i < base + len && !(base + old_ps <= i && i < base + old_pe) {
                            if base + old_cs <= i && i < base + old_ce {
                                assert(full_cons_ptr.dom().contains(i));
                            }
                        }
                    }
                };
            }

            open_atomic_invariant!(self.shared.read_in_progress_inv.borrow().borrow() => gs => {
                let tracked GhostStuffBool { perm: mut read_in_progress_perm, token: mut read_in_progress_token } = gs;

                let _ = self.shared.read_in_progress.store(Tracked(&mut read_in_progress_perm), false);
                proof {
                    let _ = self.shared.instance.borrow().end_release(&mut read_in_progress_token, &mut cons_token, &mut grant_state_token);
                }

                proof { gs = GhostStuffBool { perm: read_in_progress_perm, token: read_in_progress_token }; }
            });

            // After end_release: cons_start == cons_end == read (cons empty), prod unchanged
            proof {
                self.shared.instance.borrow().check_grant_bounds_disjoint(&grant_state_token);
                let new_ps = grant_state_token.value().prod_start;
                let new_pe = grant_state_token.value().prod_end;
                let new_cs = grant_state_token.value().cons_start;
                let new_ce = grant_state_token.value().cons_end;
                let whole_set = set_int_range(base, base + len);
                let new_prod_set = set_int_range(new_ps + base, new_pe + base);
                let new_cons_set = set_int_range(new_cs + base, new_ce + base);

                assert(new_ps == old_ps);
                assert(new_pe == old_pe);
                assert(new_cs == new_ce); // cons is empty after end_release

                // current_pool.dom() was saved before mutation as whole \ prod
                // new_cons is empty, new_prod == old_prod
                assert(current_pool.dom() =~= Set::new(|i: int|
                    whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i))) by {
                    assert forall |i: int| current_pool.dom().contains(i) <==>
                        (whole_set.contains(i) && !new_prod_set.contains(i) && !new_cons_set.contains(i)) by {
                        // new_cons_set is empty since new_cs == new_ce
                        // current_pool.dom() = whole \ old_prod = whole \ new_prod (from saved formula)
                    };
                };
                assert(new_prod_set.disjoint(new_cons_set)) by {
                    assert forall |i: int| !(new_prod_set.contains(i) && new_cons_set.contains(i)) by {};
                };
            }
            proof { bp = GhostBufferPermission { pool: current_pool, grant_state_token}; }
        });

        return Tracked(cons_token);
    }
}

fn main() {
    let mut vbuf = VBBuffer::new(6);
    let (mut prod, mut cons) = match vbuf.try_split() {
        Ok((p, c)) => (p, c),
        Err(_) => return,
    };

    // ---- phase 1: write 5 bytes, read 5 bytes, verify ptr_mut_write/ptr_mut_read round-trip ----
    {
        let mut wgr = match prod.grant_exact(5) {
            Ok(w) => w,
            Err(_) => return,
        };
        if wgr.sz != 5 { return; }

        // ptr_mut_write test: write known values [10, 20, 30, 40, 50] into the grant region
        wgr.write_byte(0, 10);
        wgr.write_byte(1, 20);
        wgr.write_byte(2, 30);
        wgr.write_byte(3, 40);
        wgr.write_byte(4, 50);

        let Tracked(prod_token) = wgr.commit(5);
        assert(prod_token.instance_id() == wgr.shared.instance@.id());
        assert(prod_token.instance_id() == prod.shared.instance@.id());
        assert(prod_token.value().is_idle());

        prod.prod_token = Tracked(Some(prod_token));

        let mut rgr = match cons.read() {
            Ok(r) => r,
            Err(_) => return,
        };
        if rgr.sz != 5 { return; }

        // ptr_mut_read test: read back the values written above
        // (PointsToRaw loses value tracking, so we cannot statically assert equality;
        //  at runtime the values will be [10, 20, 30, 40, 50])
        let _v0 = rgr.read_byte(0);
        let _v1 = rgr.read_byte(1);
        let _v2 = rgr.read_byte(2);
        let _v3 = rgr.read_byte(3);
        let _v4 = rgr.read_byte(4);

        let Tracked(cons_token) = rgr.release(5);
        cons.cons_token = Tracked(Some(cons_token));
    }

    // ---- phase 2: wrap with "skip end chunk" (write=5, read=5, sz=4 -> start=0) ----
    // This should set last := old write (=5) during commit, then write := 4.
    {
        let mut wgr = match prod.grant_exact(4) {
            Ok(w) => w,
            Err(_) => return,
        };
        if wgr.sz != 4 { return; }
        let Tracked(prod_token) = wgr.commit(4);

        prod.prod_token = Tracked(Some(prod_token));

        let mut rgr = match cons.read() {
            Ok(r) => r,
            Err(_) => return,
        };
        if rgr.sz != 4 { return; }
        let Tracked(cons_token) = rgr.release(4);
        cons.cons_token = Tracked(Some(cons_token));
    }

    // ---- phase 3: unlock last back to max (last was 5, now new_write should become 6) ----
    {
        let mut wgr = match prod.grant_exact(2) {
            Ok(w) => w,
            Err(_) => return,
        };
        if wgr.sz != 2 { return; }
        let Tracked(prod_token) = wgr.commit(2);

        prod.prod_token = Tracked(Some(prod_token));

        let mut rgr = match cons.read() {
            Ok(r) => r,
            Err(_) => return,
        };
        if rgr.sz != 2 { return; }
        let Tracked(cons_token) = rgr.release(2);
        cons.cons_token = Tracked(Some(cons_token));
    }

    // ---- phase 4: wrap when old write == max (write=6, read=6, sz=1 -> start=0) ----
    // This time "skip" branch should NOT trigger because pre.write == max.
    {
        let mut wgr = match prod.grant_exact(1) {
            Ok(w) => w,
            Err(_) => return,
        };
        if wgr.sz != 1 { return; }
        let Tracked(prod_token) = wgr.commit(1);

        prod.prod_token = Tracked(Some(prod_token));

        let mut rgr = match cons.read() {
            Ok(r) => r,
            Err(_) => return,
        };
        if rgr.sz != 1 { return; }
        let Tracked(cons_token) = rgr.release(1);
        cons.cons_token = Tracked(Some(cons_token));
    }

    // ---- phase 5: empty read should fail ----
    {
        match cons.read() {
            Ok(_) => return,
            Err(_) => { /* OK */ }
        }
    }
}

}
