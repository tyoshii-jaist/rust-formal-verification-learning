use state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
use vstd::raw_ptr::*;
use vstd::{prelude::*, *};
use vstd::layout::*;
use std::sync::Arc;

verus! {
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
    pub prod_start: int,
    pub prod_end: int,
    pub cons_start: int,
    pub cons_end: int,
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
    fn store_write_at_commit_inductive(pre: Self, post: Self, new_write: nat) { }
    
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
}}

/*
    共有する不変条件用の構造体
*/
pub tracked struct GhostStuff<Perm, Tok>
where
    Tok: UniqueValueToken<nat>,
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
    Tok: UniqueValueToken<nat>,
{
    pub open spec fn wf(self, inst: VBQueue::Instance, cell: &PermissionBool) -> bool {
        &&& self.perm@.patomic == cell.id()
        &&& self.token.instance_id() == inst.id()
        &&& self.perm@.value == self.token.value()
    }
}

pub tracked struct GhostBufferPermission
{
    pub tracked pool: PointsToRaw,
    pub tracked token: VBQueue::grant_state,
}

impl GhostBufferPermission
{
    pub open spec fn wf(self, inst: VBQueue::Instance) -> bool {
        let ps = self.token.value().prod_start;
        let pe = self.token.value().prod_end;
        let cs = self.token.value().cons_start;
        let ce = self.token.value().cons_end;

        let whole_set = set_int_range(inst.base_addr() as int, inst.base_addr() as int + inst.length() as int);
        let prod_set = set_int_range(ps + inst.base_addr() as int, pe + inst.base_addr() as int);
        let cons_set = set_int_range(cs + inst.base_addr() as int, ce + inst.base_addr() as int);

        {
            
            &&& self.token.instance_id() == inst.id()
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
            is (v: GhostStuffUsize<VBQueue::read_in_progress>) {
                v.wf(instance@, read_in_progress)
        }

        invariant on write_in_progress_inv
            with (instance, write_in_progress)
            specifically (self.write_in_progress_inv@@)
            is (v: GhostStuffUsize<VBQueue::write_in_progress>) {
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
        &&& match self.producer@ {
                Some(prod) => prod.instance_id() == self.instance@.id(),
                None => true,
            }
        &&& match self.consumer@ {
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

        let (last, Tracked(last_perm)) = PAtomicUsize::new(0);
        let tracked last_gs = GhostStuffUsize { perm: last_perm, token: last_token };

        let (reserve, Tracked(reserve_perm)) = PAtomicUsize::new(0);
        let tracked reserve_gs = GhostStuffUsize { perm: reserve_perm, token: reserve_token };

        let (read_in_progress, Tracked(read_in_progress_perm)) = PAtomicBool::new(false);
        let tracked read_in_progress_gs = GhostStuffUsize { perm: read_in_progress_perm, token: read_in_progress_token };

        let (write_in_progress, Tracked(write_in_progress_perm)) = PAtomicBool::new(false);
        let tracked write_in_progress_gs = GhostStuffUsize { perm: write_in_progress_perm, token: write_in_progress_token };

        let (already_split, Tracked(already_split_perm)) = PAtomicBool::new(false);
        let tracked already_split_gs = GhostStuffUsize { perm: already_split_perm, token: already_split_token };

        // Initialize the queue
        Self {
            length,
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
                    prod.is_idle(),
                    cons.is_idle(),
                    prod.shared.instance@.length() == old(self).instance@.length(),
                    prod.shared.instance@.length() == old(self).instance@.length(),
                }, 
                Err(_) => true
            },
    {
        let tracked GhostStuffBool { perm: mut already_split_perm, token: mut already_split_token } = self.already_split_gs;
        let already_splitted = self.already_split.swap(Tracked(&mut already_split_perm), true);
        proof {
            if !already_splitted {
                let  = slf.instance.borrow().try_split(&mut already_split_token);
            }
        }

        if already_splitted {
            return Err("already splitted");
        }

        let tracked prod_token = slf.producer.borrow_mut().tracked_take();
        let tracked cons_token = slf.consumer.borrow_mut().tracked_take();

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
            token: grant_state_token,
        };
        let tracked buf_perm_inv = Shared::new(AtomicInvariant::new(self.instance, ghost_buffer_perm, 0));

        let tracked write_inv = Shared::new(AtomicInvariant::new((self.instance, &self.write), write_gs, 1));
        let tracked read_inv = Shared::new(AtomicInvariant::new((self.instance, &self.read), read_gs, 2));
        let tracked last_inv = Shared::new(AtomicInvariant::new((self.instance, &self.last), last_gs, 3));
        let tracked reserve_inv = Shared::new(AtomicInvariant::new((self.instance, &self.reserve), reserve_gs, 4));
        let tracked read_in_progress_inv = Shared::new(
            AtomicInvariant::new((self.instance, &self.read_in_progress), divide_gs, 5)
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
        &&& self.producer@ is None
        &&& self.wf()
    }
}

impl Producer {
    fn grant_exact(&mut self, sz: usize) -> (r: Result<GrantW, &'static str>)
        requires
            old(self).is_idle(),
        ensures
            self.wf(),
            match r {
                Ok(wgr) => {
                    &&& wgr.vbq.instance@.id() == self.vbq.instance@.id()
                    &&& wgr.producer@->0.instance_id() == old(self).producer@->0.instance_id()
                    &&& wgr.can_commit(sz as nat)
                },
                _ => true
            },
    {
        proof{
            assert(self.producer@->0.value().write_in_progress == false ==> 
                self.producer@->0.value().read_obs is None);
        }
        let tracked mut prod_token = self.producer.borrow_mut().tracked_take();

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

            proof { gs = GhostStuffUsize { perm: mut write_in_progress_perm, token: mut write_in_progress_token }; }
        });

        if is_write_in_progress {
            self.prod_token = Tracked(Some(prod_token));
            return Err("write in progress");
        }

        let write: usize;
        open_atomic_invariant!(self.shared.write_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut write_perm, token: mut write_token } = gs;

            write = self.shared.write.load(Tracked(&mut write_perm));
            proof {
                let _ = self.shared.instance.borrow().load_write_at_grant(&write_token, &prod_token);
            }

            proof { gs = GhostStuffUsize { perm: mut write_perm, token: mut write_token }; }
        });

        let read: usize;
        open_atomic_invariant!(self.shared.read_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut read_perm, token: mut read_token } = gs;

            read = self.shared.read.load(Tracked(&mut read_perm));
            proof {
                let _ = self.shared.instance.borrow().load_read_at_grant(&read_token, &mut prod_token);
            }

            proof { gs = GhostStuffUsize { perm: mut read_perm, token: mut read_token }; }
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

                    proof { gs = GhostStuffUsize { perm: mut write_in_progress_perm, token: mut write_in_progress_token }; }
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

                        proof { gs = GhostStuffUsize { perm: mut write_in_progress_perm, token: mut write_in_progress_token }; }
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
        // assert(start + sz <= self.vbq.length);

        // Safe write, only viewed by this task
        let tracked mut prod_points_to_raw: Option<PointsToRaw> = None;
        open_atomic_invariant!(slf.shared.buf_perm_inv.borrow().borrow() => bp => {
            let tracked GhostBufferPermission {
                pool: mut current_pool,
                token: mut grant_state_token,
            } = bp;

            /* ここら辺に pool に関するロジックが必要 */

            open_atomic_invariant!(self.shared.reserve_inv.borrow().borrow() => gs => {
                let tracked GhostStuffBool { perm: mut reserve_perm, token: mut reserve_token } = gs;
                let _ = self.shared.reserve.store(Tracked(&mut reserve_perm), start + sz);
                proof {
                    let _ = self.vbq.instance.borrow().do_reserve(start as nat, sz as nat, &mut reserve_token, &mut prod_token);
                }
                
                proof { gs = GhostStuffUsize { perm: mut reserve_perm, token: mut reserve_token }; }
            });

            /* ここら辺に pool に関するロジックが必要 */

            let tracked (points_to_raw_prod, mut pool_rest) = current_pool.split(set_int_range(
                self.buffer_ptr as int + grant_state_token.value().prod_start,
                self.buffer_ptr as int + grant_state_token.value().prod_end));
            proof {
                prod_points_to_raw = Some(points_to_raw_prod);
            }

            let tracked (_points_to_raw_cons, pool_rest) = pool_rest.split(set_int_range(
                self.buffer_ptr as int + grant_state_token.value().cons_start,
                self.buffer_ptr as int + grant_state_token.value().cons_end));

            proof { bp = GhostBufferPermission { pool: pool_rest, token: grant_state_token}; }
        });

        let tracked prod_points_to_raw = match prod_points_to_raw {
            Some(token) => token,
            None => {
                assert(false);
                proof_from_false()
            }
        };

        Ok (
            GrantW {
                buf: self.buffer_ptr,
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
                    buf_perm_inv: Tracked(self.shared.buf_perm_inv.clone()),

                    /* Atomic変数用不変条件 */
                    write_inv: Tracked(self.shared.write_inv.clone()),
                    read_inv: Tracked(self.shared.read_inv.clone()),
                    last_inv: Tracked(self.shared.last_inv.clone()),
                    reserve_inv: Tracked(self.shared.reserve_inv.clone()),
                    read_in_progress_inv: Tracked(self.shared.read_in_progress_inv.clone()),
                    write_in_progress_inv: Tracked(self.shared.write_in_progress_inv.clone()),

                    instance: Tracked(self.instance.borrow().clone()),
                },
                points_to_raw_token: Tracked(Some(prod_points_to_raw)),
                prod_token: Tracked(Some(prod_token)),
            }
        )
    }
}

struct GrantW {
    buffer_ptr: *mut u8,
    shared: VBBufferShared<'a>,
    points_to_raw_token: Tracked<Option<PointsToRaw>>,
    prod_token: Tracked<Option<VBQueue::producer>>,
}

impl GrantW {
    pub closed spec fn can_commit(&self, sz: nat) -> bool {
        &&& self.producer@ is Some
        &&& self.producer@->0.instance_id() == self.vbq.instance@.id()
        &&& self.producer@->0.value().is_idle() || self.producer@->0.value().is_granted(sz)
    }

    pub closed spec fn is_commited(&self) -> bool {
        &&& self.producer@ is None
    }
}

impl GrantW {
    fn commit(&mut self, used: usize) -> (prod_token: Tracked<VBQueue::producer>)
        requires
            old(self).can_commit(old(self).buf.len() as nat),
            used <= old(self).buf.len(),
        ensures
            self.is_commited(),
            prod_token@.instance_id() == old(self).producer@->0.instance_id(),
            prod_token@.instance_id() == self.vbq.instance@.id(),
            prod_token@.value().is_idle(),
    {
        // If there is no grant in progress, return early. This
        // generally means we are dropping the grant within a
        // wrapper structure
        let tracked prod_token = self.producer.borrow_mut().tracked_take();

        let is_write_in_progress: bool;
        open_atomic_invariant!(self.shared.write_in_progress_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut write_in_progress_perm, token: mut write_in_progress_token } = gs;

            is_write_in_progress = self.shared.write_in_progress.load(Tracked(&mut write_in_progress_perm));
                    
            proof {
                let _ = self.shared.instance.borrow().start_commit(self.buf.len() as nat, &mut write_in_progress_token, &prod_token);
                self.shared.instance.borrow().check_write_in_progress_equality(&write_in_progress_token, &prod_token);

                if !is_write_in_progress {
                    assert(prod_token.value().is_idle());
                };
            }

            proof { gs = GhostStuffUsize { perm: mut write_in_progress_perm, token: mut write_in_progress_token }; }
        });

        if !is_write_in_progress {
            return Tracked(prod_token);
        }

        // Writer component. Must never write to READ,
        // be careful writing to LAST

        // Saturate the grant commit
        let len = self.buf.len();
        let used = if len <= used { len } else { used }; // min の代用。

        let write: usize;
        open_atomic_invariant!(self.shared.write_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut write_perm, token: mut write_token } = gs;
            write = self.shared.write.load(Tracked(&mut write_perm));

            proof {
                let _ = self.shared.instance.borrow().check_write_equality(&write_token, &prod_token);
                let _ = self.shared.instance.borrow().load_write_at_commit(&write_token, &prod_token);
            }

            proof { gs = GhostStuffUsize { perm: mut write_perm, token: mut write_token }; }
        });

        open_atomic_invariant!(self.shared.reserve_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut reserve_perm, token: mut reserve_token } = gs;
            write = self.shared.reserve.fetch_sub(Tracked(&mut reserve_perm), len - used);

            proof {
                self.shared.instance.borrow().check_reserve_equality(&reserve_token, &prod_token);
                assert(prod_token.value().grant_sz() == len as int);
                assert(prod_token.value().reserve >= len as int);
                assert(prod_token.value().reserve == reserve_token.value());
                assert(usize::MIN as int <= prod_token.value().reserve - (len - used));
                let _ = self.shared.instance.borrow().sub_reserve_at_commit((len - used) as nat, &mut reserve_token, &mut prod_token);
            }

            proof { gs = GhostStuffUsize { perm: mut reserve_perm, token: mut reserve_token }; }
        });

        let max = self.vbq.length as usize;
        let last: usize;
        open_atomic_invariant!(self.shared.last.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut last_perm, token: mut last_token } = gs;

            last = self.shared.last.load(Tracked(&mut last_perm));
            proof {
                let _ = self.shared.instance.borrow().load_last_at_commit(&last_token, &mut prod_token);
                self.shared.instance.borrow().check_last_equality(&last_token, &prod_token);
            }

            proof { gs = GhostStuffUsize { perm: mut last_perm, token: mut last_token }; }
        });


        let new_write: usize;
        open_atomic_invariant!(self.shared.reserve.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut reserve_perm, token: mut reserve_token } = gs;

            new_write = self.shared.reserve.load(Tracked(&mut reserve_perm));
            proof {
                let _ = self.shared.instance.borrow().load_reserve_at_commit(&last_token, &mut prod_token);
                self.shared.instance.borrow().check_last_equality(&reserve_token, &prod_token);
                assert(reserve_token.value() == prod_token.value().reserve);
            }

            proof { gs = GhostStuffUsize { perm: mut reserve_perm, token: mut reserve_token }; }
        });

        if (new_write < write) && (write != max) {
            // We have already wrapped, but we are skipping some bytes at the end of the ring.
            // Mark `last` where the write pointer used to be to hold the line here
            open_atomic_invariant!(self.shared.last_inv.borrow().borrow() => gs => {
                let tracked GhostStuffBool { perm: mut last_perm, token: mut last_token } = gs;
                let _ = self.shared.last.store(Tracked(&mut last_perm), write);
                    
                proof {
                    let _ = self.vbq.instance.borrow().update_last_by_write_at_commit(write as nat, &mut last_token, &mut prod_token);
                }
                
                proof { gs = GhostStuffUsize { perm: mut last_perm, token: mut last_token }; }
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
                let tracked GhostStuffBool { perm: mut last_perm, token: mut last_token } = gs;
                let _ = self.shared.last.store(Tracked(&mut last_perm), max);
                    
                proof {
                    let _ = self.vbq.instance.borrow().update_last_by_max_at_commit(&mut last_token, &mut prod_token);
                    assert(prod_token.value().last == max as nat);
                }
                
                proof { gs = GhostStuffUsize { perm: mut last_perm, token: mut last_token }; }
            });
        }
        // else: If new_write == last, either:
        // * last == max, so no need to write, OR
        // * If we write in the end chunk again, we'll update last to max next time
        // * If we write to the start chunk in a wrap, we'll update last when we
        //     move write backwards

        // Write must be updated AFTER last, otherwise read could think it was
        // time to invert early!
        let tracked mut prod_points_to_raw: Option<PointsToRaw> = None;
        open_atomic_invariant!(slf.shared.buf_perm_inv.borrow().borrow() => bp => {
            let tracked GhostBufferPermission {
                pool: mut current_pool,
                token: mut grant_state_token,
            } = bp;

            /* ここら辺に pool に関するロジックが必要 */

            open_atomic_invariant!(self.shared.write_inv.borrow().borrow() => gs => {
                let tracked GhostStuffBool { perm: mut write_perm, token: mut write_token } = gs;
                let _ = self.shared.write.store(Tracked(&mut write_perm), new_write);
                proof {
                    let _ = self.shared.instance.borrow().check_write_equality(&write_token, &prod_token);
                    let _ = self.shared.instance.borrow().store_write_at_commit(new_write as nat, &mut write_token, &mut prod_token);
                }
                
                proof { gs = GhostStuffUsize { perm: mut write_perm, token: mut write_token }; }
            });

            /* ここら辺に pool に関するロジックが必要 */

            let tracked (points_to_raw_prod, mut pool_rest) = current_pool.split(set_int_range(
                self.buffer_ptr as int + grant_state_token.value().prod_start,
                self.buffer_ptr as int + grant_state_token.value().prod_end));
            proof {
                prod_points_to_raw = Some(points_to_raw_prod);
            }

            let tracked (_points_to_raw_cons, pool_rest) = pool_rest.split(set_int_range(
                self.buffer_ptr as int + grant_state_token.value().cons_start,
                self.buffer_ptr as int + grant_state_token.value().cons_end));

            proof { bp = GhostBufferPermission { pool: pool_rest, token: grant_state_token}; }
        });

        // Allow subsequent grants
        open_atomic_invariant!(self.shared.write_in_progress_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut write_in_progress_perm, token: mut write_in_progress_token } = gs;

            is_write_in_progress = self.shared.write_in_progress.store(Tracked(&mut write_in_progress_perm), false);

            proof {
                assert(write_in_progress_token.value() == false);
            }

            proof { gs = GhostStuffUsize { perm: mut write_in_progress_perm, token: mut write_in_progress_token }; }
        });

        return Tracked(prod_token);
    }

    /// Configures the amount of bytes to be commited on drop.
    pub fn to_commit(&mut self, amt: usize) {
        self.to_commit = self.buf.len().min(amt);
    }
}

pub struct Consumer<'a> {
    buffer_ptr: *mut u8,
    shared: VBBufferShared<'a>,
    cons_token: Tracked<Option<VBQueue::consumer>>,
}

impl<'a> Consumer<'a> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.cons_token@ is Some
        &&& self.cons_token@->0.instance_id() == self.shared.instance@.id()
        &&& self.buffer_ptr@.provenance == self.shared.instance@.provenance()
        &&& self.buffer_ptr as int == self.shared.instance@.base_addr()
        &&& self.shared.wf()
 
    }
    pub closed spec fn is_idle(&self) -> bool {
        &&& self.cons_token@->0.value().is_idle()
        &&& self.wf()
    }
}

impl Consumer {
    fn read(&mut self) ->  (r: Result<GrantR, &'static str>)
        requires
            old(self).wf(),
            old(self).is_idle(),
        ensures
            self.wf(),
            match r {
                Ok(rgr) => {
                    &&& rgr.vbq.instance@.id() == self.vbq.instance@.id()
                    &&& rgr.consumer@->0.instance_id() == old(self).consumer@->0.instance_id()
                    &&& rgr.releasable(rgr.buf.len() as nat)
                },
                _ => true,
            },
    {
        let tracked mut cons_token = self.consumer.borrow_mut().tracked_take();

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

            proof { gs = GhostStuffUsize { perm: mut read_in_progress_perm, token: mut read_in_progress_token }; }
        });

        if is_read_in_progress {
            self.cons_token = Traced(Some(cons_token));
            return Err("read in progress");
        }

        let write: usize;
        open_atomic_invariant!(self.shared.write_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut write_perm, token: mut write_token } = gs;

            write = self.shared.write.load(Tracked(&mut write_perm));
            proof {
                let _ = self.shared.instance.borrow().load_write_at_read(&write_token, &cons_token);
            }

            proof { gs = GhostStuffUsize { perm: mut write_perm, token: mut write_token }; }
        });

        let last: usize;
        open_atomic_invariant!(self.shared.last.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut last_perm, token: mut last_token } = gs;

            last = self.shared.last.load(Tracked(&mut last_perm));
            proof {
                let _ = self.shared.instance.borrow().load_last_at_read(&last_token, &mut cons_token);
            }

            proof { gs = GhostStuffUsize { perm: mut last_perm, token: mut last_token }; }
        });

        let mut read: usize
        open_atomic_invariant!(self.shared.read_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut read_perm, token: mut read_token } = gs;

            read = self.shared.read.load(Tracked(&mut read_perm));
            proof {
                let _ = self.shared.instance.borrow().load_read_at_read(&read_token, &cons_token);
                self.shared.instance.borrow().check_read_is_le_last_in_inverted(&read_token, &cons_token);
                assert(write < read_token.value() ==> read_token.value() <= last);
            }

            proof { gs = GhostStuffUsize { perm: mut read_perm, token: mut read_token }; }
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
            open_atomic_invariant!(self.shared.read_inv.borrow().borrow() => gs => {
                let tracked GhostStuffBool { perm: mut read_perm, token: mut read_token } = gs;
                // TODO: ここでも permission の変更が必要?
                // ここで read が wrap する。
                // read == last の状態で、かつ、write < read なので、inverted 状態になる。    
                read = self.shared.read.store(Tracked(&mut read_perm), 0);
                proof {
                    let _ = self.shared.instance.borrow().check_read_equality(&read_token, &mut prod_token);
                    let _ = self.shared.instance.borrow().wrap_read(&mut read_token, &mut cons_token);
                    // ↑をまたぐと
                    // read == 0 になるので not inverted に切り替わる
                    // この瞬間に producer はまだ inverted
                    // read == 0 read_obs == 9 write == 9 で last は 10 のとき、not inverted 判断になる。
                }

                proof { gs = GhostStuffUsize { perm: mut read_perm, token: mut read_token }; }
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
            open_atomic_invariant!(self.shared.read_in_progress_inv.borrow().borrow() => gs => {
                let tracked GhostStuffBool { perm: mut read_in_progress_perm, token: mut read_in_progress_token } = gs;

                let _ = self.shared.read_in_progress.store(Tracked(&mut read_in_progress_perm), false);
                proof {
                    let _ = self.shared.instance.borrow().read_fail(&mut read_in_progress_token, &mut cons_token);
                }

                proof { gs = GhostStuffUsize { perm: mut read_in_progress_perm, token: mut read_in_progress_token }; }
            });
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
        assert(cons_token.value().grant_sz() == sz);
        assert(cons_token.value().read == cons_token.value().grant_start());
        assert(cons_token.value().read + sz == cons_token.value().grant_end());
        Ok(
            GrantR {
                buf: self.buffer_ptr,
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
                    buf_perm_inv: Tracked(self.shared.buf_perm_inv.clone()),

                    /* Atomic変数用不変条件 */
                    write_inv: Tracked(self.shared.write_inv.clone()),
                    read_inv: Tracked(self.shared.read_inv.clone()),
                    last_inv: Tracked(self.shared.last_inv.clone()),
                    reserve_inv: Tracked(self.shared.reserve_inv.clone()),
                    read_in_progress_inv: Tracked(self.shared.read_in_progress_inv.clone()),
                    write_in_progress_inv: Tracked(self.shared.write_in_progress_inv.clone()),

                    instance: Tracked(self.instance.borrow().clone()),
                },
                points_to_raw_token: Tracked(Some(cons_points_to_raw)),
                consumer: Tracked(Some(cons_token)),
            }
        )
    }
}

struct GrantR {
    buffer_ptr: *mut u8,
    shared: VBBufferShared<'a>,
    points_to_raw_token: Tracked<Option<PointsToRaw>>,
    cons_token: Tracked<Option<VBQueue::consumer>>,
}

impl GrantR {
    pub closed spec fn releasable(&self, sz: nat) -> bool {
        &&& self.vbq.wf()
        &&& self.buf.len() as nat == sz
        &&& self.consumer@ is Some
        &&& self.consumer@->0.instance_id() == self.vbq.instance@.id()
        &&& self.consumer@->0.value().is_idle() || self.consumer@->0.value().is_granted(sz)
    }

    pub closed spec fn released(&self) -> bool {
        &&& self.vbq.wf()
        &&& self.consumer@ is None
    }
}

impl GrantR {
    fn release(&mut self,
        used: usize
    ) -> (cons_token: Tracked<VBQueue::consumer>)
        requires
            used <= old(self).buf.len(),
            old(self).releasable(old(self).buf.len() as nat),
        ensures
            self.vbq.wf(),
            self.released(),
            cons_token@.instance_id() == old(self).consumer@->0.instance_id(),
            cons_token@.instance_id() == self.vbq.instance@.id(),
            cons_token@.value().is_idle(),
    {
        let tracked mut cons_token = self.consumer.borrow_mut().tracked_take();

        // If there is no grant in progress, return early. This
        // generally means we are dropping the grant within a
        // wrapper structure
        let is_read_in_progress: bool;
        open_atomic_invariant!(self.shared.read_in_progress_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut read_in_progress_perm, token: mut read_in_progress_token } = gs;

            is_read_in_progress = self.shared.read_in_progress.swap(Tracked(&mut read_in_progress_perm), true);

            proof {
                if !is_read_in_progress {
                    let _ = self.vbq.instance.borrow().start_release(&mut read_in_progress_token, &mut cons_token);
                }
            }

            proof { gs = GhostStuffUsize { perm: mut read_in_progress_perm, token: mut read_in_progress_token }; }
        });

        if !is_read_in_progress {
            return Tracked(cons_token);
        }

        // This should always be checked by the public interfaces
        // debug_assert!(used <= self.buf.len());

        // This should be fine, purely incrementing
        open_atomic_invariant!(self.shared.read_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut read_perm, token: mut read_token } = gs;
            write = self.shared.reserve.fetch_sub(Tracked(&mut read_perm), len - used);

            proof {
                let _ = self.shared.instance.borrow().check_read_equality(&read_token, &cons_token);
                let _ = self.shared.instance.borrow().check_consumer_obs_in_range(&mut cons_token);

                let _ = self.shared.instance.borrow().add_read_at_release(used as nat, &mut read_token, &mut cons_token);
            }

            proof { gs = GhostStuffUsize { perm: mut reserve_perm, token: mut reserve_token }; }
        });

        open_atomic_invariant!(self.shared.read_in_progress_inv.borrow().borrow() => gs => {
            let tracked GhostStuffBool { perm: mut read_in_progress_perm, token: mut read_in_progress_token } = gs;

            let _ = self.shared.read_in_progress.store(Tracked(&mut read_in_progress_perm), false);
            proof {
                let _ = self.shared.instance.borrow().end_release(&mut read_in_progress_token, &mut cons_token);
            }

            proof { gs = GhostStuffUsize { perm: mut read_in_progress_perm, token: mut read_in_progress_token }; }
        });

        return Tracked(cons_token);
    }

    /// Configures the amount of bytes to be released on drop.
    pub fn to_release(&mut self, amt: usize) {
        self.to_release = self.buf.len().min(amt);
    }
}

fn main() {
    let vbuf = VBBuffer::new(6);
    let (mut prod, mut cons) = match vbuf.try_split() {
        Ok((p, c)) => (p, c),
        Err(_) => return,
    };

    // ---- phase 1: write 5, read 5 (advance read to 5) ----
    {
        let mut wgr = match prod.grant_exact(5) {
            Ok(w) => w,
            Err(_) => return,
        };
        if wgr.buf.len() != 5 { return; }
        let Tracked(prod_token) = wgr.commit(5);
        assert(prod_token.instance_id() == wgr.vbq.instance@.id());
        assert(prod_token.instance_id() == prod.vbq.instance@.id());
        assert(prod_token.value().is_idle());

        prod.producer = Tracked(Some(prod_token));

        let mut rgr = match cons.read() {
            Ok(r) => r,
            Err(_) => return,
        };
        if rgr.buf.len() != 5 { return; }
        let Tracked(cons_token) = rgr.release(5);
        cons.consumer = Tracked(Some(cons_token));
    }

    // ---- phase 2: wrap with "skip end chunk" (write=5, read=5, sz=4 -> start=0) ----
    // This should set last := old write (=5) during commit, then write := 4.
    {
        let mut wgr = match prod.grant_exact(4) {
            Ok(w) => w,
            Err(_) => return,
        };
        if wgr.buf.len() != 4 { return; }
        let Tracked(prod_token) = wgr.commit(4);

        prod.producer = Tracked(Some(prod_token));

        let mut rgr = match cons.read() {
            Ok(r) => r,
            Err(_) => return,
        };
        if rgr.buf.len() != 4 { return; }
        let Tracked(cons_token) = rgr.release(4);
        cons.consumer = Tracked(Some(cons_token));
    }

    // ---- phase 3: unlock last back to max (last was 5, now new_write should become 6) ----
    {
        let mut wgr = match prod.grant_exact(2) {
            Ok(w) => w,
            Err(_) => return,
        };
        if wgr.buf.len() != 2 { return; }
        let Tracked(prod_token) = wgr.commit(2);

        prod.producer = Tracked(Some(prod_token));

        let mut rgr = match cons.read() {
            Ok(r) => r,
            Err(_) => return,
        };
        if rgr.buf.len() != 2 { return; }
        let Tracked(cons_token) = rgr.release(2);
        cons.consumer = Tracked(Some(cons_token));
    }

    // ---- phase 4: wrap when old write == max (write=6, read=6, sz=1 -> start=0) ----
    // This time "skip" branch should NOT trigger because pre.write == max.
    {
        let mut wgr = match prod.grant_exact(1) {
            Ok(w) => w,
            Err(_) => return,
        };
        if wgr.buf.len() != 1 { return; }
        let Tracked(prod_token) = wgr.commit(1);

        prod.producer = Tracked(Some(prod_token));

        let mut rgr = match cons.read() {
            Ok(r) => r,
            Err(_) => return,
        };
        if rgr.buf.len() != 1 { return; }
        let Tracked(cons_token) = rgr.release(1);
        cons.consumer = Tracked(Some(cons_token));
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
