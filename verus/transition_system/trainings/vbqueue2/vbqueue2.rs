use state_machines_macros::tokenized_state_machine;
//use vstd::atomic_ghost::*;
//use vstd::raw_ptr::*;
use vstd::{prelude::*, *};
//use vstd::layout::*;
//use std::sync::Arc;

verus! {
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

        // Represents the observed read var by producer
        #[sharding(variable)]
        pub producer_read_obs: Option<nat>,

        // Represents the observed write var by consumer
        #[sharding(variable)]
        pub consumer_write_obs: Option<nat>,

        // Represents the observed last var by consumer
        #[sharding(variable)]
        pub consumer_last_obs: Option<nat>,
    }

    #[invariant]
    pub fn valid_read_obs_is_none_implies_no_grant(&self) -> bool {
        self.producer_read_obs is None ==> self.write == self.reserve
    }

    #[invariant]
    pub fn valid_write_max_implies_last_max(&self) -> bool {
        // write が終端(length)にいるなら、last も終端でなければならない
        self.write == self.length ==> self.last == self.length
    }

    #[invariant]
    pub fn valid_order_from_producer_view(&self) -> bool {
        match self.producer_read_obs {
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
    pub fn valid_consumer_local_state_order(&self) -> bool {
        match (self.consumer_write_obs, self.consumer_last_obs) {
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
            
            init producer_read_obs = None;
            init consumer_write_obs = None;
            init consumer_last_obs = None;
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
            require(pre.producer_read_obs is None);
            assert(pre.write == pre.reserve);

            update write_in_progress = true;
        }
    }

    transition!{
        load_write_at_grant() {
            require(pre.write_in_progress == true);
            require(pre.producer_read_obs is None);
        }
    }

    transition!{
        load_read_at_grant() {
            require(pre.write_in_progress == true);
            require(pre.producer_read_obs is None);
            assert(pre.write == pre.reserve);

            update producer_read_obs = Some(pre.read);
        }
    }

    transition!{
        do_reserve(start: nat, sz: nat) {
            require(pre.write_in_progress == true);
            require(pre.producer_read_obs is Some);
            let new_reserve = start + sz;
            let read_obs = pre.producer_read_obs->Some_0;
            require(
                {
                    // not inverted & reserve not wrap
                    ||| read_obs <= pre.write <= new_reserve <= pre.length
                    // not inverted & reserve wrap
                    ||| new_reserve < read_obs <= pre.write <= pre.length
                    // inverted (write < read_obs) & read not wrap
                    ||| pre.write <= new_reserve < read_obs /*<= pre.last */ <= pre.length
                }
            );

            update reserve = start + sz;
        }
    }

    transition!{
        grant_fail(sz: nat) {
            require(pre.write_in_progress == true);
            require(pre.write == pre.reserve);

            update write_in_progress = false;
            update producer_read_obs = None;
        }
    }

    transition!{
        start_commit() {
            require(pre.write_in_progress == true);
        }
    }

    transition!{
        load_write_at_commit() {
            require(pre.write_in_progress == true);
            require(pre.producer_read_obs is Some);
        }
    }
 
    transition!{
        sub_reserve_at_commit(commited: nat) {
            require(pre.write_in_progress == true);
            require(pre.producer_read_obs is Some);
            require(pre.reserve >= commited);

            let grant_start = if pre.write <= pre.reserve {pre.write} else {0};
            require(pre.reserve - grant_start >= commited);

            let new_reserve = (pre.reserve - commited) as nat;

            update reserve = new_reserve;
        }
    }


    transition!{
        load_last_at_commit() {
            require(pre.write_in_progress == true);
        }
    }

    transition!{
        load_reserve_at_commit() {
            require(pre.write_in_progress == true);
        }
    }

    transition!{
        update_last_by_write_at_commit() {
            require(pre.write_in_progress == true);
            require(pre.reserve < pre.write && pre.write != pre.length);

            update last = pre.write; // write で last を更新する
        }
    }

    transition!{
        update_last_by_max_at_commit() {
            require(pre.write_in_progress == true);
            require(pre.reserve > pre.last);

            update last = pre.length; // max で last を更新する
        }
    }

    transition!{
        store_write_at_commit() {
            require(pre.write_in_progress == true);
            require(pre.producer_read_obs is Some);

            // 以下の require がないと
            // ||| self.reserve < read_obs <= self.read <= self.write <= self.length のケースで write が巻き戻ったあとの、
            // valid_producer_local_state_order の invariant が保たれることを示せない。
            require(pre.reserve < pre.write ==> pre.write == pre.last);
            let read_obs = pre.producer_read_obs->Some_0;
            let new_write = pre.reserve;

            require(new_write == pre.length ==> pre.last == pre.length);

            require(
                {
                    // not inverted & reserve not wrap
                    ||| read_obs <= new_write == pre.reserve <= pre.length
                    // inverted (write < read_obs) & read not wrap
                    ||| new_write == pre.reserve < read_obs <= pre.last <= pre.length
                }
            );
            update write = new_write;
        }
    }

    transition!{
        commit_end() {
            require(pre.write_in_progress == true);
            require(pre.reserve == pre.write);

            update write_in_progress = false;
            update producer_read_obs = None;
        }
    }

    transition!{
        start_read() {
            require(pre.read_in_progress == false);
            require(pre.consumer_write_obs is None);
            require(pre.consumer_last_obs is None);

            update read_in_progress = true;
        }
    }

    transition!{
        load_write_at_read() {
            require(pre.read_in_progress == true);
            require(pre.consumer_write_obs is None);
            require(pre.consumer_last_obs is None);

            update consumer_write_obs = Some(pre.write);
        }
    }

    transition!{
        load_last_at_read() {
            require(pre.read_in_progress == true);
            require(pre.consumer_write_obs is Some);
            require(pre.consumer_last_obs is None);

            update consumer_last_obs = Some(pre.last);
        }
    }

    transition!{
        load_read_at_read() {
            require(pre.read_in_progress == true);
            require(pre.consumer_write_obs is Some);
            require(pre.consumer_last_obs is Some);
        }
    }
 
    transition!{
        wrap_read() {
            require(pre.read_in_progress == true);
            require((pre.read == pre.consumer_last_obs->Some_0) && (pre.consumer_write_obs->Some_0 < pre.read));

            update read = 0;
        }
    }

    transition!{
        read_fail() {
            require(pre.read_in_progress == true);

            update read_in_progress = false;
            update consumer_write_obs = None;
            update consumer_last_obs = None;
        }
    }


    transition!{
        start_release() {
            require(pre.read_in_progress == true);
            require(pre.consumer_write_obs is Some);
            require(pre.consumer_last_obs is Some);
        }
    }

    transition!{
        add_read_at_release(used: nat) {
            require(pre.read_in_progress == true);
            require(pre.consumer_write_obs is Some);
            require(pre.consumer_last_obs is Some);

            let write_obs = pre.consumer_write_obs->Some_0;
            let last_obs = pre.consumer_last_obs->Some_0;
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
        }
    }
    
    transition!{
        release_end() {
            require(pre.read_in_progress == true);

            update read_in_progress = false;
        }
    }

    #[inductive(try_split)]
    fn try_split_inductive(pre: Self, post: Self) { }
    
    #[inductive(start_grant)]
    fn start_grant_inductive(pre: Self, post: Self) { }
    
    #[inductive(load_write_at_grant)]
    fn load_write_at_grant_inductive(pre: Self, post: Self) { }
    
    #[inductive(load_read_at_grant)]
    fn load_read_at_grant_inductive(pre: Self, post: Self) { }
    
    #[inductive(do_reserve)]
    fn do_reserve_inductive(pre: Self, post: Self, start: nat, sz: nat) { }
    
    #[inductive(grant_fail)]
    fn grant_fail_inductive(pre: Self, post: Self, sz: nat) { }
    
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
    fn update_last_by_write_at_commit_inductive(pre: Self, post: Self) { }
    
    #[inductive(update_last_by_max_at_commit)]
    fn update_last_by_max_at_commit_inductive(pre: Self, post: Self) { }
    
    #[inductive(store_write_at_commit)]
    fn store_write_at_commit_inductive(pre: Self, post: Self) { }
    
    #[inductive(commit_end)]
    fn commit_end_inductive(pre: Self, post: Self) { }
    
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
    
    #[inductive(release_end)]
    fn release_end_inductive(pre: Self, post: Self) { }
}}

fn main() {}
}
