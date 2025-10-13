use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::prelude::*;
use vstd::thread::*;
use vstd::*;

verus! {
const TOTAL = 10;

tokenized_state_machine! {
    TransferAtoB {
        fields {
            #[sharding(variable)]
            pub a: int,

            #[sharding(variable)]
            pub b: int,

            #[sharding(variable)]
            pub b_increment_reserve: int, これは各スレッドごとのチケットにすべき。
        }

        #[invariant]
        pub fn main_invariant(&self) -> bool {
            self.a + self.b + self.b_increment_reserve == TOTAL
        }

        init!{
            initialize() {
                init a = TOTAL;
                init b = 0;
                init b_increment_reserve = 0;
            }
        }

        transition!{
            tr_decrement_a(current_a: int) {
                require(current_a == pre.a);
                require(pre.a > 0);
                update a = pre.a - 1;
                update b_increment_reserve = pre.b_increment_reserve + 1;
            }
        }
    } 
}
}