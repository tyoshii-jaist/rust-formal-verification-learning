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

            #[sharding(map)]
            pub decrement_ticket: Map<int, bool>, // tid vs whether the thread has a decrement ticket
        }

        #[invariant]
        pub fn main_invariant(&self) -> bool {
            self.a + self.b + self.decrement_ticket.dom().filter(|&(_, v)| *v).len() == TOTAL
        }

        init!{
            initialize() {
                init a = TOTAL;
                init b = 0;
                init decrement_ticket = Map::new();
            }
        }

        transition!{
            tr_decrement_a(thread_id: int, current_a: int) {
                require(current_a == pre.a);
                require(pre.a > 0);
                require(!decrement_ticket.dom().contains(thread_id));
                update a = pre.a - 1;
                add decrement_ticket += [thread_id => true];
            }
        }

        transition!{
            tr_increment_b(thread_id: int) {
                require(decrement_ticket[thread_id]);
                update b = pre.b + 1;
                remove decrement_ticket -= [thread_id => true];
            }
        }

        property!{
            finalize() {
                assert pre.a == 0;
                assert pre.b == TOTAL;
                assert pre.counter == 2;
            }
        }
    }
}

struct_with_invariants! {
    pub struct Global {
        pub a_atomic: AtomicU32<_, TransferAtoB::a, _>,
        pub b_atomic: AtomicU32<_, TransferAtoB::b, _>,
        pub instance: Tracked<TransferAtoB>,
    }

    spec fn wf(&self) -> bool {
        invariant on a_atomic with (instance) is (v: u32, g: TransferAtoB::a) {
            g.instance_id() == instance@.id()
            && g.value() == v as int
        }

        invariant on b_atomic with (instance) is (v: u32, g: TransferAtoB::b) {
            g.instance_id() == instance@.id()
            && g.value() == v as int
        }
    }
}

fn main() {
    // initialize protocol instance
    let tracked (
        Tracked(instance),
        Tracked(a_token),
        Tracked(b_token),
        Tracked(decrement_ticket_token),
    ) = TransferAtoB::initialize();

    let tr_instance: Tracked<TransferAtoB::Instance> = Tracked(instance.clone());
    let a_atomic = AtomicU32::new(Ghost(tr_instance), 0, Tracked(a_token));
    let b_atomic = AtomicU32::new(Ghost(tr_instance), 0, Tracked(b_token));
    let global = Global {
        a_atomic,
        b_atomic,
        instance: Tracked(instance),
    };
    let global_arc = Arc::new(global);

    // Spawn threads
    let join_handle1 = spawn(
        (move || -> (new_a_token: Tracked<TransferAtoB::a>, new_b_token: Tracked<TransferAtoB::b>, new_decrement_ticket_token: Tracked<TransferAtoB::decrement_ticket>)
            ensures
                new_a_token@.instance_id() == instance@.id() && new_b_token@.instance_id() == instance@.id() && new_decrement_ticket_token@.instance_id() == instance@.id(),
            {
                let tracked mut a_token = a_token;
                let tracked mut b_token = b_token;
                let tracked mut decrement_ticket_token = decrement_ticket_token;
                let thread_id = 1; // 固定値
                let globals = &*global_arc;

                loop {
                    let current_a = atomic_with_ghost!(&globals.a_atomic => load();
                        ghost c => {}
                    );
                    if current_a == 0 {
                        break;
                    }

                    let res = atomic_with_ghost!(&globals.a_atomic => compare_exchange(current_a, current_a - 1);
                        ghost c => {
                            globals.instance.borrow().tr_decrement_a(thread_id, current_a as int, &mut c, &mut a_token, &mut decrement_ticket_token);
                            globals.instance.borrow().tr_increment_b(thread_id, &mut c, &mut b_token, &mut decrement_ticket_token);
                        }
                    );


                };

                Tracked(local_a_token, local_b_token, local_decrement_ticket_token)
            }
        )
    );
}
}
