use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::prelude::*;
use vstd::thread::*;
use vstd::*;

verus! {

tokenized_state_machine!(
    TransferAtoB {
        fields {
            #[sharding(variable)]
            pub a: int,

            #[sharding(variable)]
            pub b: int,

            #[sharding(variable)]
            pub waiting_increment: int,
        }

        #[invariant]
        pub fn main_invariant(&self) -> bool {
            self.a + self.b + self.waiting_increment == 10
        }

        init!{
            initialize() {
                init a = 1;
                init b = 0;
                init waiting_increment = 0;
            }
        }

        transition!{
            tr_dec_a() {
                require(pre.a > 0);
                update a = pre.a - 1;
                update waiting_increment = pre.waiting_increment + 1;
            }
        }

        transition!{
            tr_inc_b() {
                require(pre.waiting_increment > 0);
                update b = pre.b + 1;
                update waiting_increment = pre.waiting_increment - 1;
            }
        }

        property!{
            decrement_will_not_underflow_u32() {
                assert 0 <= pre.a;
            }
        }

        property!{
            increment_will_not_overflow_u32() {
                assert 0 <= pre.b < 0xffff_ffff;
            }
        }

        property!{
            finalize(updated: bool) {
                require(pre.a == 0);
                require(pre.b == 1);
            }
        }
        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(tr_dec_a)]
        fn tr_dec_a_inductive(pre: Self, post: Self) { }

        #[inductive(tr_inc_b)]
        fn tr_inc_b_inductive(pre: Self, post: Self) { }
    }
);

struct_with_invariants! {
    pub struct Global {
        pub atomic_a: AtomicU32<_, TransferAtoB::a, _>,
        pub atomic_b: AtomicU32<_, TransferAtoB::b, _>,
        pub instance: Tracked<TransferAtoB::Instance>,
    }

    spec fn wf(&self) -> bool {
        invariant on atomic_a with (instance) is (v: u32, g: TransferAtoB::a) {
            g.instance_id() == instance@.id() && g.value() == v as int
        }

        invariant on atomic_b with (instance) is (v: u32, g: TransferAtoB::b) {
            g.instance_id() == instance@.id() && g.value() == v as int
        }
    }
}

fn main() {
    // initialize protocol instance
    let tracked (
        Tracked(instance),
        Tracked(a_token),
        Tracked(b_token),
        Tracked(waiting_increment_token),
    ) = TransferAtoB::Instance::initialize();

    let tr_instance: Tracked<TransferAtoB::Instance> = Tracked(instance.clone());
    let atomic_a = AtomicU32::new(Ghost(tr_instance), 1, Tracked(a_token));
    let atomic_b = AtomicU32::new(Ghost(tr_instance), 0, Tracked(b_token));
    let global = Global {
        atomic_a,
        atomic_b,
        instance: Tracked(instance),
    };
    let global_arc = Arc::new(global);

    // Spawn threads
    let global_arc1 = global_arc.clone();
    let join_handle1 = spawn(
        (move || -> (ret: (Tracked<(TransferAtoB::a, TransferAtoB::b, bool)>))
            ensures
                ret@.0.instance_id() == instance.id() && ret@.1.instance_id() == instance.id() ,
            {
                let globals = &*global_arc1;
                let tracked mut a_token = a_token; // moved
                let tracked mut b_token = b_token; // moved
                let current_a =
                    atomic_with_ghost!(&globals.atomic_a => load();
                    returning ret;
                    ghost a => {
                        globals.instance.borrow().decrement_will_not_underflow_u32(&mut a);
                    }
                );

                let _ =
                    atomic_with_ghost!(&globals.atomic_a => compare_exchange(current_a, current_a - 1);
                        update old_val -> new_val;
                        returning ret;
                        ghost a => {
                            match ret {
                                Result::Ok(_) => {
                                    assert(old_val == current_a);
                                    assert(new_val == current_a - 1);
                                    globals.instance.borrow().decrement_will_not_underflow_u32(&mut a);
                                    globals.instance.borrow().tr_dec_a(&mut c, &mut a_token); // atomic decrement
                                    updated = true;

                                    let current_b =
                                        atomic_with_ghost!(&globals.atomic_b => fetch_add(1);
                                        returning ret;
                                        ghost b => {
                                            globals.instance.borrow().increment_will_not_overflow_u32(&mut b);
                                            globals.instance.borrow().tr_inc_b(&mut c, &mut b_token); // atomic increment
                                        }
                                    );
                                },
                                Result::Err(_) => {
                                    assert(old_val == new_val);
                                    updated = false;
                                }
                            }
                        }
                );
                Tracked((a_token, b_token, updated))
            }),
    );

    let tracked mut t;
    match join_handle1.join() {
        Result::Ok(thread_ret) => {
            proof {
                t = thread_ret.get();
            }
        },
        _ => {
            return ;
        },
    };

    // thread を join して、atomicを再度ロードする
    let global = &*global_arc;
    let x =
        atomic_with_ghost!(&global.atomic_a => load();
        ghost c => {
            instance.finalize(t.1, &c, &t.0);
        })
    ;

    assert(t.1 && x == 1 || !t.1);
}
}
