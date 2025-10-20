use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::prelude::*;
use vstd::thread::*;
use vstd::*;

verus! {

tokenized_state_machine!(
    CompareAndExchangeTest {
        fields {
            #[sharding(variable)]
            pub counter: int,

            #[sharding(variable)]
            pub cae_a: bool,
        }

        #[invariant]
        pub fn main_invariant(&self) -> bool {
            self.counter == (if self.cae_a { 1 as int} else {0} )
        }

        init!{
            initialize() {
                init counter = 0;
                init cae_a = false;
            }
        }

        transition!{
            tr_inc_a() {
                require(!pre.cae_a);
                update counter = pre.counter + 1;
                update cae_a = true;
            }
        }

        property!{
            already_incremented() {
                require(pre.cae_a);
                assert pre.counter == 1;
            }
        }

        property!{
            increment_will_not_overflow_u32() {
                assert 0 <= pre.counter < 0xffff_ffff;
            }
        }

        property!{
            finalize(updated: bool) {
                require((updated && pre.cae_a) || !updated);
                assert ((updated && pre.counter == 1) || !updated);
            }
        }
        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(tr_inc_a)]
        fn tr_inc_a_inductive(pre: Self, post: Self) { }
    }
);

struct_with_invariants! {
    pub struct Global {
        pub atomic_counter: AtomicU32<_, CompareAndExchangeTest::counter, _>,
        pub instance: Tracked<CompareAndExchangeTest::Instance>,
    }

    spec fn wf(&self) -> bool {
        invariant on atomic_counter with (instance) is (v: u32, g: CompareAndExchangeTest::counter) {
            g.instance_id() == instance@.id() && g.value() == v as int
        }
    }
}

fn main() {
    // initialize protocol instance
    let tracked (
        Tracked(instance),
        Tracked(counter_token),
        Tracked(cae_a_token),
    ) = CompareAndExchangeTest::Instance::initialize();

    let tr_instance: Tracked<CompareAndExchangeTest::Instance> = Tracked(instance.clone());
    let atomic_counter = AtomicU32::new(Ghost(tr_instance), 0, Tracked(counter_token));
    let global = Global {
        atomic_counter,
        instance: Tracked(instance),
    };
    let global_arc = Arc::new(global);

    let total: u32 = 10;

    // Spawn threads
    let global_arc1 = global_arc.clone();
    let join_handle1 = spawn(
        (move || -> (ret: (Tracked<(CompareAndExchangeTest::cae_a, bool)>))
            ensures
                ret@.0.instance_id() == instance.id() && ((ret@.0.value() == true && ret@.1 == true) || ret@.1 == false),
            {
                let globals = &*global_arc1;
                let tracked mut token = cae_a_token; // moved
                let tracked mut updated;
                let current =
                    atomic_with_ghost!(&globals.atomic_counter => load();
                    returning ret;
                    ghost c => {
                        globals.instance.borrow().increment_will_not_overflow_u32(&mut c);
                    }
                );

                let _ =
                    atomic_with_ghost!(&globals.atomic_counter => compare_exchange(current, current + 1);
                        update old_val -> new_val;
                        returning ret;
                        ghost c => {
                            match ret {
                                Result::Ok(_) => {
                                    assert(old_val == current);
                                    assert(new_val == current + 1);
                                    globals.instance.borrow().increment_will_not_overflow_u32(&mut c);
                                    globals.instance.borrow().tr_inc_a(&mut c, &mut token); // atomic increment
                                    updated = true;
                                },
                                Result::Err(_) => {
                                    assert(old_val == new_val);
                                    updated = false;
                                }
                            }
                        }
                );
                Tracked((token, updated))
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
        atomic_with_ghost!(&global.atomic_counter => load();
        ghost c => {
            instance.finalize(t.1, &c, &t.0);
        })
    ;

    assert(t.1 && x == 1 || !t.1);
}
}
