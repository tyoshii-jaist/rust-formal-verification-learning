use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::prelude::*;
use vstd::thread::*;
use vstd::*;

// https://github.com/verus-lang/verus/blob/808725c449a5769ea5ad393ca551d120ebea5242/examples/state_machines/maps.rs#L13

verus! {
const TOTAL: u32 = 10;
tokenized_state_machine!(
    TransferAtoB {
        fields {
            #[sharding(constant)]
            pub total: int,

            #[sharding(variable)]
            pub a: int,

            #[sharding(variable)]
            pub b: int,

            #[sharding(storage_map)]
            pub decrement_ticket: Map<int, bool>, // tid vs whether the thread has a decrement ticket
        }

        #[invariant]
        pub fn main_invariant(&self) -> bool {
            self.a + self.b + self.decrement_ticket.dom().filter(|k: int| self.decrement_ticket[k]).len() == self.total
        }

        init!{
            initialize(total: int, decrement_ticket: Map<builtin::int, bool>) {
                init total = total;
                init a = total;
                init b = 0;
                init decrement_ticket = decrement_ticket;
            }
        }

        transition!{
            tr_decrement_a(thread_id: int, current_a: int, b: bool) {
                require(current_a == pre.a);
                require(pre.a > 0);
                update a = pre.a - 1;
                deposit decrement_ticket += [thread_id => b];
            }
        }

        transition!{
            tr_increment_b(thread_id: int, b: bool) {
                update b = pre.b + 1;
                withdraw decrement_ticket -= [thread_id => b];
            }
        }

        property!{
            finalize_a() {
                assert pre.a == 0;
            }
        }

        property!{
            finalize_b() {
                assert pre.b == pre.total;
            }
        }

        // これは verus コマンドがコンパイルエラーで suggest したもの。
        #[inductive(initialize)]
        fn initialize_inductive(post: Self, total: int, decrement_ticket: Map<builtin::int, bool>) { }
       
        #[inductive(tr_decrement_a)]
        fn tr_decrement_a_inductive(pre: Self, post: Self, thread_id: int, current_a: int, b: bool) { }
       
        #[inductive(tr_increment_b)]
        fn tr_increment_b_inductive(pre: Self, post: Self, thread_id: int, b: bool) { }
        // ここまで。
    }
);

struct_with_invariants! {
    pub struct Global {
        pub a_atomic: AtomicU32<_, TransferAtoB::a, _>,
        pub b_atomic: AtomicU32<_, TransferAtoB::b, _>,
        pub instance: Tracked<TransferAtoB::Instance>,
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
    ) = TransferAtoB::Instance::initialize(TOTAL as int, Map::empty(), Map::tracked_empty());

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
    let global_arc1 = global_arc.clone();
    let join_handle1 = spawn(
        (move || -> ()
            {
                let thread_id = 0; // 固定値
                let globals = &*global_arc1;

                loop {
                    let current_a = atomic_with_ghost!(&globals.a_atomic => load();
                        ghost c => {}
                    );
                    if current_a == 0 {
                        break;
                    }

                    let res = atomic_with_ghost!(&globals.a_atomic => compare_exchange(current_a, current_a - 1);
                        ghost a => {
                            globals.instance.borrow().tr_decrement_a(thread_id as int, current_a as int, true, &mut a, true);
                        }
                    );
                    
                    let res = atomic_with_ghost!(&globals.b_atomic => fetch_sub(1);
                        ghost b => {
                            // transition を呼び出すときの引数リストが特殊で、よくわからない。
                            globals.instance.borrow().tr_increment_b(thread_id as int, true, &mut b);
                        }
                    );
                };
                ()
            }
        )
    );

    /*
    let global_arc2 = global_arc.clone();
    let join_handle2 = spawn(
        (move || -> (new_b_token: Tracked<TransferAtoB::b>)
            ensures
                new_b_token@.instance_id() == instance.id(),
            {
                let tracked mut a_token = a_token;
                let tracked mut b_token = b_token;
                let thread_id = 1; // 固定値
                let globals = &*global_arc2;

                loop {
                    let current_a = atomic_with_ghost!(&globals.a_atomic => load();
                        ghost c => {}
                    );
                    if current_a == 0 {
                        break;
                    }

                    let res = atomic_with_ghost!(&globals.a_atomic => compare_exchange(current_a, current_a - 1);
                        ghost a => {
                            // transition を呼び出すときの引数リストが特殊で、よくわからない。
                            // 原著論文を確認すると、pre 等で使われている variable、読まれている? map が instance の定義順に並んでいるように見える。
                            globals.instance.borrow().tr_decrement_a(thread_id as int, current_a as int, true, &mut a, true);
                            globals.instance.borrow().tr_increment_b(thread_id as int, true, &mut b_token);
                        }
                    );
                };

                Tracked(b_token)
            }
        )
    );
    */

    match join_handle1.join() {
        Result::Ok(token) => {
            ()
        },
        _ => {
            return ;
        },
    };

    /*
    match join_handle2.join() {
        Result::Ok(token) => {
            ()
        },
        _ => {
            return ;
        },
    };
    */

    // thread を join して、atomicを再度ロードする
    let global = &*global_arc;
    let a =
        atomic_with_ghost!(&global.a_atomic => load();
        ghost a => {
            instance.finalize_a(&a);
        }
    );

    let b =
        atomic_with_ghost!(&global.b_atomic => load();
        ghost b => {
            instance.finalize_b(&b);
        }
    );

    assert(a == 0);
    assert(b == TOTAL);
}
}
