use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::prelude::*;
use vstd::thread::*;
use vstd::*;

verus! {
tokenized_state_machine!(
    X {
        fields {
            #[sharding(variable)]
            pub counter: int,

            #[sharding(variable)]
            pub inc_a: bool,

            #[sharding(variable)]
            pub inc_b: bool,
        }

         // この操作は Atomic 以外の場合は逐次評価されるのか？
        #[invariant]
        pub fn main_inv(&self) -> bool {
            self.counter == (if self.inc_a { 1 as int} else { 0 }) + (if self.inc_b { 1 as int } else { 0 })
        }

        init!{
            initialize() {
                init counter = 0;
                init inc_a = false;
                init inc_b = false;
            }
        }

        transition!{
            tr_inc_a() {
                require(!pre.inc_a);
                update counter = pre.counter + 1;
                update inc_a = true;
            }
        }

        transition!{
            tr_inc_b() {
                require(!pre.inc_b);
                update counter = pre.counter + 1;
                update inc_b = true;
            }
        }

        property!{
            increment_will_not_overflow_u32() {
                assert 0 <= pre.counter < 0xffff_ffff;
            }
        }

        property!{
            finalize() {
                require(pre.inc_a);
                require(pre.inc_b);
                assert pre.counter == 2;
            }
        }

        #[inductive(tr_inc_a)]
        fn tr_inc_a_preserves(pre: Self, post: Self) {
        }

        #[inductive(tr_inc_b)]
        fn tr_inc_b_preserves(pre: Self, post: Self) {
        }

        #[inductive(initialize)]
        fn initialize_inv(post: Self) {
        }
    }
);

struct_with_invariants!{
    pub struct Global {
        // counter field とマッチする値
        pub atomic: AtomicU32<_, X::counter, _>, //# 真ん中 (V) に型を書く

        // protocol のインスタンス
        pub instance: Tracked<X::Instance>,
    }

    spec fn wf(&self) -> bool {
        invariant on atomic with (instance) is (v: u32, g: X::counter) {
            g.instance_id() == instance@.id()
            && g.value() == v as int
        }
    }
}

fn main() {
    // プロトコルの初期化
    let tracked (
        Tracked(instance), // fieled 以外にinstanceも返している。
        Tracked(counter_token),
        Tracked(inc_a_token),
        Tracked(inc_b_token),
    ) = X::Instance::initialize();

    // カウンターの初期化
    let tr_instance: Tracked<X::Instance> = Tracked(instance.clone());
    // pub const exec fn new(Ghost(k): Ghost<K>, u: u32, Tracked(g): Tracked<G>) -> t : Self
    //     requires
    //         Pred::atomic_inv(k, u, g),
    //     ensures
    //         t.well_formed() && t.constant() == k,
    let atomic = AtomicU32::new(Ghost(tr_instance), 0, Tracked(counter_token));
    let global = Global { atomic, instance: Tracked(instance.clone()) };
    let global_arc = Arc::new(global);

    // Spawn threads

    let global_arc1 = global_arc.clone();
    let join_handle1 = spawn(
        (move || -> (new_token: Tracked<X::inc_a>)
            ensures
                new_token@.instance_id() == instance.id() && new_token@.value() == true,
            {
                // inc_a_token は closure の中に move される
                let tracked mut token = inc_a_token;
                let globals = &*global_arc1;
                let _ = atomic_with_ghost!(&globals.atomic => fetch_add(1);
                    ghost c => {
                        globals.instance.borrow().increment_will_not_overflow_u32(&c);
                        globals.instance.borrow().tr_inc_a(&mut c, &mut token); // atomic increment
                    }
                );
            Tracked(token)
        }),
    );

    let global_arc2 = global_arc.clone();
    let join_handle2 = spawn(
        (move || -> (new_token: Tracked<X::inc_b>)
            ensures
                new_token@.instance_id() == instance.id() && new_token@.value() == true,
            {
                // inc_b_token は closure の中に move される
                let tracked mut token = inc_b_token;
                let globals = &*global_arc2;
                let _ = atomic_with_ghost!(&globals.atomic => fetch_add(1);
                    ghost c => {
                        globals.instance.borrow().increment_will_not_overflow_u32(&mut c);
                        globals.instance.borrow().tr_inc_b(&mut c, &mut token);
                    }
                );
                Tracked(token)
            }),
    );

    let tracked inc_a_token;
    match join_handle1.join() {
        Result::Ok(token) => {
            proof {
                inc_a_token = token.get();
            }
        },
        _ => {
            return ;
        },
    };

    let tracked inc_b_token;
    match join_handle2.join() {
        Result::Ok(token) => {
            proof {
                inc_b_token = token.get();
            }
        },
        _ => {
            return ;
        },
    };

    // thread を join して、atomicを再度ロードする
    let global = &*global_arc;
    let x =
        atomic_with_ghost!(&global.atomic => load();
        ghost c => {
            instance.finalize(&c, &inc_a_token, &inc_b_token);
        }
    );

    assert(x == 2);
}

} // verus