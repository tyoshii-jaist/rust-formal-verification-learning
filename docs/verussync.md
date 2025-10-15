## VerusSync
The short short story is Verus allows users to define ghost state using a novel “ghost state
description language” that we call VerusSync. In VerusSync, the user defines the ghost state
they want, the transitions they want to perform with it, and prove invariants and other wellformedness
conditions on it. In exchange, VerusSync creates an API of “ghost tokens” that are
useful for verifying concurrent code.
We will characterize VerusSync more formally in Chapter 5. In this chapter, we will present
an example-driven introduction to VerusSync, starting in §3.6.

sharding strategy (シャーディング戦略: 分ける戦略、みたいな感じ)

sharding()のかっこに書いてあるのはstrategyであり、variable,constantなどがあり、それによりtokenの性質も変わる。

add で map_field に k => v を足せる

#[invariant] 経由で不変量を見る。



# Atomicについて(これはVerusSyncでない。)

SeqCst
https://zenn.dev/belle/articles/bcddf554a43053


https://verus-lang.github.io/verus/verusdoc/vstd/atomic_ghost/struct.AtomicU32.html
https://verus-lang.github.io/verus/verusdoc/vstd/macro.atomic_with_ghost.html

    // pub const exec fn new(Ghost(k): Ghost<K>, u: u32, Tracked(g): Tracked<G>) -> t : Self
    //     requires
    //         Pred::atomic_inv(k, u, g),
    //     ensures
    //         t.well_formed() && t.constant() == k,

K = そのアトミックに結びついた 「不変条件（invariant）の定数パラメータ」。
生成時に Ghost<K> を渡して固定され、AtomicU32::constant() で取り出せる。以後ずっと変わらない“タグ/設定/識別子/静的パラメータ”。ドキュメント上も pub struct AtomicU32<K, G, Pred> で Pred: AtomicInvariantPredicate<K, u32, G> とあり、constant() は K を返す仕様になっている

G = そのアトミックにぶら下がる 「可変なゴースト状態」（tracked リソース）。
生成時に Tracked<G> を渡し、atomic_with_ghost! のブロック内で 操作に応じて更新する義務がある。つまり “前の値 prev と g が不変量を満たしていたなら、操作後は next と更新後の g が不変量を満たせ”という契約。ブロック内では ghost $g => { ... } で g: G に触れられる。


# Rely Guarantee

Rely-Guarantee (RG) でも Verus(VerusSync系の invariant)でも、共有状態が他スレッドの介入下でも壊れないことを示す。

Rely (環境側)、Guarantee (自分側) の約束。

Verus は invariant と token を用いて、lock とかを紐づけることで壊さないことを書く。


# 値の転送プログラムの検証
TOTAL 値を決め、a = TOTAL、b = 0 から始めて、2つのスレッドがめいめいに a から 1 引き、b に 1 加える。
a が 0 になるまで繰り返す。

まずは簡単に a 回 decrement して b を increment する ()


# 3.4.5 の Ghost Object
Here, the word “invariant” is taken
from separation logic, where an invariant can be thought of as a kind of “container” that stores a
proposition. The container can be shared, and it permits clients to temporarily obtain ownership
of the contents.

### state machine の inductive について
コンパイラが教えてくれる！！

```
error: missing inductiveness proofs for 3 transition(s); try adding the following stubs:
       
        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(tr_decrement_a)]
        fn tr_decrement_a_inductive(pre: Self, post: Self, thread_id: int, current_a: int) { }
       
        #[inductive(tr_increment_b)]
        fn tr_increment_b_inductive(pre: Self, post: Self, thread_id: int) { }
```
