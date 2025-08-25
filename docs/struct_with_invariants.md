# struct_with_invariants を理解する

https://verus-lang.github.io/verus/verusdoc/vstd/pervasive/macro.struct_with_invariants.html

このマクロは、AtomicInvariantやLocalInvariantといったデータ型に不変条件（invariants）を定義する際の定型コードを削減することを目的としている。

struct_with_invariants!マクロは、以下の作業を自動化する。

- 不変条件の定義: 構造体（struct）とその不変条件を宣言するspec関数をまとめて定義する。
- 型パラメータの補完: マクロは、ユーザーが定義した不変条件に基づいて、構造体のフィールドにある不完全な型パラメータを自動的に埋める。
- Traitの実装: ユーザーが提供した述語（predicate）を用いて新しい型を作成し、特定の特性を実装することで、サポートされている不変条件型のPred型パラメータを埋める。

不変条件の個々の定義は**InvariantDecl**と呼ばれ、以下の要素で構成される。

- フィールド: 不変条件を適用する対象のフィールド。
- パラメータ: 不変条件によって制約される型パラメータ。
- ブール式: 不変条件を定義する真偽値の式。


https://github.com/verus-lang/verus/blob/main/examples/basic_lock2.rs
```
struct_with_invariants!{
    // こちらが構造体の定義
    struct Lock<T> {
        pub atomic: AtomicBool<_, Option<cell::PointsTo<T>>, _>, // この PointsToはロックへのアクセス権になる。そのため、ロック取得済み状態では誰かに渡しているので、Noneになる。ロックが獲得できる状態であれば、Someになる。
        pub cell: PCell<T>,
    }

    // こちらが対となる仕様の定義
    // invariant なので常に満たされる。
    spec fn wf(self) -> bool {
        // これが InvariantDecl
        // "atomic" が$field_nameで、上記Lockのatomicになる。
        // "with" が$dependenciesで、上記Lockのcellになる。
        // "is" の($params) { $bool_expr }
        // AtomicBoolはatomic_ghost型なので、$paramは格納する値 (bool) と G (atomicフィールドの <_, G, _> と一致)になる。
        invariant on atomic with (cell) is (v: bool, g: Option<cell::PointsTo<T>>) { この gの型は atomicフィールドの <_, G, _> のGと一致する
            match g {
                None => {
                    // When there's no PointsTo, the lock must be taken, thus
                    // the boolean value is 'true'.
                    v == true
                }
                Some(points_to) => {
                    points_to.id() == cell.id() // dependenciesに追加しているのでcellはアクセスできる
                      && points_to.is_init()
                      && v == false
                }
            }
        }
    }
}
```