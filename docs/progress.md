# 進捗

## Verus

### コードのモードの整理
| | spec code | proof code | exec code |
|---|---|---|---|
| **目的** | プログラムの性質を記述する | プログラムの性質を証明する | 通常のRustコードであり、コンパイルされ実行される |
| **compiled or ghost** | ghost | ghost | compiled |
| **code style** | purely functional | mutation allowed | mutation allowed |
| **can call spec functions** | yes | yes | yes |
| **can call proof functions** | no | yes | yes |
| **can call exec functions** | no | no | yes |
| **body visibility** | may be visible (visibleでない場合は引数が一致しているような場合にしか同一判定ができない) | never visible | never visible |
| **body** | body optional (ない場合は関数の型のみチェックされる?) | body mandatory | body mandatory |
| **determinism** | deterministic | nondeterministic | nondeterministic |
| **preconditions/postconditions** | recommends (checkedで強制しない限りチェックされない) | requires/ensures | requires/ensures |

### 変数のモードの整理
| | Default variable mode | ghost variables | tracked variables | exec variables |
|---|---|---|---|---|
| **spec code** | ghost | yes | | |
| **proof code** | ghost | yes | yes | |
| **exec code** | exec | yes | yes | yes |

### PPtr ("permissioned pointer")
- 入門用ポインタ取り扱い機能​ https://verus-lang.github.io/verus/verusdoc/vstd/simple_pptr/struct.PPtr.html​
- これを用いて、参照、参照外し、読み、書きのコードを書いた。​
    - trainings/pptr_basics/my_pptr.rs​
    - trainings/pptr_basics/my_pptr2.rs

### raw pointer
- raw pointer でも基本的な読み書きの例を書いた​
    - trainings/raw_ptr_basics/my_ptr.rs​
        - 4 バイトの領域を割り当て、初期化、書き込み、解放を行う​
    - split_ptr.rs
        - 8バイトの領域を割り当て、u32を二つ割り当てる例を書いた​

途中、後ろのu32のメモリアドレスがusizeの上限を超えない保証ができなかった​
Zulipで質問したところ、Verusの問題だったらしく、修正してくれた​。
https://verus-lang.zulipchat.com/#narrow/channel/399078-help/topic/.E2.9C.94.20possible.20overflow.20warning.20when.20using.20block_ptr.20.2B.204/with/528528009​

- Block 構造体を使う例 (これ以降 verus analyzer 用にフォルダを分けるようにした)​
    - verus/trainigns/verus_block_test​
    - 上記メモリアドレスをより丁寧に管理し、かつ、n個のu32を払い出せるような構造体を定義​
    - 非常に簡単な固定メモリアドレスアロケーターと言えなくもない
    - 各要素の free、および、deallocには対応していない。


# 2025/11/9 進捗
1. Atomic について
    - Verus では SeqCst 扱いとなる。Relaxed や Acq/Rel は対応しない。
    - SeqCst は一番強い順序制約を課すので、RelaxedやAcq/Relを使っている場合は別途保証する必要がある。
    - 参考: https://zenn.dev/belle/articles/bcddf554a43053
2. VerusSync の transition システム
    - Verus ではマルチスレッドの検証用に verus transition system (tokenized_state_machine) という機能を提供している
        - safety (データ競合free) と funtional correctness に主にフォーカスしており、liveness と termination はスコープ外 (元の論文の 2.2 に謳っている)
    - transition システムでは field を持つゴーストなモデルを定義し、状態遷移時に問題がないかを管理する
        - 不変量 (invariants) とその不変量が成り立つ証明を書く。
            - init(state) ==> inv(state)
            - transition(pre, post) && inv(pre) ==> inv(post)
        - トークン化された状態マシンに「トークン型（token types）」の集合を生成する。
        - システムの各遷移（transition）は、通常の遷移関係だけでなく、“トークンの交換（exchange）”としても捉える。
        - field に値を持つ
        - init! で初期化
        - transition! で遷移
        - invariant で不変量を記述する
        - inductive で遷移時の前後のチェック条件を記述する
        - 内部的には素の Verus コードに展開されているようなので、必ずしも使わなくてもよい。
        - https://verus-lang.github.io/verus/state_machines/strategy-reference.html
3. Verus state machine を用いた BBQueue の検証における現実的な課題
    - transition の記述と関数の使い方にかなり癖がある。
        - 引数が関数の処理内容によって変わるので、特にややこしい。
        - selfの意味がどのstmtの中にいるかで変わる。
        - sharding storategy ごとにかなり記述が異なる。update, remove, withdraw など
        - instance など暗黙に定義されている構造体もある。
        - 中間コードを見るような方式があると助かる。--log-all でなんとなくは見える。
    - 公式チュートリアルに書かれていた SPSC の例をもう少し理解する
        - Queueの各要素を PCell として管理している。
            - cell 本体の方を exec の方の buffer に入れ、cell_permの方を state machine に入れている
            - struct_with_invariants の定義で Atomic 変数と state machine の同名フィールドと紐づけている
    - 少しずつ慣れてきたが、まだ時間がかかる。
        - 簡単な例を書くことで、tokenized_state_machine の取り回しは何となくわかった。
            - 1 エレメントの withdraw ができた。(depositはしていない)
        - 簡単な例でも論理的整合性がないとドツボにはまるので、なかなかシンプルな問題設定が難しい
            - BBQueue 本体に手を付けた方が良いと判断し、開始した
        - エラーが直観的でない
        - ただし、書く、エラーを見る、直す、のサイクルは回り始めた。
    - BBQueue特有の課題
        - BBQueueのメモリハンドリングについて整理
            - BBQueueは Rust の const generics でコンパイルタイムにサイズを確定させ、[u8; N] の塊でハンドリング方式を取っている。
            - Prod/Consにはsliceを使ってこの領域の view を渡して見せている。(当然 unsafe の領域になる)
            - verus では[u8; N] を *mut u8 に変換することが未サポートなため、ヒープ確保で代替することにした。(fat => thin がサポートされていない？)issueあり。
        - Prod/Cons に BBQueue 構造体本体へのポインタを渡しているがここもかなりトリッキー(unsafe)なので、正しく Verus で取り扱える文脈に変換する方法を考えないといけない。今は Arc (Atomic Ref count) で代替して実装を進めている。


# interleaving について
VerusSync の並行意味論は、Iris 系の仕組みの上に乗っているとみなせる：
- Resource Algebra（RA）によるリソースモデル
- frame-preserving update
- guards / Storage Protocol
- invariant / fancy update（mask 付き view shift）

tokenized_state_machine が生成するトークンとその操作は、これら RA／Storage Protocol の上に載る frame-preserving update として実装可能になっている

並行実行・interleaving のレベルでは

遷移に対応するトークン操作が RA 上の frame-preserving update になっており
global invariant を Iris 型の invariant として保持することで定義された遷移 step を、任意の順番・任意のスレッド間で interleave してもglobal invariant は壊れないという形の性質を、Iris のメタ理論から得ている。

