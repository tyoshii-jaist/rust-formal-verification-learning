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


# 11/9 進捗
- VerusSync の transition システムを読み進めた
        - transition システムでは field を持つゴーストなモデルを定義し、状態遷移時に問題がないかを管理する
            - field に値を持つ
            - init! で初期化
            - transition! で遷移
            - invariant で不変量を記述する
            - inductive で遷移時の前後のチェック条件を記述する
            - 内部的には素の Verus コードに展開されているようなので、必ずしも使わなくてもよい。
        - transition の記述と関数の使い方にかなり癖がある。
            - 引数が関数の処理内容によって変わるので、特にややこしい。
            - selfの意味がどのstmtの中にいるかで変わる。
            - sharding storategy ごとにかなり記述が異なる。update, remove, withdraw など
            - instance など暗黙に定義されている構造体もある。
            - 中間コードを見るような方式があると助かる。--log-all でなんとなくは見える。
        - 少しずつ慣れてきたが、まだ時間がかかる。
            - 簡単な例でも論理的整合性がないとドツボにはまるので、なかなかシンプルな問題設定が難しい
            - エラーが直観的でない
            - ただし、書く、エラーを見る、直す、のサイクルは回り始めた。
        - 見えている課題と今後の方向性
            - SPSC の例をもう少し理解する
                - 簡単な例を書くことで、tokenized_state_machine の取り回しは何となくわかった。
            - 2スレッドで、PointsToのプールからの出し入れ (withdraw/deposit)をやってみた。
                - これは BBQueue のベースになる
                - 1 エレメントの withdraw ができた。(depositはしていない)
                - n エレメントの withdraw/deposit に発展させたい。
                    => Adhoc な拡張を行うと論理整合性が取れなくて進捗が著しく悪いので、BBQueue 本体の検証に移ることにした。
            - BBQueue では slice を取り扱うのでその取り回しがまだわかっていない
                - BBQueueは Rust の const generics でコンパイルタイムにサイズを確定させ、[u8; N] の塊でハンドリング方式を取っている。
                - Prod/Consにはポインタを使ってこの塊の view を渡して見せている。(当然 unsafe の領域になる)
                - verus では[u8; N] を *mut u8 に変換することが未サポートなため、ヒープ確保で代替することにした。(fat => thin がサポートされていない？)
            - BBQueue 書き始めた。

