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


## BBQueue
[guide on YouTube]: https://www.youtube.com/watch?v=ngTCf2cnGkY
[BipBuffers]: https://www.codeproject.com/Articles/3479/%2FArticles%2F3479%2FThe-Bip-Buffer-The-Circular-Buffer-with-a-Twist
[blog post]: https://ferrous-systems.com/blog/lock-free-ring-buffer/

### 特徴
- 循環バッファ
- BipBuffersにインスパイアされた。
- DMAフレンドリー
- SPSC (Single Producer, Single Consumer)。スレッドセーフであり、PとCは別々のスレッドで動作できる。
- 組み込み向け
- no_std
- Lock Free Algo
- 小さいサイズ(1Kとか4Kとか)向け？オーバーヘッドが小さい。標準的なヒープを使う循環バッファライブラリは他にもRust実装はあるので、使いどころのすみ分けはある。
- ヒープがないような環境も想定している。固定アドレス。

### YouTube見たときのメモ書き (後で整理。不正確かも。)
線形のメモリがチャンクに分割されている。
ReadポインタとWriteポインタになる。最初は左端。同じだと読めない。
ラップする。

一般の循環バッファはスロット型なので、可変長データの場合はちょっと注意がいる。
従来の循環バッファーはこの時に遅くなりがち。ハードウェアオフロードも難しい。
120byteや20byteなどの可変長のときに大体固定スロットを使っているので問題になる。無駄になる。
(ポインタタグというテクニックがあるが、安全性担保が難しい？)

BBQueueではどうするか？
AsideとBsideがある。常に2つのことができる。

#### Producer
grant: give me space to write bytes. 成功すると slice を得る。連続領域。
commit: make available to read.

#### Consumer
read: give me available bytes to read.
release: make available to write.

上記4は完全に独立して動くことができる。
Result型を返すので、確保できないときとかは適切にエラーが返される。

#### Producerスレッドの動作例説明
1grantしてHardwareにその領域にデータを書き込みを依頼。割り込みで受け取り、2commitする。
#### Consumerスレッドの動作例説明
3read 4release

#### 特殊状態説明
commitのラップアラウンド時
お尻の方で連続領域が足りない場合、先頭から払い出したいときはwatermarkを使う。これはBBQ内部で閉じられており、PもCも知らない。Cはwatermarkにあたるとwatarmarkが消えて、read pointerはラップする。

readの先がwrapしている場合、末端で一回切れる。2回Read要求する必要がある。

#### Frame message機能について
headerが導入される。内部的な動作は同じ。チャンクを追跡する。headerサイズは可変。7ビット利用。
grant max 64 とすると最大で64の領域が欲しいということを要求できる。
BBQは64+headerの領域を確保する。
ただ、最初にはPは32バイトしかデータを受け取らなかった。32だけcommitされる。
するとheaderに32と書かれているので、32しか読まなくてよいことがわかる。

readの挙動も変わり、readはフレーム単位でしか返さない。
(ラップした領域のjoinとかはしなさそう。)

#### ロックフリーアルゴリズムの理解は難しい！
https://www.youtube.com/watch?v=ngTCf2cnGkY のQAにおいて以下のように言っている(文字起こしかつ機械翻訳なのでちょっと誤訳があるかも。)
やはり完全に不安は消えていない気もするので、証明すると価値はありそうだと感じた。
「ロックフリーアルゴリズムは、正しく実装するのが非常に難しいことで有名です。 正しく動いているように見えて、99.99%の時間は動くけれど、肝心な時に動かない、ということが非常によくあります。私が自分のロックフリーアルゴリズムが正しいかどうかを頭の中でモデル化して検討する作業の多くは、ETHチューリッヒのアンドレア・ラトゥーダ・アックスと一緒に行いました。数年前のChaos Communication Congressで、私たちは座って考えられるすべてのことを図に描き出しました。それでも、このコードの内部を触るたびに、少し神経質になります。だから、BBQueueのほとんどすべてのバージョンで、コアロジックはほぼ常に全く同じなんです。一度解明したら、もう触りたくない、触ると不安になるからです。」


### BBQueue 内部を見てみる
メモリ領域は `UnsafeCell<MaybeUninit<[u8; N]>>` として定義されている。これの Verusでの取り扱い型を知る必要がある。
==> PCellが用意されていた。これから読む。
https://verus-lang.github.io/verus/verusdoc/vstd/cell/struct.PCell.html


Atomic系のVerusでのハンドリング方法を知る必要がある。

==> 用意されていた。これから読む。
https://verus-lang.github.io/verus/verusdoc/vstd/atomic_ghost/index.html
https://verus-lang.github.io/verus/verusdoc/vstd/pervasive/macro.struct_with_invariants.html

各機能はここを見るのが大事
https://verus-lang.github.io/verus/guide/features.html?highlight=UnsafeCell#supported-rust-features

これが Atomic と PCell を絡めた良い例のようなので精読する
https://github.com/verus-lang/verus/blob/main/examples/basic_lock2.rs


```
pub struct BBBuffer<const N: usize> {
    buf: UnsafeCell<MaybeUninit<[u8; N]>>,

    /// Where the next byte will be written
    write: AtomicUsize,

    /// Where the next byte will be read from
    read: AtomicUsize,

    /// Used in the inverted case to mark the end of the
    /// readable streak. Otherwise will == sizeof::<self.buf>().
    /// Writer is responsible for placing this at the correct
    /// place when entering an inverted condition, and Reader
    /// is responsible for moving it back to sizeof::<self.buf>()
    /// when exiting the inverted condition
    last: AtomicUsize,

    /// Used by the Writer to remember what bytes are currently
    /// allowed to be written to, but are not yet ready to be
    /// read from
    reserve: AtomicUsize,

    /// Is there an active read grant?
    read_in_progress: AtomicBool,

    /// Is there an active write grant?
    write_in_progress: AtomicBool,

    /// Have we already split?
    already_split: AtomicBool,
}
```