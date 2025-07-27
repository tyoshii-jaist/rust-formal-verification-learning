循環バッファ
BipBuffersにインスパイアされた。
DMAフレンドリー
SPSC (Single Producer, Single Consumer)。スレッドセーフであり、PとCは別々のスレッドで動作できる。
組み込み向け。
no_std
Lock Free Algo
小さいサイズ (1Kとか4Kとか)でオーバーヘッドが小さい

Circular BUffer
ヒープがないような環境も想定している。固定アドレス。

線形のメモリがチャンクに分割されている。
ReadポインタとWriteポインタになる。最初は左端。同じだと読めない。
ラップする。

一般の循環バッファはスロット型なので、可変長データの場合はちょっと注意がいる。
従来の循環バッファーはこの時に遅くなりがち。ハードウェアオフロードも難しい。
120byteや20byteなどの可変長のときに大体固定スロットを使っているので問題になる。無駄になる。
(ポインタタグというテクニックがあるが、安全性担保が難しい？)

BBQueueではどうするか？
AsideとBsideがある。常に2つのことができる。

### Producer
grant: give me space to write bytes. 成功すると slice を得る。連続領域。
commit: make available to read.

### Consumer
read: give me available bytes to read.
release: make available to write.

上記4は完全に独立して動くことができる。
Result型を返す。

### Producerスレッドの例
1grantしてHardwareにその領域にデータを書き込みを依頼。割り込みで受け取り、2commitする。

### Consumer スレッド
3read 4release

### 特殊状態説明
commitのラップアラウンド時
お尻の方で連続領域が足りない場合、先頭から払い出したいときはwatermarkを使う。これはBBQ内部で閉じられており、PもCも知らない。Cはwatermarkにあたるとwatarmarkが消えて、read pointerはラップする。

readの先がwrapしている場合、末端で一回切れる。2回Read要求する必要がある。


### Frame message機能について
headerが導入される。内部的な動作は同じ。チャンクを追跡する。headerサイズは可変。7ビット利用。
grant max 64 とすると最大で64の領域が欲しいということを要求できる。
BBQは64+headerの領域を確保する。
ただ、最初にはPは32バイトしかデータを受け取らなかった。32commitする。
するとheaderに32と書かれているので、32しか読まなくてよいことがわかる。

readの挙動も変わり、readはフレーム単位でしか返さない。
(ラップした領域のjoinとかはしなさそう。)


# ロックフリーアルゴリズムの理解は難しい！
https://www.youtube.com/watch?v=ngTCf2cnGkY のQAにおいて以下のように言っている(文字起こしかつ機械翻訳なのでちょっと誤訳があるかも。)
やはり完全に不安は消えていない気もするので、証明すると価値はありそうだと感じた。
「ロックフリーアルゴリズムは、正しく実装するのが非常に難しいことで有名です。 正しく動いているように見えて、99.99%の時間は動くけれど、肝心な時に動かない、ということが非常によくあります。私が自分のロックフリーアルゴリズムが正しいかどうかを頭の中でモデル化して検討する作業の多くは、ETHチューリッヒのアンドレア・ラトゥーダ・アックスと一緒に行いました。」

「数年前のChaos Communication Congressで、私たちは座って考えられるすべてのことを図に描き出しました。それでも、このコードの内部を触るたびに、少し神経質になります。だから、BBQueueのほとんどすべてのバージョンで、コアロジックはほぼ常に全く同じなんです。一度解明したら、もう触りたくない、触ると不安になるからです。」


[guide on YouTube]: https://www.youtube.com/watch?v=ngTCf2cnGkY
[BipBuffers]: https://www.codeproject.com/Articles/3479/%2FArticles%2F3479%2FThe-Bip-Buffer-The-Circular-Buffer-with-a-Twist
[this blog post]: https://ferrous-systems.com/blog/lock-free-ring-buffer/


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