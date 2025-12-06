# BBQueue の理解
どのようなコンセプトでどういう問題をクリアしたライブラリなのかを理解する。

## 概要
SPSCのロックフリー循環バッファ (+ no_std)

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


### 「ロックフリー」について整理
- ロック (mutex 等)

相互排他のために所有権を取れない側を待たせる

- アトミック

CPU の提供する不可分操作を利用する。


BBQueue はアトミック (とメモリバリア) を使い、ロックは使わずにデータ競合を回避しているため、「ロックフリー」といえる。ただし、ProducerとConsumerの状況には依存して待ちが発生しないとは言えないので、「ウェイトフリー」ではない。

ロックフリーなので、相手方の都合で実質的に処理が進めない (Consumerが読めるデータがない) 場合でも待たされない。しかし、結局BBQueue使用者側にリトライ、スリープ、ロックなどの戦略を外出ししているだけとも言える。

### BBQueue の機能的利点について整理
類似の概念として既存の循環バッファ、BipBuffer などがある。

BipBufferとは基本的なバッファ管理方式は同じ。

原始的な循環バッファは使用者側に返す領域が連続領域かどうか保証しない。

BipBufferは保証する。そのため、ゼロコピーを実現しやすく、メモリマップ、DMAと相性が良い。

BBQueueはこの利点についてはBipBufferと同様になる。

BBQueueはBipBufferの一実装であり、SPSCなどスレッド周りの管理や、APIなどを整備してRustライブラリとして使いやすくしている。


## 動作理解
### Atomic変数
- The value of the shared `write` AtomicUsize. 次に書き込む位置。
- The value of the shared `read` AtomicUsize. 次に読みだされる位置
- The value of the shared `last` AtomicUsize. Bufferが循環した際に、読み込み可能な位置を示す。
- The value of the shared `reserve` AtomicUsize. Writerが書き込み可能な位置を示す。まだreadはできない。
- The value of the shared `already_split` AtomicBool. 初期化済みかを示す。
- The value of the shared `read_in_progress` AtomicBool. ConsumerにactiveなGrantがあるかを示す。
- The value of the shared `write_in_progress` AtomicBool. ProducerにactiveなGrantがあるかを示す。

### 操作
1. Producerがgrant(usize)を行う
write_in_progressをtrueに*更新*する。
write位置を決める。(Invert確認などを行う)
reserve値を*更新*する。
(空きがない場合にはエラーになるが、詳細は省略)

ProducerはGrantWを得て、その中にはBufferのslice (write ~ reserve) が入っており、読み書きができる。

![Grant](./assets/bbqueue_step1_grant.png)

2. Producerがcommitを行う
write_in_progressをfalseに*更新*する。
reserve位置を使った分に応じて戻して*更新*する。(使わなかった分を返す)
last位置を*更新*する。 (wrapした場合は前のwriteがlastになる。reserveがlastを追い越したら、lastは最後の位置にする、など)
write位置をreserveの値で*更新*する。

![Commit](./assets/bbqueue_step2_commit.png)

3. Consumerがread()を行う
read_in_progressをtrueに*更新*する。
read位置を*更新*する。
write, last, read の値をチェックし、wrapを検知したらread値を0に*更新*する。

Consumerはinvertしていたら read ~ lastまで、していなければ read ~ write間のsliceを得る。

![Read](./assets/bbqueue_step3_read.png)

4. Consumerがrelease()を行う
read_in_progressをfalseに*更新*する。
read位置を読んだ分だけ*更新*する。

![Release](./assets/bbqueue_step4_release.png)

### ざっくり理解
ロックを使わず、bufferの領域をProducerとConsumerで排他的に利用させることでデータ競合を防いでいる。


## 何を検証するのか？
上記操作が正しく動くこと。すなわち、書かれたものが正しく読めること。
- データ競合などが起きない。


## どう検証するのか。
VerusのTokenized State Machinesを使う。
https://verus-lang.github.io/verus/state_machines/tokenized.html
https://verus-lang.github.io/verus/state_machines/high-level-idea.html

## 実例
SPSCの循環キューの例があった。
https://verus-lang.github.io/verus/state_machines/examples/producer-consumer-queue.html

これはSPSCの状態と遷移を以下のように定義し、形式化した上で検証している。

### 管理すべき状態
- The value of the shared `head` atomic
- The value of the shared `tail` atomic
- The producer’s state
    Is the producer step in progress?
    Local `tail` field saved by the producer
- The consumer’s state
    Is the consumer step in progress?
    Local `head` field saved by the producer
- The IDs of cells in the buffer (so we know what permissions we’re meant to be storing)
- The permissions that are actually stored.

### 検証が必要な操作
dequeue が想定通りの型のデータを返すことを保証する。

### 状態遷移
- produce_start
- produce_end
- consume_start
- consume_end


## BBQueueに適用すると？
実は結構似ている。
上記の例も *ロックフリー循環キュー* のアルゴリズムである。
grantとcommitが一緒になっている点が違う。
1セル書き込み固定だが、複数指定が可能な点が違う。


### 管理すべき状態
- The value of the shared `write` AtomicUsize
- The value of the shared `read` AtomicUsize
- The value of the shared `last` AtomicUsize
- The value of the shared `reserve` AtomicUsize
- The value of the shared `already_split` AtomicBool
- The value of the shared `read_in_progress` AtomicBool
- The value of the shared `write_in_progress` AtomicBool
- The producer’s state
    Local `write`, `last`, `reserve`
- The consumer’s state
    Local `write`, `last`, `read`
- The buffer (PCell)
- The permissions (PointsTo)

### 検証が必要な操作
read が想定通りの型のデータを返すことを保証する。

### 状態遷移
- write_grant_start
- write_grant_end
- commit_start
- commit_end
- read_grant_start
- read_grant_end
- release_start
- release_end



## バッファは Verus でどう扱うべきか？

UnsafeCell は PCell が対応する。
よって PCell<[u8; N]> になる？
Const generics は Partially Supported らしい。

https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/fn.allocate.html

[u8; N] は使えないことが分かった。
https://github.com/verus-lang/verus/issues/187
[u8; N] の *mut T への変換ができない。

ということで妥協してヒープの allocate を使う。
const N を使う理由もなく、const generics は partially support なので利用をやめる。
struct_with_invariants! で closed spec の方にどのように N を渡せばよいかも不詳。

ghost の producer を commit 時に渡すように変えないと駄目なようだ。

core::cmp::min もつかえない
```
error: `core::cmp::min` is not supported (note: you may be able to add a Verus specification to this function with `assume_specification`) (note: the vstd library provides some specification for the Rust std library, but it is currently limited)
```


mut self も使えない。今回は &mut self にした。
```
error: The verifier does not yet support the following Rust feature: mut self
   --> vbqueue_proto_use_allocate_no_const_generics.rs:640:5
    |
640 |     pub fn commit(mut self, used: usize) {
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

```
struct_with_invariants!{
    pub struct VBBuffer<const N: usize> {
        buffer: *mut u8,
        write: AtomicU64<_, VBQueue::write, _>,
        read: AtomicU64<_, VBQueue::read, _>,
        last: AtomicU64<_, VBQueue::last, _>,
        reserve: AtomicU64<_, VBQueue::reserve, _>,
        read_in_progress: AtomicBool<_, VBQueue::read_in_progress, _>,
        write_in_progress: AtomicBool<_, VBQueue::write_in_progress, _>, 
        already_split: AtomicBool<_, VBQueue::already_split, _>,

        instance: Tracked<VBQueue::Instance>,
    }

    pub closed spec fn wf(&self) -> bool {
    }
```


### Producer/Consumer に渡す BBQueue の参照をどうするか
BBQueueの元の実装は NonNull<BBBuffer<N>> を使っている。
Verus のProd/Consの例はArcを使っており、少し違う。

NonNull<BBBuffer<N>>は non null な生ポインタに近いので、PCellを使うのが妥当なのか？
ここを読む.https://verus-lang.github.io/verus/guide/interior_mutability.html
ちょっと大変そうなので、一旦 Verus 公式の Arc 方式で妥協...

### Producer/Consumer に渡す GrantW/GrantR 内のスライスはどう扱うか？
元の実装は [u8; N] の領域に対して from_raw_parts_mut (unsafe) を使ってスライスを作り、返している。
今のところ、[u8; N] を *mut u8 に変換できないので、ヒープにアロケートする妥協を行うことにした。

また、GrantW/GrantRは元のRust 実装で使っている &mut [u8]（スライス型）を Verus 側ではそのまま扱えない。(未対応)

Verus の raw_ptr モジュールは、基本的に PointsTo<T> や ptr_mut_write<T> のように
「コンパイル時にサイズが決まる型 T が 1 個置かれている領域」を前提にしており、
長さが実行時に変わるスライス（&mut [u8]）をそのまま T として扱うことができない。


実行コードではバッファを *mut u8 と usize（長さ）として保持し、スライス相当の範囲は生ポインタとオフセットで扱う。

メモリ領域の所有権については、PointsToRaw とそのドメイン（バイト範囲）で管理し、u8 単位の書き込みに対して ptr_mut_write::<u8> を用いる

つまり、Verus では Rust の &mut [u8] を直接モデリングするのではなく、*mut u8 + len と ghost の所有権によって、
「スライスとしての意味」を表現する。

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

pub struct GrantW<'a, const N: usize> {
    pub(crate) buf: NonNull<[u8]>,
    bbq: NonNull<BBBuffer<N>>,
    pub(crate) to_commit: usize,
    phatom: PhantomData<&'a mut [u8]>,
}

pub struct GrantR<'a, const N: usize> {
    pub(crate) buf: NonNull<[u8]>,
    bbq: NonNull<BBBuffer<N>>,
    pub(crate) to_release: usize,
    phatom: PhantomData<&'a mut [u8]>,
}
```


split_read、frame 機能などは対応しない。


### バッファの権利払い出し用のメモ
write_in_progress 状態でのみ write ~ reserve の間を Prod に貸し出す。reserve は増やされる可能性があるので、そうすると貸し出しも増やす。

read_in_progress 状態でのみ read ~ write または read ~ last の間を Prod に貸し出す。read 位置は調整される可能性があるおで、その際には貸し出し領域も変更する。