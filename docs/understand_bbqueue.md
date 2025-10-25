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
