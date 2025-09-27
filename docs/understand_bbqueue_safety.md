# BBQueue の理解
どのようなコンセプトでどういう問題をクリアしたライブラリなのかを理解する。

## 概要
SPSCのロックフリー循環バッファ (+ no_std)


| 想定される問題種類 | BBQueueでの具体的な状況 | どう対応しているか |
|---|---|---|
| ポインタの競合 | read と write の位置などの情報が複数のスレッドから書き込まれてしまう | SPSC で共有しないから起きない |
| データの競合 | write 完了していない領域を read してしまう。read しきっていない領域に write してしまう | コア部分になる。別途書く。 |
| ABA問題 | read や write 位置などの情報変化を検知できない | それら変数を共有しないから起きない |
| デッドロック | read と write スレッドがお互いを待ちあう | SPSCかつロックフリーなので起きない |
| ライブロック | read と write スレッドがお互いを譲り合う | SPSCかつロックフリーなので起きない |
| スタベーション | read と write スレッドのいずれかが進行しない状態になる| SPSCかつロックフリーなので起きない |


### データ競合について
#### writeされていない領域を読まない
write済みな箇所を示す値はproducerのみがAtomicに操作する。
DMA等で、producer以外が書き込める領域は reserve で確保し、完了時にAtomicにcommitすることで安全にwrite位置を更新する。

#### readされていない領域に書かない
read済みな箇所を示す値はconsumerのみがAtomicに操作する。


### コード読み
BBBuffer: 根幹となるデータ構造

impl<'a, const N: usize> BBBuffer<N>: ライフタイムに依存するメソッドを実装している。Prod/ConsインスタンスのライフタイムがBBBufferと同じなので、そこを共有する必要がある。
impl<const A: usize> BBBuffer<A>: ライフタイムに依存しないメソッドを実装している

new() で初期化し、try_split() で Pros/Cons を得る。try_split() は一度しかできない。
try_release() は解放。


### VerusのConcurrencyの節がマジ大事！
https://verus-lang.github.io/verus/guide/concurrency.html
https://verus-lang.github.io/verus/state_machines/intro.html


これがめちゃ大事なエッセンスが積まれている！
https://verus-lang.github.io/verus/state_machines/examples/producer-consumer-queue.html

```
Verified implementation
With verification, we always need to start with the question of what, exactly, we are verifying. In this case, we aren’t actually going to add any new specifications to the enqueue or dequeue functions; our only aim is to implement the queue and show that it is memory-type-safe, e.g., that dequeue returns a well-formed T value without exhibiting any undefined behavior.
```

ここは本当に大事である。BBQueueに読み替えると、reserve、commitは正しい範囲に書き込み、readが正しいデータを返すこと (writeが最後にcommitした内容が返ること) になるだろうか。


UnsafeCell<MaybeUninit<T>>　は PCell<T> になる。


```
Now, if we’re going to be using a PCell instead of an UnsafeCell, then at the two points where we manipulate the cell, we are somehow going to need to have the permission token at those points.

Furthermore, we have four points that manipulate atomics. Informally, these atomic operations let us synchronize access to the cell in a data-race-free way. Formally, in the verified setting, these atomics will let us transfer control of the permission tokens that we need to access the cells.

Specifically:

enqueue needs to obtain the permission at produce_start, use it to perform a write, and relinquish it at produce_end.
dequeue needs to obtain the permission at consume_start, use it to perform a read, and relinquish it at consume_end.
```

ここをBBQueueに翻題する必要がある！

buf (PCell) にアクセスする際には必ずパーミッションが必要になる。


## 状態を整理

公式ドキュメントの例
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



### 検証のアプローチ

BufをUnsafeCellとVerusで等価なPCell (Permissioned Cell) にする。Pcellには id とそれに紐づくtokenがあり、それがないと操作できない。

例では、enqueue/dequeueの開始時にtokenを得て、終わったら返す、という形で扱っている。

token管理用のMapを用意して、それを更新することで管理している。

BBQueue では
### 管理すべき状態
- The value of the shared `write` AtomicUsize
- The value of the shared `read` AtomicUsize
- The value of the shared `last` AtomicUsize
- The value of the shared `reserve` AtomicUsize
- The value of the shared `already_split` AtomicBool
- The value of the shared `read_in_progress` AtomicBool
- The value of the shared `write_in_progress` AtomicBool
- The producer’s state
    Local `write`, `read` on grant
    Local `write`, `last`, `reserve` on commit
- The consumer’s state
    Local `write`, `last`, `read` on read
- The buffer (PCell)
- The permissions (PointsTo?)

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
