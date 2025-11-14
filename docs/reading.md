# Chapter 1 Introduction
形式検証とかのそもそもの話。


# Chapter 2 Motivation and Case Studies
Case studies と Challenge。
2.2 Scope and the correctness properties of interest はとても大事。
2.2 Scope and the correctness properties of interest
Before diving in, allow me to delineate the scope of the correctness properties we are going to
be considering.
There are a number of properties one might be concerned with proving about a given
program or system:
1. Safety, that is, that the program does not exhibit some undesirable behavior. Safety can
include:
• Freedom from memory safety violations (spatial memory safety or temporal memory
safety)
• Freedom from data races
• Freedom from panics and early exits
2. Functional correctness, that is, any outputs or observable events of the program correspond
to some specification.
7
3. Liveness, properties like “the program will terminate” or “some desired thing will eventually
happen.”
4. Leak-freedom, the absence of memory leaks or of other resource leaks.
5. Privacy-preservation, that the observable properties are independent of some secret data.
This is an example of a hyperproperty, a property over sets of possible executions rather
than a property over a single execution.
Properties of interest The main focus of this thesis is on safety and functional correctness
properties. The two are in fact closely related: We cannot even attempt to prove functional
correctness without safety, and safety is sometimes (though not always) reliant on functional
correctness. Specifically, for safety, we are concerned the most with the absence of undefined
behavior, which includes both memory safety and data-race-freedom. For functional correctness,
the exact specification depends on the application.
Properties that are out of scope We treat liveness and termination as completely out-ofscope.
Termination for concurrent programs is in general quite difficult, and we do not attempt
it here. We also do not look at leak-freedom or any hyperproperties.
We also do not address panic-freedom; in fact, some of the code we will consider intentionally panics in certain situations. In principle, panic-freedom isn’t much different than other kinds of safety violations, though it might be more challenging to eliminate all panics (as panics are often the “final escape hatch” from situations that are hard to reason about).


# Chapter 3 Verus Overview
VerusはLinear Dafny/IronSyncの続き。

(3) A system of “ghost objects” operating within the ownership type system, allowing us to
address challenges that would otherwise be impossible with more standard ownership
types.
Most of the ghost object system is inspired by concurrent separation logic [61], and
especially the Iris concurrent separation logic [35]. We take direct inspiration from the
following aspects of CSL:
• Memory permissions, to handle data structures whose shapes make poor fits for
traditional ownership types.
• Ghost state and invariants, to handle concurrent data structures and other situations
where disparately owned objects need to maintain coordination.

Verus uses modular verification of functions based on preconditions and postconditions, discharging
proof obligations using an SMT solver, similar to Dafny [48] and F⋆ [70]. Let’s unpack
what this means.

モジュラー検証とは、一つの関数(lemma)に絞って検証を行うことをいう。全体は個別の検証の集まりで行われる。これにより検証機へのプレッシャーを軽減する。

requires/ensures の基本的な仕組みは 3.3.1 に書いてある。最弱事前条件を用いる標準的な方法で行う。

3.3.3 に Z3 を用いた証明の自動化について記載がある。
トリガーパターンについても記載がある。

3.4 以下は Rust の primitive について個別に細かい説明がある。

# Chapter 4 Ghost State as Monoids
Verus Monoidal Ghost Interface は素の Verus (spec/proof/exec とか ghost とか tracked とか) に
- RA（リソース代数）用の trait と Resource<P> 型
- Storage protocol 用の trait と StorageResource<K, V, P> 型
- join/split/update, withdraw/deposit/exchange, guards など

中身は全部 ghost / tracked な値・関数で書かれた Verus コードですが、
「可換モノイドになっていて」
「frame-preserving update がこう定義されていて」
「この公理群を満たしていれば RA / Storage protocol とみなす」


Irisと関連が強い。
Irisは「資源」の論理らしい。

bunched implication => の線が一本多いやつ
separation conjuntion \*
magic wand -\*

P ⇛ Q view shift P と Q は常に交換できる
P ≡−\∗ Q is the view shift wand PとQは交換可能。上と違い、一度しか交換できない。(-\* と同じ)



## ヒープの例で RA を理解したい
- ヒープ = 「アドレス → 値」の有限マップ h : Addr ⇀ Val。Map<usize, T> みたいなもの。
- P, Q = 「ヒープに関する性質」（heap predicate）の述語

### P, Q, R, S の例 (h: ヒープ)
- アドレス x に 10 の値が入っている。P(h) ≜ (h.contains_key(x) ∧ h[x] = 10) SLだとx ↦ 10 
- アドレス x に何かしらの値が入っている Q(h) ≜ h.contains_key(x)
- x に 10、y に 20 が入っている 
  R(h) ≜
    h.contains_key(x) ∧ h[x] = 10 ∧
    h.contains_key(y) ∧ h[y] = 20

- x と y が同じ値を指している
x と y が同じ値を指している
S(h) ≜
    h.contains_key(x) ∧
    h.contains_key(y) ∧
    h[x] = h[y]

### 「P ⇛ Q view shift」 「P と Q は常に交換できる」 の理解
Pは自分の持ち分だけを書き換えてQに変えられる。
例
x ↦ 0 ⇛ x ↦ 1
emp ⇛ ∃y. y ↦ 0 (ただし y は他と被らないとかの制約がある)

ゴーストだとそういうことは気にしなくてよい
P(h,g) ≜ ghost_counter(g) = n
から
Q(h,g) ≜ ghost_counter(g) = n+1

###  ≡−∗ は一回しか使えない。消費される。
P * (P ≡−∗ Q)  ⊢  |==> Q


### fancy update（マスク付き view shift）とは何か
P ⇛^E1_E2 Q = mask-changing view shift

「今のマスクが E1 で、P が成り立っている状態から、マスクを E2 に変えつつ、P を Q に交換してよい」

マスク E は「今、どの invariant を開けてもよいか」の集合。


### mask = 「開けてよい invariant の集合」とは何か
マスク E は openable な invariant の集合。invariant には名前空間 N がついている。

N ⊆ E なら、名前空間 N に属する invariant は “マスク E の下で open してよい（開けることが許されている

Iris では invariant に「名前空間 N」が付いていると思えばいいらしい。
P_N : 「名前空間 N に属する invariant P が登録されている」という persistent な事実を意味する。
mask E は「今、E に含まれる名前空間の invariant は“開けてもよい”」という情報になる。

### Inv-Open ルールをヒープの具体例で読む
P_N : 「名前空間 N に invariant P が登録されている」
N ⊆ E : 「今のマスク E に N が含まれているので、この invariant は open できる」

具体例
アドレス x に「常に偶数が入っている」という invariant を考える。
P(h) ≜ ∃v. h[x] = v ∧ (v mod 2 = 0)
1. invariant を open して、実際の x ↦ v を手に入れる
（ただし v は偶数である）
2.  x に v+2 を書き込む
3. 「v+2 も偶数」と示して、P が成り立つことを示す。
4. invariant を close して基に戻す

確かにこう考えると、invariant をオープンし、クローズ用に1回きりのトークンを受け取るというのはよくわかる。


### 4.3 の Resource Algebras を読む
妥当性述語 V : M → Prop

直感：
「このリソースの組み合わせは OK / NG」

さらに V には downward-closed (下に向かって閉じる) という条件を課す。

a ≼ b を「a が b の sub-resource」つまり
「∃c. a·c = b」と定義して、
条件：
a ≼ b ∧ V(b) ⇒ V(a) → 大きいリソース b が valid なら、その部分 a も valid。
さらに単位元は必ず valid：V(ϵ)

≼ (先行するか等しい)

ヒープの例だと、
M = 「ヒープ断片」の集合（アドレス→値の有限マップ）
· = 「disjoint union」（キーが被ってたら invalid、被ってなければ普通にマージ）
a ≼ b = ∃c. a·c = b = 「a と c を disjoint union すると b になる」
→ 「a は b の部分ヒープ」
V(b) = 「b は“衝突なし”のまともなヒープ」だとすると、b の部分ヒープ a も当然「衝突なし」のまともなヒープである


これを満たす RA (M,·,V) だとゴースト状態が使えるようになる。

「名前 γ の場所に、値 a のゴーストリソースを持っている」という状態になる。

Example 1 は排他的な典型的なRAを表す。

∀x, y. ex(x) · ex(y) =  bottom and ∀a, a · ϵ = a and a · bottom  =  bottom
なので、 ex(x) · ex(y) はあり得ない。つまり同一アドレスに異なる値が入っているなんてことはあり得ない。


ex(x) ⇝ ex(y), which implies the view shift, ex(x)_γ ⇛ ex(y) _γ

つまり任意のアドレスの値を書き換えても大丈夫だと言っている。


論文中で x,y を state と呼んでるのは、『その ghost リソースが表してる抽象状態』という意味だが、ヒープで考えるとセルに x や y の値が入っているみたいに考える。


物理ヒープ側
- アドレス：ℓ
- 中身：v
- アサーション：ℓ ↦ v 「実メモリのアドレス ℓ に v が入っている」

ゴースト（RA）側
- RA 要素：ex(x)（ただの値）
- ゴースト名：γ
- アサーション：ex(x)_γ → 「ゴーストロケーション γ に、抽象状態 x を排他的に持っている」

x は単純には v を持って管理してもよいし、別の管理用の値でもよい。γもゴーストな世界のアドレスみたいなもの。

両者を Invariant で関連付けると。
Inv(ℓ, γ)  ≜  ∃v. ex(v)_γ * ℓ ↦ v

ℓ, γ　の組に対し、ℓにvが入っているならば γ にも ex(v) がある。

### 4.5 共有読取ロジック Leaf
fractional permission と counting permissionを一般化した “共有読取ロジック Leaf” を Iris 上で定義し、その中核として G ⤔ P（guards）と “storage protocol” を導入してる

G ⤔ P（「G guards P」）は Iris の命題（iProp）
意味はざっくり：
「G を持っていれば、P を shared read-only として使っていい」


# Chapter 5 VerusSync

ShardableState

Shardable Transition Modeling Language (STML).











### Iris from the ground up もチョイ読み
The key idea of Iris is　that even the fanciest of the interference-control mechanisms in recent concurrency logics can be expressed by a combination of two orthogonal (and already well-known) ingredients:
partial commutative monoids (PCMs) and invariants.

2 章
幽霊状態の必要性。幽霊状態 a_gamma は名前 gamma で a の値を持ち、現在の x の状態をミラーする。

幽霊状態を記録することで、その場所でどのような共有が許されるかを選択できる。

幽霊位置gammmaにはすきな構造や所有権を選択できる。

Iris allows one to use ghost state via the proposition a γ , which asserts ownership of a
piece a of a ghost location γ .

すべての PCM は RA だが、逆はそうではない。