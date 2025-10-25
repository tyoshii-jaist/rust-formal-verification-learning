### 関連して気になったことのメモ書き

- WP (Weakest Precondition)

wp = “S 後に Q を得るための、最弱の十分条件（かつ状態レベルでは必要十分）"

- Monoid
M x M -> M

結合律を満たす。
(a * b) * c = a * (b * c)

単位元がある
a * e = a かつ e * a = a

逆元はなくて良い。

(Z, + , 0), (N, +, 0) とか。


#### Iris lecture note をチラ見
*Invariants* are a mechanism that allows different program threads to access shared
resources, e.g., read and write to the same location, provided they do not invalidate properties
other threads depend on, i.e., provided they maintain invariants. 

*Ghost state* is a mechanism
which allows the invariants to evolve over time. It allows the logic to keep track of additional
information that is not present in the program code being verified, but is nonetheless essential
to proving its correctness, such as relationships between values of different program variables.

並行性は fork と CAS

configuration は heap と thread pool

CAS(l, v, v') は heap h から l の値を探し、v と比較し一致すれば、h(l) を v に更新する。これをAtomicに行う。


Intuition for Iris propositions Intuitively, an Iris proposition describes a set of resources.
A canonical example of a resource is a heap fragment.

P * Q は「互いに重ならないヒープ h = h1 ⊎ h2 に分けられて、h1 ⊨ P かつ h2 ⊨ Q」。

P −* Q は「任意のヒープ hP で hP ⊨ P なら、今のヒープと合体 h ⊎ hP は Q を満たす」。

要は、**足された P を消費して Q を成立させる能力**　を今の状態が持っている、という主張。

x |-> u -* (x |-> u * y |-> v)



Remember: Prove global properties, export local features.

birds_eye はinput tokenによらない値を使いたいときに使う。決定的ではなくなる。