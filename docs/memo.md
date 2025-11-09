# 11/9
* interlieve がどうなっているかをちゃんと調べる *

In order to reason about “reachable states,” Verus requires the user to supply an inductive invariant (lines 44–45). Verus checks that the invariant is actually inductive (i.e., that it holds true of any valid initial state, and that it is preserved across transitions), and it also checks that it implies all the safety conditions. In this case all these conditions happen to be straightforward, and the solver dispatches them easily. As always, more advanced cases might require manual proofs from the developer.


振る舞いはある程度変わる。パフォーマンスについて変更がある場合は、そこについて別途言及が必要。
deallocとstack、静的領域確保との差分についても調べる

