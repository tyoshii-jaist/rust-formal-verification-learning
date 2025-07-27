use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

verus!{
fn gcd(p: u32, q: u32) -> (r: u32)
    requires
        p > 0 && q > 0,
    ensures
        r <= p && r <= q
        && p % r == 0
        && q % r == 0
        && forall |i: nat|
            (i > 0 && (#[trigger] ((p as nat) % (i as nat)) == 0)
            && (#[trigger] ((q as nat) % (i as nat)) == 0)) ==> i <= r
{
    let mut i: u32 = if p < q {p} else {q};
    loop
        invariant
            i >= 1,
            i <= p && i <= q,
            forall |k: nat|
                (k > 0 && k <=p && k <= q && (#[trigger] ((p as nat) % (k as nat)) == 0)
                    && (#[trigger] ((q as nat) % (k as nat)) == 0))
                ==> k <= i,
        decreases
            i
    {
        if p % i == 0 && q % i == 0 {
            proof {
                // assertでSMTソルバーに事実確認を促すイメージ
                // 「k が p を割り切り、かつ、k が q を割り切るなら k は i 以下」を示したい。
                // i は p と q の小さいほうから始めてデクリメントしてきている。
                // このブロックに入った時点で i は p と q を初めて割り切っているので、p と q の最大公約数になることはわかる。
                // ただ、SMTソルバーは (by 以下なしでは) 納得していない。
                assert(forall |k: nat|
                    (k > 0 && (#[trigger] ((p as nat) % (k as nat)) == 0)
                        && (#[trigger] ((q as nat) % (k as nat)) == 0))
                    ==> k <= i
                ) by { // by はなくてもよい。SMTソルバーが納得しない場合にさらにかみ砕いた情報を与えるときに使う。
                    assert forall |k: nat| // assert forall ですべての k について追加で証明を足す。
                        (k > 0 &&
                        #[trigger] ((p as nat) % (k as nat)) == 0 &&
                        #[trigger] ((q as nat) % (k as nat)) == 0) implies k <= i
                    by {
                        // p % k == 0 のときに k は p 以下であるということを知らないことが原因で納得していなかったので、
                        // これを与えてあげると証明が通った。lemma_mod_is_zero は verus の証明ライブラリから持ってきた。
                        // Proof that if x % m is zero and x is positive, then x >= m.
                        // https://verus-lang.github.io/verus/verusdoc/vstd/arithmetic/div_mod/fn.lemma_mod_is_zero.html
                        lemma_mod_is_zero(p as nat, k as nat);
                        lemma_mod_is_zero(q as nat, k as nat);
                    }
                };
            };
            return i;
        }
        i -= 1;
    }
}

fn main() {}

}