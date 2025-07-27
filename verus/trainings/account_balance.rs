use vstd::prelude::*;

verus!{
spec fn always_non_negative(s: Seq<i64>) -> bool
{
    forall|i: int| 0 <= i <= s.len() ==> sum(#[trigger] s.take(i)) >= 0    
}

spec fn sum(s: Seq<i64>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        sum(s.drop_last()) + s.last()
    }
}

fn non_negative(operations: &[i64]) -> (r: bool)
    ensures
        r == always_non_negative(operations@),
{
    let mut s = 0i128;
    for i in 0usize..operations.len()
        invariant
            i64::MIN <= s <= i64::MAX * i,
            s == sum(operations@.take(i as int)),
            forall|j: int| 0 <= j <= i ==> sum(#[trigger] operations@.take(j)) >= 0,
    {
        assert(operations@.take(i as int) =~= operations@.take(i as int + 1).drop_last());
        s = s + operations[i] as i128;
        if s < 0 {
            return false;
        }
    }
    true
}

fn main() {}
}