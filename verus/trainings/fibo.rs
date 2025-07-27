use vstd::prelude::*;

verus!{

spec fn fib(x: nat) -> nat 
    decreases x // 原子帰納関数の存在性定理に基づいている。項の数が減ることを示さないといけない？スコット。while/for 等のループについても説明している。ドメインセオリー
{
    if x == 0 {
        0
    } else if x == 1 {
        1
    } else {
        fib((x - 1) as nat) + fib((x - 2) as nat)
    }
}

proof fn lemma_fib_is_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        fib(i) <= fib(j),
    decreases j - i,
{
    if i < 2 && j < 2 {
    } else if i == j {
    } else if i == j - 1 {
        assert(fib(j) == fib((j - 2) as nat) + fib((j - 1) as nat));
    } else {
        lemma_fib_is_monotonic(i, (j - 1) as nat);
        lemma_fib_is_monotonic(i, (j - 2) as nat);
    }
}

fn fib_impl(x: u64) -> (result: u64) 
    requires
        fib(x as nat) <= u64::MAX
    ensures
        result == fib(x as nat) 
{
    if x == 0 {
        return 0;
    }

    let mut prev: u64 = 0;
    let mut current: u64 = 1;
    let mut i = 1;
    while i < x
        invariant
            fib(x as nat) <= u64::MAX,
            1 <= i <= x,
            current == fib(i as nat),
            prev == fib((i - 1) as nat),
        decreases
            x - i
    {
        i += 1;
        proof {
            lemma_fib_is_monotonic(i as nat, x as nat);
        }
        let tmp = prev + current; // この値は fib(i + 1) (i <= x) なので fib(x) <= u64::MAX にはならない。ということを示す必要がある。  
        prev = current;
        current = tmp;
    }
    current
}

#[verifier::external]
fn main() {
    println!("{}", fib_impl(10));
}
}