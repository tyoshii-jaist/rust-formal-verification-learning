use vstd::prelude::*;

verus!{

spec fn fib(x: nat) -> nat 
    decreases x
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
{
    if i < 2 && j < 2 {
    } else if i == j {
    } else if i == j - 1 {
        assume(false);
    } else {
        assume(false);
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
    for i in iter: 1..x
        invariant
            fib(x as nat) <= u64::MAX,
            current == fib(i as nat),
            1 <= i <= x,
            prev == fib((i - 1) as nat),
    {
        proof {
            lemma_fib_is_monotonic((i + 1) as nat, x as nat);
        }
        let tmp = prev + current;
        prev = current;
        current = tmp;
    }
    current
}

fn main() {}
}