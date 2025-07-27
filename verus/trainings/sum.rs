use vstd::prelude::*;

verus!{
spec fn sum_up_to(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        n + sum_up_to((n - 1) as nat)
    }
}

fn sum_up_to_impl(n: u32) -> (r: u64)
    ensures
        r == sum_up_to(n as nat)
{
    let mut r = 0u64;
    for i in 1u64..(n as u64 + 1) 
        invariant
            r <= u32::MAX * i,
            r == sum_up_to((i - 1) as nat),
    {
        r += i;
    }
    r
}

fn compose_sum_up_to_impl(n1: u32, n2: u32) -> (r: u64)
    requires
        sum_up_to(n1 as nat) + sum_up_to(n2 as nat) <= u64::MAX,
    ensures
        r == sum_up_to(n1 as nat) + sum_up_to(n2 as nat)
{
    sum_up_to_impl(n1) + sum_up_to_impl(n2)
}

fn main() {}
}