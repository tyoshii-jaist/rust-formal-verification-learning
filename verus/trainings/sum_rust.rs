fn sum_up_to(n: u32) -> u64 {
    let mut r = 0u64;

    for i in 0..n+1 {
        r += i as u64;
        println!("i:{} r: {} recs: {}", i, r, sum_up_to_recursive(i));
    }
    r
}

fn sum_up_to_recursive(n: u32) -> u64 {
    if n == 0 {
        0
    } else {
        n as u64 + sum_up_to_recursive(n - 1)
    }
}

fn main() {
    println!("{}", sum_up_to(10));
    println!("{}", sum_up_to_recursive(10));
}