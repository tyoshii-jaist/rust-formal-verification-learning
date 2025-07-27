fn gcd(p: u32, q: u32) -> u32 {
    let mut i: u32 = if p < q {p} else {q};

    loop {
        if p % i == 0 && q % i == 0 {
            return i;
        }
        i -= 1;
    }
}

fn main() {
    for p in vec![(12, 24), (3, 2), (18, 24)] {
        println!("{}, {} gcd {}", p.0, p.1, gcd(p.0, p.1));
    }
}