/*
struct Point {
    x: f64,
    y: f64,
} */

fn main() {
    let mut x = 42;

    x = 43;

    let y = x; // move here
    println!("y = {}", y);

    let mut mx = 43; // これの左側はmxの値は変えられることを示す。
    mx = 45;
    let rmx = &mut mx; // これの右辺の mut は"可変"参照を示す。
    *rmx = 55;
    println!("mx = {}", mx);

    let hx = Box::<u64>::new(122);
    let hx2 = hx;
    println!("hx = {}", hx2);
}