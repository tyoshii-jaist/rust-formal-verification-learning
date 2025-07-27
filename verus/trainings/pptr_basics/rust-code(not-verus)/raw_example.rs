#![feature(box_as_ptr)]

use std::ptr;

struct Point {
    x: f64,
    y: f64,
}

fn main() {
    let mut value: u64 = 10;

    // 可変な生ポインタを作成
    let ptr: *mut u64 = &mut value;
    // let ptr = &raw mut value; でも作れるが、nightlyでしか利用できないらしい。

    unsafe {
        // 生ポインタ経由で値を読み出し、5 を足して書き戻す
        *ptr += 5;
    }

    println!("value = {}", value); // => 15


    let pt = Box::new(Point { x: 10.0, y: 0.0 });

    // https://doc.rust-lang.org/std/boxed/struct.Box.html#method.as_ptr

    /*
    unsafe {
        let raw_cnst: *const Point = Box::as_ptr(&pt);
        println!("value in unsafe block via raw= {}", (*raw_cnst).x);
    }
     */
    unsafe {
        let raw_cnst: *const Point = &*pt;
        println!("value in unsafe block via raw= {}", (*raw_cnst).x);
    }

    // https://doc.rust-lang.org/std/boxed/struct.Box.html#method.into_raw //消費 = move される
    let raw: *mut Point = Box::into_raw(pt);
    //println!("pt = {}", pt.x); // into_rawでmoveされているのでできない。

    unsafe {
        //let z = *raw; // error[E0507]: cannot move out of `*raw` which is behind a raw pointer
        let z = ptr::read(raw); // read を呼ぶと読み出して代入できる。これは強制的にメモリコピーしている。https://doc.rust-lang.org/std/ptr/fn.read.html
        println!("value in unsafe block via z = {}", z.x);
        println!("value in unsafe block via raw= {}", (*raw).x);
    }

    let xx = Box::<u64>::new(1);
    println!("value in unsafe block = {}", xx);
}
