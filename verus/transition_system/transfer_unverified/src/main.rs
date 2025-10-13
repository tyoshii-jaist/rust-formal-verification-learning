use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;
use std::thread::spawn;

const TOTAL: u32 = 10;

fn main() {
    // 各変数を初期化
    let a = AtomicU32::new(TOTAL);
    let b = AtomicU32::new(0);

    let shared_a = Arc::new(a);
    let shared_b = Arc::new(b);

    let handle1 = {
        let shared_a = shared_a.clone();
        let shared_b = shared_b.clone();
        spawn(move || {
            loop {
                let current_a = shared_a.load(Ordering::SeqCst);
                if current_a == 0 {
                    break;
                }

                match shared_a.compare_exchange(current_a, current_a - 1, Ordering::SeqCst, Ordering::SeqCst) {
                    Ok(_) => {
                        shared_b.fetch_add(1, Ordering::SeqCst);
                        println!("Thread 1: Decremented A, Incremented B");
                    }
                    Err(_) => {
                        // 競合が発生した場合は再試行
                        continue;
                    }
                };
            };
        })
    };


    let handle2 = {
        let shared_a = shared_a.clone();
        let shared_b = shared_b.clone();
        spawn(move || {
            loop {
                let current_a = shared_a.load(Ordering::SeqCst);
                if current_a == 0 {
                    break;
                }

                match shared_a.compare_exchange(current_a, current_a - 1, Ordering::SeqCst, Ordering::SeqCst) {
                    Ok(_) => {
                        shared_b.fetch_add(1, Ordering::SeqCst);
                        println!("Thread 2: Decremented A, Incremented B");
                    }
                    Err(_) => {
                        // 競合が発生した場合は再試行
                        continue;
                    }
                };
            };
        })
    };

    match handle1.join() {
        Result::Ok(()) => {}
        _ => {
            return;
        }
    };

    match handle2.join() {
        Result::Ok(()) => {}
        _ => {
            return;
        }
    };

    let final_a = shared_a.load(Ordering::SeqCst);
    let final_b = shared_b.load(Ordering::SeqCst);
    println!("Final A: {}, Final B: {}", final_a, final_b);

}
