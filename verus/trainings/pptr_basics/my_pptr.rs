use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::raw_ptr::MemContents;

verus!{

// TY: Copyを実装していない構造体の例として使う
struct Point {
    x: u64,
    y: u64,
}

// TY: コピーを返す。PPtr#readも同様。https://verus-lang.github.io/verus/verusdoc/vstd/simple_pptr/struct.PPtr.html#method.read
// TY: そもそもdereferenceとは？
// TY: https://doc.rust-jp.rs/book-ja/ch19-01-unsafe-rust.html#%E7%94%9F%E3%83%9D%E3%82%A4%E3%83%B3%E3%82%BF%E3%82%92%E5%8F%82%E7%85%A7%E5%A4%96%E3%81%97%E3%81%99%E3%82%8B
// TY: https://doc.rust-jp.rs/book-ja/ch15-02-deref.html#%E5%8F%82%E7%85%A7%E5%A4%96%E3%81%97%E6%BC%94%E7%AE%97%E5%AD%90%E3%81%A7%E5%80%A4%E3%81%BE%E3%81%A7%E3%83%9D%E3%82%A4%E3%83%B3%E3%82%BF%E3%82%92%E8%BF%BD%E3%81%84%E3%81%8B%E3%81%91%E3%82%8B
// TY: Derefトレイトで実装される。moveされるか参照が返されるかは実装による。
// TY: - 基本的に safe rust では参照は有効であることをcompirerが保証している
fn read_val<V: Copy>(p: &PPtr<V>, Tracked(perm): Tracked<&PointsTo<V>>) -> (r: V)
    requires
        perm.pptr() == p,
        perm.is_init(),
    ensures
        perm.mem_contents() == MemContents::Init(r),
{
    return p.read(Tracked(perm));
}

fn main() {
    unsafe {
        // ALLOCATE
        // p: PPtr<u64>, points_to: PointsTo<u64>
        // TY: Trackedはタプル構造体でPointsTo<u64>を取り出してpoints_toに束縛している
        // TY: empty() はヒープにメモリを割り当てる。初期化しない。
        // TY: つまり let v = Box::<V>::new(Uninit); let p: *mut u64 = &mut *v; のようなイメージ。
        let (p, Tracked(mut points_to)) = PPtr::<u64>::empty();

        assert(points_to.mem_contents() === MemContents::Uninit);
        assert(points_to.pptr() == p);


        // unsafe { *p = 5; }
        p.write(Tracked(&mut points_to), 5);

        assert(points_to.mem_contents() === MemContents::Init(5));
        assert(points_to.pptr() == p);

        let z = p.read(Tracked(&points_to));
        assert(z == 5);
    }
}
}
