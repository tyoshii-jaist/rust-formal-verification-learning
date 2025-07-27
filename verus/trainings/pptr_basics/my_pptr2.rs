use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::raw_ptr::MemContents;

verus!{
// TY: PPtrはヒープ領域に割り当てられた生ポインターのラッパー。
// TY: アクセスの際にゴーストなパーミッショントークンであるPointsToトークンが必要になる。
// TY: 使い方の理解のために簡単なコードを書く。

// p: PPtrの指す値を読みだす。(参照)
fn read_val<V: Copy>(p: &PPtr<V>, Tracked(perm): Tracked<&PointsTo<V>>) -> (r: V)
    requires
        perm.pptr() == p,
        perm.is_init(),
    ensures
        perm.mem_contents() == MemContents::Init(r),
{
    p.read(Tracked(perm)) // VにCopyを要求している。Copyされた値が返る。
}

// p: PPtrの指す値に書き込む。(代入)
fn write_val<V: Copy>(p: PPtr<V>, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V)
    requires
        old(perm).pptr() == p,
    ensures
        perm.pptr() == p,
        perm.mem_contents() == MemContents::Init(in_v),
        perm.is_init(),
{
    p.write(Tracked(perm), in_v)
}

// p: PPtrの指す値に加算する (参照と代入)
// u64 に限定している。AddトレイトのVerusでの使い方がわからない。
//fn add_val<V: Copy + Add<V, Output = V>>(p: PPtr<V>, Tracked(perm): Tracked<&mut PointsTo<V>>, to_add: V) -> (r: V)
fn add_val(p: PPtr<u64>, Tracked(perm): Tracked<&mut PointsTo<u64>>, to_add: u64) -> (r: u64)
    requires
        old(perm).pptr() == p,
        old(perm).is_init(),
        old(perm).value() + to_add <= u64::MAX,
    ensures
        perm.value() == (old(perm).value() + to_add) as int,
        perm.is_init(),
        perm.pptr() == p,
{
    let current = p.read(Tracked(perm));
    p.write(Tracked(perm), current + to_add);
    p.read(Tracked(perm))
}

// 値のswap
fn swap_val<V: Copy>(p1: PPtr<V>, Tracked(perm1): Tracked<&mut PointsTo<V>>, p2: PPtr<V>, Tracked(perm2): Tracked<&mut PointsTo<V>>)
    requires
        old(perm1).pptr() == p1,
        old(perm2).pptr() == p2,
        old(perm1).is_init(),
        old(perm2).is_init(),
    ensures
        perm1.pptr() == p1,
        perm2.pptr() == p2,
        perm1.is_init(),
        perm2.is_init(),
        old(perm1).value() == perm2.value(),
        old(perm2).value() == perm1.value(),
{
    let tmp = p1.read(Tracked(perm1));
    p1.write(Tracked(perm1), p2.read(Tracked(perm2)));
    p2.write(Tracked(perm2), tmp);
}

fn main() {
    unsafe {
        let (p, Tracked(mut points_to)) = PPtr::<u64>::empty();

        // unsafe { *p = 5; }
        write_val(p, Tracked(&mut points_to), 5);

        // let x = unsafe { *p };
        let x = read_val(&p, Tracked(&points_to));
        assert(x == 5);

        // unsafe { *p += 10; }
        add_val(p, Tracked(&mut points_to), 10);

        // let y = unsafe { *p };)
        let y = read_val(&p, Tracked(&points_to));
        assert(y == 15);

        let (p2, Tracked(mut points_to2)) = PPtr::<u64>::new(25);
        swap_val(p, Tracked(&mut points_to), p2, Tracked(&mut points_to2));
        let t = p.read(Tracked(&points_to));
        assert(t == 25);
        let t2 = p2.read(Tracked(&points_to2));
        assert(t2 == 15);
    }
}
}
