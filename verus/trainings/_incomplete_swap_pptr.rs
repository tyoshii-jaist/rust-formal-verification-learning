use vstd::prelude::*;
use vstd::simple_pptr::PPtr; // Permissioned Pointer, A PPtr is equvialent to its usize-based address.
// https://verus-lang.github.io/verus/verusdoc/vstd/simple_pptr/struct.PPtr.html
// The perm: PointsTo<V> object tracks two pieces of data:
// 
// perm.pptr() is the pointer that the permission is associated to.
// perm.mem_contents() is the memory contents, which is one of either:
// MemContents::Uninit if the memory pointed-to by by the pointer is uninitialized.
// MemContents::Init(v) if the memory points-to the the value v.

verus!{
fn swap_values(x: PPtr<u32>, y: PPtr<u32>)
    requires
        x.is_valid(),
        y.is_valid(),
        x.as_usize() != y.as_usize(),
    ensures
        x.read() == y.initial_value(),
        y.read() == x.initial_value()
{
    // 値を一時変数に保存
    let temp = x.read();

    // 値をスワップ
    x.write(y.read());
    y.write(temp);
}

fn main() {}
}
