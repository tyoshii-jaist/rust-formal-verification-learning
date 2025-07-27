use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::layout::*;

verus!{
global layout u32 is size == 4, align == 4;

fn main() {
    // u32のバイト数など環境情報を提供
    layout_for_type_is_valid::<u32>();

    // https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/fn.allocate.html
    // メモリを割り当てる。ptr (*mut T)とPointsToRawトークンと Dealloc用トークンが返される
    let (ptr, Tracked(token), Tracked(dealloc)) = allocate(4, 4);

    // PointsToRaw#into_typed で PointsTo に変換できる。
    let tracked mut token = token.into_typed::<u32>(ptr as usize);
    let ptr = ptr as *mut u32;

    assert(equal(token.ptr(), ptr));
    assert(equal(token.opt_value(), MemContents::Uninit));

    ptr_mut_write(ptr, Tracked(&mut token), 5);
    assert(equal(token.ptr(), ptr));
    assert(equal(token.opt_value(), MemContents::Init(5)));

    let t = ptr_ref(ptr, Tracked(&token));
    assert(equal(*t, 5));

    let x = ptr_mut_read(ptr, Tracked(&mut token));
    assert(equal(token.ptr(), ptr));
    assert(equal(token.opt_value(), MemContents::Uninit));
    assert(equal(x, 5));

    let tracked token = token.into_raw();
    deallocate(ptr as *mut u8, 4, 4, Tracked(token), Tracked(dealloc));
}
}