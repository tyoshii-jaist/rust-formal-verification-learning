use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::layout::*;
use vstd::set_lib::*;

// allocateでu32(4バイト)2つ分の8バイトの領域を確保し、それぞれの値を生ポインタを経由して書き込む例を書いてみる。

verus!{

global layout u32 is size == 4, align == 4;

fn main() {
    layout_for_type_is_valid::<u32>();

    let (block_ptr, Tracked(token2), Tracked(dealloc2)) = allocate(8, 4);

    let ghost b2_addr_t = block_ptr as int + 4 as int;
    //assume(b2_addr_t <= usize::MAX); 
    let tracked (b1, b2) = token2.split(set_int_range(block_ptr as int, b2_addr_t as int));
 
    let tracked mut b1_pointsto = b1.into_typed::<u32>(block_ptr as usize);
    let tracked mut b2_pointsto = b2.into_typed::<u32>(b2_addr_t as usize);
    let b1_ptr = block_ptr as *mut u32;    
    let b2_ptr = with_exposed_provenance(block_ptr as usize + 4, expose_provenance(block_ptr));

    assert(equal(b1_pointsto.ptr(), b1_ptr));
    assert(equal(b2_pointsto.ptr(), b2_ptr));
    assert(equal(b1_pointsto.opt_value(), MemContents::Uninit));
    assert(equal(b2_pointsto.opt_value(), MemContents::Uninit));

    ptr_mut_write(b1_ptr, Tracked(&mut b1_pointsto), 555);
    ptr_mut_write(b2_ptr, Tracked(&mut b2_pointsto), 666);
    assert(equal(b1_pointsto.ptr(), b1_ptr));
    assert(equal(b1_pointsto.opt_value(), MemContents::Init(555)));
    assert(equal(b2_pointsto.ptr(), b2_ptr));
    assert(equal(b2_pointsto.opt_value(), MemContents::Init(666)));

    let b1_val = ptr_ref(b1_ptr, Tracked(&b1_pointsto));
    assert(equal(*b1_val, 555));
    let b2_val = ptr_ref(b2_ptr, Tracked(&b2_pointsto));
    assert(equal(*b2_val, 666));

    let b1_read = ptr_mut_read(b1_ptr, Tracked(&mut b1_pointsto)); 
    assert(equal(b1_pointsto.ptr(), b1_ptr));
    assert(equal(b1_pointsto.opt_value(), MemContents::Uninit)); // moved?
    assert(equal(b1_read, 555));
    let b2_read = ptr_mut_read(b2_ptr, Tracked(&mut b2_pointsto));
    assert(equal(b2_pointsto.ptr(), b2_ptr));
    assert(equal(b2_pointsto.opt_value(), MemContents::Uninit)); // moved?
    assert(equal(b2_read, 666));
}
}