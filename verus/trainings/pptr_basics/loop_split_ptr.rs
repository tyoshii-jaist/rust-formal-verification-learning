use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::layout::*;
use vstd::set_lib::*;

// allocateでu8(1バイト)8つ分の8バイトの領域を確保し、一つ一つ分解してそれぞれのpoints_toを作る例

verus!{

global layout u8 is size == 1, align == 1;

fn main() {
    layout_for_type_is_valid::<u8>();
    let length: usize = 2;

    let (block_ptr, Tracked(token), Tracked(dealloc)) = allocate(length, 1);

    proof {
        let ghost b2_addr_t = block_ptr as int + 1 as int;
        //assume(b2_addr_t <= usize::MAX); 
        let tracked (b1, b2) = token.split(set_int_range(block_ptr as int, b2_addr_t as int));
    
        let tracked mut b1_pointsto = b1.into_typed::<u8>(block_ptr as usize);
        let tracked mut b2_pointsto = b2.into_typed::<u8>(b2_addr_t as usize);
    }
    let b1_ptr = block_ptr as *mut u8;    
    let b2_ptr: *mut u8 = with_exposed_provenance(block_ptr as usize + 1, expose_provenance(block_ptr));
}
}