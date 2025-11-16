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

    assert(block_ptr@.provenance == token.provenance());

    let ghost mut current_ptr = block_ptr;
    let tracked mut token = token;
    assert(token.is_range(block_ptr as int, length as int));
    assert(block_ptr as int + length <= usize::MAX + 1);
    let tracked mut points_to_map = Map::<nat, vstd::raw_ptr::PointsTo<u8>>::tracked_empty();

    for len in 0..length
        invariant
            len <= length,
            block_ptr as int + length <= usize::MAX + 1,
            token.is_range(block_ptr as int + len as int, length - len),
            forall |i: nat|
                i >= block_ptr as nat && i < block_ptr as nat + len as nat
                    ==> points_to_map.contains_key(i),
            forall |i: nat|
                i >= block_ptr as nat && i < block_ptr as nat + len as nat
                    ==> (points_to_map.index(i as nat).ptr() as nat == i as nat
                        && points_to_map.index(i as nat).ptr()@.provenance == token.provenance()),
            block_ptr@.provenance == token.provenance(),
        decreases
            length - len,
    {
        proof {
            let ghost b1_addr_t = block_ptr as int + len as int;
            let ghost b2_addr_t = b1_addr_t + 1;
            
            let tracked (b1, b2) = token.split(set_int_range(b1_addr_t, b2_addr_t as int));
            assert(b1.is_range(b1_addr_t as usize as int, size_of::<u8>() as int));

            let tracked b1_pointsto = b1.into_typed::<u8>(b1_addr_t as usize);
            token = b2;
            points_to_map.tracked_insert(b1_addr_t as nat, b1_pointsto);
            assert(points_to_map.contains_key(b1_addr_t as nat));
            assert(points_to_map.index(b1_addr_t as nat).ptr() as nat == b1_addr_t as nat);
            assert(b1_pointsto.ptr()@.provenance == b1.provenance());
            assert(b1.provenance() == token.provenance());
        }
    }


/*
    assert(forall |i: nat|
        i >= (block_ptr as usize) as nat && i < block_ptr as usize as nat + length as nat
            ==> points_to_map.contains_key(i));

    assert(points_to_map.contains_key((block_ptr as usize + 1 as nat) as nat));
    
    assert(block_ptr@.provenance == token.provenance());
    
    let addr = block_ptr as usize;
    let ptr = with_exposed_provenance::<u8>(addr, expose_provenance(block_ptr));
    assert(points_to_map.contains_key(ptr.addr() as nat));
    let tracked mut points_to = points_to_map.tracked_remove(ptr.addr() as nat);

    assert(points_to.ptr() as nat == ptr.addr() as nat);
    assert(block_ptr@.provenance == token.provenance());
    assert(ptr@.provenance == token.provenance());
    assert(points_to.ptr()@.provenance == ptr@.provenance);
    assert(points_to.ptr()@.metadata == ptr@.metadata);
    assert(points_to.ptr() == ptr);
    ptr_mut_write(ptr, Tracked(&mut points_to), 5);
    let val = ptr_ref(ptr, Tracked(&points_to));
    assert(val == 5);
*/
    for i in 0..length
        invariant
            i <= length,
            block_ptr as usize + length <= usize::MAX + 1,
            forall |j: nat|
                j >= block_ptr as nat + i as nat && j < block_ptr as nat + length as nat
                    ==> points_to_map.contains_key(j),
            forall |j: nat|
                j >= block_ptr as nat + i as nat && j < block_ptr as nat + length as nat
                    ==> (points_to_map.index(j as nat).ptr() as nat == j as nat
                        && points_to_map.index(j as nat).ptr()@.provenance == token.provenance()),
            block_ptr@.provenance == token.provenance(),
        decreases
            length - i,
    {
        let addr = block_ptr as usize + i;
        let ptr: *mut u8 = with_exposed_provenance(addr, expose_provenance(block_ptr));
        assert(points_to_map.contains_key(addr as nat));
        let tracked mut points_to = points_to_map.tracked_remove(addr as nat);

        assert(points_to.ptr() as nat == ptr.addr() as nat);
        assert(block_ptr@.provenance == token.provenance());
        assert(ptr@.provenance == token.provenance());
        assert(points_to.ptr()@.provenance == ptr@.provenance);
        assert(points_to.ptr()@.metadata == ptr@.metadata);
        assert(points_to.ptr() == ptr);
        assert(equal(points_to.ptr(), ptr));
        ptr_mut_write(ptr, Tracked(&mut points_to), 5);
        let val = ptr_ref(ptr, Tracked(&points_to));
        assert(val == 5);
    }
}
}