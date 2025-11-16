use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::layout::*;
use vstd::set_lib::*;

// allocateでu8(1バイト)8つ分の8バイトの領域を確保し、一つ一つ分解してそれぞれのpoints_toを作る例

verus!{

global layout u8 is size == 1, align == 1;

fn main() {
    layout_for_type_is_valid::<u8>();
    let length: usize = 64;

    let (block_ptr, Tracked(token), Tracked(dealloc)) = allocate(length, 1);

    assert(block_ptr@.provenance == token.provenance());

    let tracked mut token = token;
    assert(token.is_range(block_ptr as int, length as int));
    assert(block_ptr as int + length * size_of::<u8>() <= usize::MAX + 1);
    let tracked mut points_to_map = Map::<nat, vstd::raw_ptr::PointsTo<u8>>::tracked_empty();

    for len in 0..length
        invariant
            len <= length,
            block_ptr as int + length * size_of::<u8>() <= usize::MAX + 1,
            token.is_range(block_ptr as int + len * size_of::<u8>() as int, length * size_of::<u8>() - len),
            forall |i: nat|
                i >= block_ptr as nat && i < block_ptr as nat + len * size_of::<u8>() as nat
                    ==> points_to_map.contains_key(i),
            forall |i: nat|
                i >= block_ptr as nat && i < block_ptr as nat + len * size_of::<u8>() as nat
                    ==> (points_to_map.index(i as nat).ptr() as nat == i as nat
                        && points_to_map.index(i as nat).ptr()@.provenance == token.provenance()),
            block_ptr@.provenance == token.provenance(),
        decreases
            length - len,
    {
        proof {
            let ghost range_start_addr = block_ptr as int + len * size_of::<u8>() as int;
            let ghost range_end_addr = range_start_addr + 1 * size_of::<u8>();
            
            let tracked (top, rest) = token.split(set_int_range(range_start_addr, range_end_addr as int));
            assert(top.is_range(range_start_addr as usize as int, size_of::<u8>() as int));

            let tracked top_pointsto = top.into_typed::<u8>(range_start_addr as usize);
            token = rest;
            points_to_map.tracked_insert(range_start_addr as nat, top_pointsto);
            assert(points_to_map.contains_key(range_start_addr as nat));
            assert(points_to_map.index(range_start_addr as nat).ptr() as nat == range_start_addr as nat);
            assert(top_pointsto.ptr()@.provenance == top.provenance());
            assert(top.provenance() == token.provenance());
        }
    }

    for i in 0..length
        invariant
            i <= length,
            block_ptr as usize + length * size_of::<u8>() <= usize::MAX + 1,
            block_ptr@.provenance == token.provenance(),
            forall |j: nat|
                j >= block_ptr as nat + i * size_of::<u8>() as nat && j < block_ptr as nat + length * size_of::<u8>() as nat
                    ==> (
                        points_to_map.contains_key(j)
                        && points_to_map.index(j as nat).ptr() as nat == j as nat
                        && points_to_map.index(j as nat).ptr()@.provenance == token.provenance()),
        decreases
            length - i,
    {
        let addr = block_ptr as usize + i; // * size_of::<u8>();
        let ptr: *mut u8 = with_exposed_provenance(addr, expose_provenance(block_ptr));
        assert(points_to_map.contains_key(addr as nat));
        let tracked mut points_to = points_to_map.tracked_remove(addr as nat);

        assert(equal(points_to.ptr(), ptr));
        ptr_mut_write(ptr, Tracked(&mut points_to), 5);
        let val = ptr_ref(ptr, Tracked(&points_to));
        assert(val == 5);
    }
}
}