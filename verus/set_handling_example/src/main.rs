use vstd::prelude::*;
use vstd::set_lib::*;

verus!{

fn main() {
    proof {
        let set_u = set_int_range(0, 100);
        assert((forall |i: int| i >= 0 && i < 100 ==> set_u.contains(i)));
        let set_a = set_int_range(0, 4);
        assert((forall |i: int| i >= 0 && i < 4 ==> set_a.contains(i)));

        let set_b = set_u.difference(set_a);
        assert((forall |i: int| i >= 5 && i < 100 ==> set_b.contains(i)));
    }

}
}