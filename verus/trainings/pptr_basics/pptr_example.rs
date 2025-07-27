use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::raw_ptr::MemContents;

verus!{

fn main() {
    unsafe {
        // ALLOCATE
        // p: PPtr<u64>, points_to: PointsTo<u64>
        // TY: Trackedはタプル構造体でPointsTo<u64>を取り出してpoints_toに束縛している
        let (p, Tracked(mut points_to)) = PPtr::<u64>::empty();

        assert(points_to.mem_contents() === MemContents::Uninit);
        assert(points_to.pptr() == p);

        // unsafe { *p = 5; }
        p.write(Tracked(&mut points_to), 5);

        assert(points_to.mem_contents() === MemContents::Init(5));
        assert(points_to.pptr() == p);

        // let x = unsafe { *p };
        let x = p.read(Tracked(&points_to));

        assert(x == 5);

        // DEALLOCATE
        let y = p.into_inner(Tracked(points_to));

        assert(y == 5);
    }
}
}
