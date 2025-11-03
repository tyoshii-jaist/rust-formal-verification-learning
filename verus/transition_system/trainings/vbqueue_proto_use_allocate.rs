// use state_machines_macros::tokenized_state_machine;
//use vstd::atomic_ghost::*;
use vstd::raw_ptr::*;
//use vstd::cell::*;
//use vstd::map::*;
use vstd::{prelude::*, *};
use vstd::modes::*;
use vstd::layout::*;

verus! {
global layout u8 is size == 1, align == 1;

/*
tokenized_state_machine!{VBQueue<const N: usize> {
    fields {
        #[sharding(variable)]
        pub not_granted: raw_ptr::PointsToRaw;

        #[sharding(variable)]
        pub granted_write: raw_ptr::PointsToRaw;

        #[sharding(variable)]
        pub granted_write: raw_ptr::PointsToRaw;
    }

    init! {
        initialize(provenance: raw_ptr::Provenance) {
            init not_granted = raw_ptr
        }
    }
}}
*/

pub struct VBBuffer<const N: usize> {
    buffer: *mut u8,
    buffer_perm: Tracked<raw_ptr::PointsToRaw>,
    buffer_dealloc_token: Tracked<raw_ptr::Dealloc>,
}

impl<const N: usize> VBBuffer<N>
{
    fn new() -> (s: Self)
        requires
            valid_layout(N, 1),
            N > 0, // TODO: 元の BBQueue はこの制約は持っていない。0で使うことはないと思うが。
        ensures
            s.buffer_perm@.is_range(s.buffer.addr() as int, N as int),
            s.buffer.addr() + N <= usize::MAX + 1,
            s.buffer_dealloc_token@@
                == (DeallocData {
                    addr: s.buffer.addr(),
                    size: N as nat,
                    align: 1,
                    provenance: s.buffer_perm@.provenance(),
                }),
            s.buffer.addr() as int % 1 as int == 0,
            s.buffer@.provenance == s.buffer_perm@.provenance(),
    {
        layout_for_type_is_valid::<u8>();
        // TODO: 元の BBQueue は静的に確保している。
        let (buffer_ptr, buffer_perm, buffer_dealloc_token) = allocate(N, 1);

        // Initialize the queue
        Self {
            buffer: buffer_ptr,
            buffer_perm,
            buffer_dealloc_token
        }
    }

    fn try_split(&mut self) -> ()
        requires
            old(self).buffer.addr() as int % align_of::<[u8; N]>() as int == 0,
            old(self).buffer_perm@.is_range(old(self).buffer.addr() as int, size_of::<[u8; N]>() as int),
    {
        proof {
            // そのまま self.buffer_perm を使うと into_typed で move のエラーが出るので、swapしておく。
            let tracked bufp = self.buffer_perm.borrow();
            let tracked mut buffer_perm = raw_ptr::PointsToRaw::empty(bufp.provenance());
            tracked_swap(&mut buffer_perm, self.buffer_perm.borrow_mut());        
            //assume(size_of::<[u8; N]>() == N as int);
            assert(buffer_perm.is_range(self.buffer.addr() as int, size_of::<[u8; N]>() as int));
            let tracked points_to = buffer_perm.into_typed::<[u8; N]>(self.buffer.addr() as usize);

            //tracked_swap(&mut buffer_perm, self.buffer_perm.borrow_mut());
        }
    }

    const fn capacity(&self) -> usize {
        N
    }
}

fn main() {

    let vbuf: VBBuffer<6> = VBBuffer::new();
}

}