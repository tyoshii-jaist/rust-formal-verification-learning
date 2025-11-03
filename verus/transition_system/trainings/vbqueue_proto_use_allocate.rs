// use state_machines_macros::tokenized_state_machine;
//use vstd::atomic_ghost::*;
use vstd::raw_ptr::*;
//use vstd::cell::*;
//use vstd::map::*;
use vstd::{prelude::*, *};
use vstd::modes::*;
use vstd::layout::*;
use std::sync::Arc;

verus! {
global layout u8 is size == 1, align == 1;

pub enum ProducerState {
    Idle(nat),  // local copy of write か？
    Reserved(nat),
}

pub enum ConsumerState {
    Idle(nat),  // local copy of read か？
    Reading(nat),
}

tokenized_state_machine!{VBQueue<const N: usize> {
    fields {
        #[sharding(constant)]
        pub capacity: nat,

        #[sharding(variable)]
        pub buffer_perm: raw_ptr::PointsToRaw,

        #[sharding(variable)]
        pub buffer_dealloc_token: raw_ptr::Dealloc,

        #[sharding(variable)]
        pub write: nat,

        #[sharding(variable)]
        pub read: nat,

        #[sharding(variable)]
        pub last: nat,

        #[sharding(variable)]
        pub reserve: nat,

        #[sharding(variable)]
        pub read_in_progress: bool,

        #[sharding(variable)]
        pub write_in_progress: bool,

        #[sharding(variable)]
        pub already_split: bool,

        // Represents the local state of the single-producer
        #[sharding(variable)]
        pub producer: ProducerState,

        // Represents the local state of the single-consumer
        #[sharding(variable)]
        pub consumer: ConsumerState,
    }

    init! {
        initialize(n: nat, buffer_perm: raw_ptr::PointsToRaw, buffer_dealloc_token: raw_ptr::Dealloc) {
            init capacity = n;
            init buffer_perm = buffer_perm;
            init buffer_dealloc_token = buffer_dealloc_token;
            init write = 0;
            init read = 0;
            init last = n; // FIXME
            init reserve = 0;
            init read_in_progress = false;
            init write_in_progress = false;
            init already_split = false;
        }
    }
}}

pub struct VBBuffer<const N: usize> {
    buffer: *mut u8,
    write: AtomicU64<_, VBQueue::write, _>,
    read: AtomicU64<_, VBQueue::read, _>,
    last: AtomicU64<_, VBQueue::last, _>,
    reserve: AtomicU64<_, VBQueue::reserve, _>,
    read_in_progress: AtomicBool<_, VBQueue::read_in_progress, _>,
    write_in_progress: AtomicBool<_, VBQueue::write_in_progress, _>, 
    already_split: AtomicBool<_, VBQueue::already_split, _>, 

    instance: Tracked<VBQueue::Instance<T>>,
    buffer_perm: Tracked<raw_ptr::PointsToRaw>,
    buffer_dealloc_token: Tracked<raw_ptr::Dealloc>,
}

pub struct Producer<const N: usize> {
    vbq: Arc<VBBuffer<N>>,
    //producer: Tracked<VBQueue::producer>,
}
/*
impl<T> Producer<T> {
    pub closed spec fn wf(&self) -> bool {
        (*self.queue).wf()
            && self.producer@.instance_id() == (*self.queue).instance@.id()
            && self.producer@.value() == ProducerState::Idle(self.tail as nat)
            && (self.tail as int) < (*self.queue).buffer@.len()
    }
}
 */
pub struct Consumer<const N: usize> {
    vbq: Arc<VBBuffer<N>>,
}

/*
impl<T> Consumer<T> {
    pub closed spec fn wf(&self) -> bool {
        (*self.queue).wf()
            && self.consumer@.instance_id() === (*self.queue).instance@.id()
            && self.consumer@.value() === ConsumerState::Idle(self.head as nat)
            && (self.head as int) < (*self.queue).buffer@.len()
    }
}
 */
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
        layout_for_type_is_valid::<[u8; N]>();
        // TODO: 元の BBQueue は静的に確保している。
        let (buffer_ptr, buffer_perm, buffer_dealloc_token) = allocate(N, 1);

        // Initialize the queue
        Self {
            buffer: buffer_ptr,
            buffer_perm,
            buffer_dealloc_token
        }
    }

    fn try_split(self) -> Result<(Producer<N>, Consumer<N>),  &'static str>
    {
        // TODO: already_split の実装
        // FIXME:元の実装は Arc は使っていない。
        // また、buffer のゼロ化もしているが、こちらは今はやっていない。
        let vbbuffer_arc = Arc::new(self);
        Ok((
            Producer {
                vbq: vbbuffer_arc.clone(),
            },
            Consumer {
                vbq: vbbuffer_arc.clone(),
            }
        ))
    }

    fn experimental(&mut self) -> ()
        requires
            old(self).buffer.addr() as int % align_of::<[u8; N]>() as int == 0,
            old(self).buffer_perm@.is_range(old(self).buffer.addr() as int, size_of::<[u8; N]>() as int),
    {
        let tracked mut points_to;
        proof {
            // そのまま self.buffer_perm を使うと into_typed で move のエラーが出るので、swapしておく。
            let tracked bufp = self.buffer_perm.borrow();
            let tracked mut buffer_perm = raw_ptr::PointsToRaw::empty(bufp.provenance());
            tracked_swap(&mut buffer_perm, self.buffer_perm.borrow_mut());        
            //assume(size_of::<[u8; N]>() == N as int);
            assert(buffer_perm.dom() == crate::set_lib::set_int_range(
                self.buffer.addr() as int,
                self.buffer.addr() as int + size_of::<[u8; N]>() as int,
            ));
            assert(buffer_perm.is_range(self.buffer.addr() as int, size_of::<[u8; N]>() as int));
            points_to = buffer_perm.into_typed::<[u8; N]>(self.buffer.addr() as usize);

            assert(equal(points_to.opt_value(), MemContents::Uninit));
            //tracked_swap(&mut buffer_perm, self.buffer_perm.borrow_mut());
        }

        let ptr = self.buffer as *mut [u8; N];
        proof {
            assert(equal(points_to.ptr() as usize, self.buffer as usize));
            // FIXME: assume を取り除く
            assume(equal(points_to.ptr() as *mut u8, self.buffer as *mut u8));
        }
        ptr_mut_write(ptr, Tracked(&mut points_to), [0u8; N]);
        assert(equal(points_to.opt_value(), MemContents::Init([0u8; N])));


    }

    // TODO: try_release を実装する

    const fn capacity(&self) -> usize {
        N
    }
}

fn main() {
    let vbuf: VBBuffer<6> = VBBuffer::new();
}

}