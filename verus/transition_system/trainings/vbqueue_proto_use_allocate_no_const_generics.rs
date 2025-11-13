use state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
//use vstd::atomic_ghost::*;
use vstd::raw_ptr::*;
//use vstd::cell::*;
//use vstd::map::*;
use vstd::{prelude::*, *};
//use vstd::modes::*;
use vstd::layout::*;
use std::sync::Arc;

verus! {
global layout u8 is size == 1, align == 1;

pub enum ProducerState {
    Idle((nat, nat)), // local copy of (write, reserved)
    Reserved((nat, nat)), // local copy of (write, reserved)
}

pub enum ConsumerState {
    Idle((nat, nat)),  // local copy of (read, write)
    Reading((nat, nat)), // local copy of (read, write)
}

tokenized_state_machine!{VBQueue {
    fields {
        #[sharding(constant)]
        pub start_addr: nat,

        #[sharding(constant)]
        pub length: nat,

        #[sharding(storage_map)]
        pub storage: Map<nat, raw_ptr::PointsTo<u8>>,

        #[sharding(storage_option)]
        pub buffer_dealloc: Option<raw_ptr::Dealloc>,

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
/*
        // Represents the local state of the single-producer
        #[sharding(variable)]
        pub producer: ProducerState,

        // Represents the local state of the single-consumer
        #[sharding(variable)]
        pub consumer: ConsumerState,
 */
    }

    /*
    #[invariant]
    pub fn buffer_perm_is_some(&self) -> bool {
        self.buffer_perm is Some
    }

    #[invariant]
    pub fn buffer_dealloc_is_some(&self) -> bool {
        self.buffer_dealloc is Some
    }
    */

    init! {
        initialize(start_addr: nat,
            length: nat,
            storage: Map<nat, raw_ptr::PointsTo<u8>>,
            buffer_dealloc: raw_ptr::Dealloc)
        {
            init start_addr = start_addr;
            init length = length;
            init storage = storage;
            init buffer_dealloc = Some(buffer_dealloc);
            init write = 0;
            init read = 0;
            init last = length;
            init reserve = 0;
            init read_in_progress = false;
            init write_in_progress = false;
            init already_split = false;
        }
    }

    
    #[inductive(initialize)]
    fn initialize_inductive(post: Self, start_addr: nat, length: nat, storage: Map<nat, raw_ptr::PointsTo<u8>>, buffer_dealloc: raw_ptr::Dealloc) {
        assert(post.buffer_dealloc is Some);
    }

    /*
    確かに error: unable to prove inherent safety condition: the value being guarded must be stored が出るな...
    https://github.com/verus-lang/verus/blob/7b6fdd861b43cbd88e886ad16c7af7cb1186ebc1/examples/scache/rwlock.rs#L308
     
    property!{
        guard_buffer_perm(perm: raw_ptr::PointsToRaw) {
            guard buffer_perm >= Some(perm);
        }
    }
    */

    transition!{
        try_split() {
            require(pre.already_split == false);

            update already_split = true;
        }
    }

    transition!{
        grant_start() {
            require(pre.write_in_progress == false);

            update write_in_progress = true;
        }
    }

    transition!{
        do_reserve(new_reserve: nat) {
            update reserve = new_reserve;
        }
    }

    transition!{
        grant_end() {
            update write_in_progress = false;
        }
    }

    /*
    transition!{
        withdraw_buffer_perm() {
            withdraw buffer_perm -= Some(let _) by {
                assume(pre.buffer_perm is Some);
            };
        }
    } */

    #[inductive(try_split)]
    fn try_split_inductive(pre: Self, post: Self) { }

    #[inductive(grant_start)]
    fn grant_start_inductive(pre: Self, post: Self) { }

    #[inductive(grant_end)]
    fn grant_end_inductive(pre: Self, post: Self) { }

    #[inductive(do_reserve)]
    fn do_reserve_inductive(pre: Self, post: Self, new_reserve: nat) { }
/*
    #[inductive(withdraw_buffer_perm)]
    fn withdraw_buffer_perm_inductive(pre: Self, post: Self) { }
 */
}}

struct_with_invariants!{
    pub struct VBBuffer {
        buffer: *mut u8,
        length: usize,
        write: AtomicU64<_, VBQueue::write, _>,
        read: AtomicU64<_, VBQueue::read, _>,
        last: AtomicU64<_, VBQueue::last, _>,
        reserve: AtomicU64<_, VBQueue::reserve, _>,
        read_in_progress: AtomicBool<_, VBQueue::read_in_progress, _>,
        write_in_progress: AtomicBool<_, VBQueue::write_in_progress, _>, 
        already_split: AtomicBool<_, VBQueue::already_split, _>,

        instance: Tracked<VBQueue::Instance>,
    }

    pub closed spec fn wf(&self) -> bool {
        /*
        predicate {
            &&& N == self.instance@.capacity
        } */

        invariant on write with (instance) is (v: u64, g: VBQueue::write) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
        }

        invariant on read with (instance) is (v: u64, g: VBQueue::read) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
        }

        invariant on last with (instance) is (v: u64, g: VBQueue::last) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
        }

        invariant on reserve with (instance) is (v: u64, g: VBQueue::reserve) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
        }

        invariant on read_in_progress with (instance) is (v: bool, g: VBQueue::read_in_progress) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v
        }

        invariant on write_in_progress with (instance) is (v: bool, g: VBQueue::write_in_progress) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v
        }

        invariant on already_split with (instance) is (v: bool, g: VBQueue::already_split) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v
        }
    }
}

pub struct Producer {
    vbq: Arc<VBBuffer>,
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
pub struct Consumer {
    vbq: Arc<VBBuffer>,
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
impl VBBuffer
{
    fn new(length: usize) -> (s: Self)
        requires
            valid_layout(length, 1),
            length > 0, // TODO: 元の BBQueue はこの制約は持っていない。0で使うことはないと思うが。
        ensures
        /*
            s.instance@.buffer_perm().is_range(s.buffer.addr() as int, length as int),
            s.instance@.buffer_dealloc()@
                == (DeallocData {
                    addr: s.buffer.addr(),
                    size: length as nat,
                    align: 1,
                    provenance: s.instance@.buffer_perm().provenance(),
                }),
            
        */
            s.buffer.addr() + length <= usize::MAX + 1,
            s.buffer.addr() as int % 1 as int == 0,
            //s.buffer@.provenance == s.instance@.split_guard_buffer_perm().provenance(),
            s.wf(),
    {
        // TODO: 元の BBQueue は静的に確保している。
        let (buffer_ptr, Tracked(buffer_perm), Tracked(buffer_dealloc)) = allocate(length, 1);
        //assert(buffer_ptr as usize + length <= usize::MAX + 1);
        assume(buffer_ptr.addr() + length <= usize::MAX); // FIXME!

        let tracked mut points_to_map = Map::<nat, raw_ptr::PointsTo<u8>>::tracked_empty();
        
        let tracked mut points_to_raw = buffer_perm;
        let tracked mut points_to_raw_u8: raw_ptr::PointsToRaw;
        let tracked mut p_rest: raw_ptr::PointsToRaw;

        let from_addr: usize = buffer_ptr.addr();
        let to_addr: usize = buffer_ptr.addr() + length;

        assert(points_to_raw.is_range(from_addr as int, length as int));

        for len in 0..length
            invariant
                len >= 0,
                len <= length - 1,
                points_to_raw.is_range(from_addr as int + len as int, length as int - len as int),
            decreases
                length - len,
        {
            proof {
                let addr = from_addr as int + len as int;
                let tracked splitted = points_to_raw.split(vstd::set_lib::set_int_range(addr as int, (addr + 1) as int));

                let tracked mut points_to = splitted.0.into_typed::<u8>(addr as usize);
                points_to_map.insert(addr as nat, points_to);
                assert(splitted.1.contains_range(addr as int, to_addr as int + 1));
                points_to_raw = splitted.1;
            }
        }
    
        let tracked (
            Tracked(instance),
            //Tracked(buffer_perm_token),
            //Tracked(buffer_dealloc_token),
            Tracked(write_token),
            Tracked(read_token),
            Tracked(last_token),
            Tracked(reserve_token),
            Tracked(read_in_progress_token),
            Tracked(write_in_progress_token),
            Tracked(already_split_token),
        ) = VBQueue::Instance::initialize(buffer_ptr as nat, length as nat, points_to_map, buffer_dealloc, points_to_map, Some(buffer_dealloc));

        let tracked_inst: Tracked<VBQueue::Instance> = Tracked(instance.clone());
        let write_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(write_token));
        let read_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(read_token));
        let last_atomic = AtomicU64::new(Ghost(tracked_inst), length as u64, Tracked(last_token));
        let reserve_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(reserve_token));
        let read_in_progress_atomic = AtomicBool::new(Ghost(tracked_inst), false, Tracked(read_in_progress_token));
        let write_in_progress_atomic = AtomicBool::new(Ghost(tracked_inst), false, Tracked(write_in_progress_token));
        let already_split_atomic = AtomicBool::new(Ghost(tracked_inst), false, Tracked(already_split_token));

        // Initialize the queue
        Self {
            buffer: buffer_ptr,
            length,
            write: write_atomic,
            read: read_atomic,
            last: last_atomic,
            reserve: reserve_atomic,
            read_in_progress: read_in_progress_atomic,
            write_in_progress: write_in_progress_atomic,
            already_split: already_split_atomic,
            instance: Tracked(instance),
        }
    }

    fn try_split(self) -> (res: Result<(Producer, Consumer),  &'static str>)
        requires
            self.wf(),
        ensures
            self.wf(),
            match res {
                Ok((prod, cons)) => prod.vbq.wf() && cons.vbq.wf(),
                Err(_) => true
            }
    {
        let already_splitted =
            atomic_with_ghost!(&self.already_split => swap(true);
                update prev -> next;
                returning ret;
                ghost already_split_token => {
                    if !ret {
                        assert(prev == false);
                        assert(next == true);
                        assert(already_split_token.value() == false);
                        let _ = self.instance.borrow().try_split(&mut already_split_token);
                        assert(already_split_token.value() == true);
                    };
                }
        );

        if already_splitted {
            return Err("already splitted");
        }

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
/*
    fn experimental(&mut self) -> ()
        requires
            old(self).buffer.addr() as int % align_of::<u8>() as int == 0,
            //old(self).instance@.buffer_perm().is_range(old(self).buffer.addr() as int, size_of::<u8>() as int),
    {
        let tracked mut points_to;
        proof {
            // そのまま self.buffer_perm を使うと into_typed で move のエラーが出るので、swapしておく。
            let tracked bufp = self.buffer_perm.borrow();
            let tracked mut buffer_perm = raw_ptr::PointsToRaw::empty(bufp.provenance());
            tracked_swap(&mut buffer_perm, self.buffer_perm.borrow_mut());        
            assert(buffer_perm.dom() == crate::set_lib::set_int_range(
                self.buffer.addr() as int,
                self.buffer.addr() as int + size_of::<u8>() as int,
            ));
            assert(buffer_perm.is_range(self.buffer.addr() as int, size_of::<u8>() as int));
            points_to = buffer_perm.into_typed::<u8>(self.buffer.addr() as usize);

            assert(equal(points_to.opt_value(), MemContents::Uninit));
            //tracked_swap(&mut buffer_perm, self.buffer_perm.borrow_mut());
        }

        let ptr = self.buffer as *mut u8;
        proof {
            assert(equal(points_to.ptr() as usize, self.buffer as usize));
            // FIXME: assume を取り除く
            assume(equal(points_to.ptr() as *mut u8, self.buffer as *mut u8));
        }
        ptr_mut_write(ptr, Tracked(&mut points_to), 0);
        assert(equal(points_to.opt_value(), MemContents::Init(0)));
    }
     */

    // TODO: try_release を実装する
}

struct GrantW {
    buf: *mut u8,
    vbq: Arc<VBBuffer>,
    to_commit: usize,
}

impl Producer {
    fn grant_exact(&mut self, sz: usize) -> Result<GrantW, &'static str>
        requires
            old(self).vbq.wf(),
    {
        let is_write_in_progress =
            atomic_with_ghost!(&self.vbq.write_in_progress => swap(true);
                update prev -> next;
                returning ret;
                ghost write_in_progress_token => {
                    if !ret {
                        assert(prev == false);
                        assert(next == true);
                        assert(write_in_progress_token.value() == false);
                        let _ = self.vbq.instance.borrow().grant_start(&mut write_in_progress_token);
                        assert(write_in_progress_token.value() == true);
                    };
                }
        );

        if is_write_in_progress {
            return Err("write in progress");
        }

        let write = atomic_with_ghost!(&self.vbq.write => load();
            ghost write_in_progress_token => {
            }
        );

        let read = atomic_with_ghost!(&self.vbq.read => load();
            ghost write_in_progress_token => {
            }
        );
        let max = self.vbq.length as u64;
        let already_inverted = write < read;
        assume(write + sz < u64::MAX);

        let start = if already_inverted {
            if (write + sz as u64) < read {
                // Inverted, room is still available
                write
            } else {
                // Inverted, no room is available
                atomic_with_ghost!(&self.vbq.write_in_progress => store(false);
                    ghost write_in_progress_token => {
                        let _ = self.vbq.instance.borrow().grant_end(&mut write_in_progress_token);
                        assert(write_in_progress_token.value() == false);
                    }
                );
                return Err("Inverted, no room is available");
            }
        } else {
            if write + sz as u64 <= max {
                // Non inverted condition
                write
            } else {
                // Not inverted, but need to go inverted

                // NOTE: We check sz < read, NOT <=, because
                // write must never == read in an inverted condition, since
                // we will then not be able to tell if we are inverted or not
                if (sz as u64) < read {
                    // Invertible situation
                    0
                } else {
                    // Not invertible, no space
                    atomic_with_ghost!(&self.vbq.write_in_progress => store(false);
                        ghost write_in_progress_token => {
                            let _ = self.vbq.instance.borrow().grant_end(&mut write_in_progress_token);
                            assert(write_in_progress_token.value() == false);
                        }
                    );
                    return Err("Insufficient size");
                }
            }
        };

        assume(start + sz < u64::MAX); // FIXME!
        // Safe write, only viewed by this task

        atomic_with_ghost!(&self.vbq.reserve => store(start + sz as u64);
            ghost reserve_token => {
                let _ = self.vbq.instance.borrow().do_reserve((start + sz) as nat, &mut reserve_token);
                assert(reserve_token.value() == start + sz as u64);
            }
        );

        /*
        proof {
            let tracked buffer_perm = self.vbq.instance.borrow().withdraw_buffer_perm();
        } */

        // This is sound, as UnsafeCell, MaybeUninit, and GenericArray
        // are all `#[repr(Transparent)]
        // let start_of_buf_ptr = inner.buf.get().cast::<u8>();
        // let grant_slice = unsafe { from_raw_parts_mut(start_of_buf_ptr.add(start), sz) };

        Ok (
            GrantW {
                buf: self.vbq.buffer,
                vbq: self.vbq.clone(),
                to_commit: sz,
            }
        )
    }
}

fn main() {
    let vbuf: VBBuffer = VBBuffer::new(6);
    let (mut prod, mut cons) = match vbuf.try_split() {
        Ok((prod, cons)) => (prod, cons),
        Err(_) => {
            return;
        }
    };

    // Request space for one byte
    let mut wgr = prod.grant_exact(1);
    
}

}