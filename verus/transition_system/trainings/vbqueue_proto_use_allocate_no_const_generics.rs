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
    Idle(nat),
    WriteFilled(nat),
    WriteAndReadFilled((nat, nat)), // (start, start + sz)
    Reserved((nat, nat)), // (start, start + sz)
}

pub enum ConsumerState {
    Idle(nat),
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

        // Represents the local state of the single-producer
        #[sharding(variable)]
        pub producer: ProducerState,

        // Represents the local state of the single-consumer
        #[sharding(variable)]
        pub consumer: ConsumerState,
    }

    #[invariant]
    pub fn valid_storage_all(&self) -> bool {
        match self.producer {
            ProducerState::Reserved(_) => {
                true
            },
            _ => {
                forall |i: nat|
                    i >= self.start_addr && i < self.start_addr + self.length * size_of::<u8>() as nat
                        ==> self.storage.contains_key(i) && self.storage.dom().contains(i)
            },
        }
    }

    #[invariant]
    pub fn valid_producer_local_state(&self) -> bool {
        match self.producer {
            ProducerState::Idle(w) => self.write == w, //&& self.reserve == w,
            ProducerState::WriteFilled(w) => self.write == w,
            ProducerState::WriteAndReadFilled((w, _)) => self.write == w,
            ProducerState::Reserved((_, r)) => self.reserve == r,
        }
    }

    init! {
        initialize(start_addr: nat,
            length: nat,
            storage: Map<nat, raw_ptr::PointsTo<u8>>,
            buffer_dealloc: raw_ptr::Dealloc)
        {
            require(
                forall |i: nat|
                    i >= start_addr && i < start_addr + length * size_of::<u8>() as nat
                        ==> storage.contains_key(i) && storage.dom().contains(i)
            );

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

            init producer = ProducerState::Idle(0);
            init consumer = ConsumerState::Idle(0);
        }
    }

    
    #[inductive(initialize)]
    fn initialize_inductive(post: Self, start_addr: nat, length: nat, storage: Map<nat, raw_ptr::PointsTo<u8>>, buffer_dealloc: raw_ptr::Dealloc) {
        assert(post.buffer_dealloc is Some);
        assert(
            forall |i: nat|
                i >= post.start_addr && i < post.start_addr + post.length * size_of::<u8>() as nat
                    ==> post.storage.contains_key(i)
        );
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
        grant_fill_write() {
            require(pre.producer is Idle);

            update producer = ProducerState::WriteFilled(pre.write);
        }
    }

    transition!{
        grant_fill_read() {
            require(pre.producer is WriteFilled);

            update producer = ProducerState::WriteAndReadFilled((pre.producer->WriteFilled_0, pre.read));
        }
    }

    transition!{
        do_reserve(start: nat, sz: nat) {
            require(start + sz <= pre.length);
            require(pre.producer is WriteAndReadFilled);

            update reserve = start + sz;

            birds_eye let withdraw_range_map: Map<nat, raw_ptr::PointsTo<u8>> = Map::new(
                |i: nat| start + pre.start_addr <= i && i < start + sz + pre.start_addr,
                |i: nat| pre.storage[i]);

            withdraw storage -= (withdraw_range_map) by {
                assert (withdraw_range_map.submap_of(pre.storage)) by {
                    assert(Set::new(|i: nat| i >= start + pre.start_addr && i < start + sz  + pre.start_addr).subset_of(Set::new(|i: nat| i >= pre.start_addr && i < pre.start_addr + pre.length)));
                    assert(Set::new(|i: nat| i >= pre.start_addr && i < pre.start_addr + pre.length).subset_of(pre.storage.dom()));
                    assert(withdraw_range_map.dom().subset_of(Set::new(|i: nat| i >= start + pre.start_addr && i < start + sz + pre.start_addr)));
                    assert(pre.valid_storage_all());
                }
            };
            
            update producer = ProducerState::Reserved((start, start + sz));
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

    #[inductive(grant_fill_write)]
    fn grant_fill_write_inductive(pre: Self, post: Self) {
        assert(post.producer is WriteFilled);
    }

    #[inductive(grant_fill_read)]
    fn grant_fill_read_inductive(pre: Self, post: Self) {
        assert(post.producer is WriteAndReadFilled);
    }

    #[inductive(grant_end)]
    fn grant_end_inductive(pre: Self, post: Self) { }

    #[inductive(do_reserve)]
    fn do_reserve_inductive(pre: Self, post: Self, start: nat, sz: nat) {
        assert(post.producer is Reserved);
        assert(post.producer->Reserved_0.1 == post.reserve);
    }
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
    producer: Tracked<VBQueue::producer>,
}

impl Producer {
    pub closed spec fn wf(&self) -> bool {
        (*self.vbq).wf()
            && self.producer@.instance_id() == (*self.vbq).instance@.id()
            && self.producer@.value() is Idle
            //&& (self.tail as int) < (*self.queue).buffer@.len()
    }
}

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
    fn new(length: usize) -> (r:(Self, Tracked<VBQueue::producer>,Tracked<VBQueue::consumer>))
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
            r.0.buffer.addr() + length <= usize::MAX + 1,
            r.0.buffer.addr() as int % 1 as int == 0,
            //s.buffer@.provenance == s.instance@.split_guard_buffer_perm().provenance(),
            r.0.wf(),
            r.0.instance@.id() == r.1@.instance_id(),
            r.1@.value() is Idle,
    {
        // TODO: 元の BBQueue は静的に確保している。
        let (buffer_ptr, Tracked(buffer_perm), Tracked(buffer_dealloc)) = allocate(length, 1);

        // allocate で得た buffer_perm (PointsToRaw) を u8 1バイトごとに分割して、addr => PointsTo の Map として格納する
        let tracked mut buffer_perm = buffer_perm;
        assert(buffer_perm.is_range(buffer_ptr as int, length as int));
        assert(buffer_ptr as int + length * size_of::<u8>() <= usize::MAX + 1);
        let tracked mut points_to_map = Map::<nat, vstd::raw_ptr::PointsTo<u8>>::tracked_empty();

        for len in 0..length
            invariant
                len <= length,
                buffer_ptr as int + length * size_of::<u8>() <= usize::MAX + 1,
                buffer_perm.is_range(buffer_ptr as int + len * size_of::<u8>() as int, length * size_of::<u8>() - len),
                forall |i: nat|
                    i >= buffer_ptr as nat && i < buffer_ptr as nat + len * size_of::<u8>() as nat
                        ==> points_to_map.contains_key(i),
                forall |i: nat|
                    i >= buffer_ptr as nat && i < buffer_ptr as nat + len * size_of::<u8>() as nat
                        ==> (points_to_map.index(i as nat).ptr() as nat == i as nat
                            && points_to_map.index(i as nat).ptr()@.provenance == buffer_perm.provenance()),
                buffer_ptr@.provenance == buffer_perm.provenance(),
            decreases
                length - len,
        {
            proof {
                let ghost range_start_addr = buffer_ptr as int + len * size_of::<u8>() as int;
                let ghost range_end_addr = range_start_addr + 1 * size_of::<u8>();
                
                let tracked (top, rest) = buffer_perm.split(crate::set_lib::set_int_range(range_start_addr, range_end_addr as int));
                assert(top.is_range(range_start_addr as usize as int, size_of::<u8>() as int));

                let tracked top_pointsto = top.into_typed::<u8>(range_start_addr as usize);
                buffer_perm = rest;
                points_to_map.tracked_insert(range_start_addr as nat, top_pointsto);
                assert(points_to_map.contains_key(range_start_addr as nat));
                assert(points_to_map.index(range_start_addr as nat).ptr() as nat == range_start_addr as nat);
                assert(top_pointsto.ptr()@.provenance == top.provenance());
                assert(top.provenance() == buffer_perm.provenance());
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
            Tracked(producer_token),
            Tracked(consumer_token),
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
        (Self {
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
        }, Tracked(producer_token), Tracked(consumer_token))
    }

    fn try_split(self, producer_token: Tracked<VBQueue::producer>, consumer_token: Tracked<VBQueue::consumer>) -> (res: Result<(Producer, Consumer),  &'static str>)
        requires
            self.wf(),
            producer_token@.instance_id() == self.instance@.id(),
            producer_token@.value() is Idle,
        ensures
            self.wf(),
            match res {
                Ok((prod, cons)) => prod.wf(), //&& cons.vbq.wf(),
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
                producer: producer_token,
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
            old(self).wf(),
            old(self).producer@.value() is Idle,
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
            ghost write_token => {
                let _ = self.vbq.instance.borrow().grant_fill_write(&write_token, self.producer.borrow_mut());
            }
        );

        let read = atomic_with_ghost!(&self.vbq.read => load();
            ghost read_token => {
                let _ = self.vbq.instance.borrow().grant_fill_read(&read_token, self.producer.borrow_mut());
            }
        );
        let max = self.vbq.length as u64;
        let already_inverted = write < read;
        assume(write + sz < u64::MAX);  // FIXME!

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

        
        proof {
            assume(start + sz < u64::MAX); // FIXME!
            assume(start + sz <= self.vbq.instance@.length());  // FIXME!
        }
        // Safe write, only viewed by this task

        atomic_with_ghost!(&self.vbq.reserve => store(start + sz as u64);
            ghost reserve_token => {
                let _ = self.vbq.instance.borrow().do_reserve(start as nat, sz as nat, &mut reserve_token, self.producer.borrow_mut());
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
    let (vbuf, Tracked(producer_token), Tracked(consumer_token)) = VBBuffer::new(6);
    let (mut prod, mut cons) = match vbuf.try_split(Tracked(producer_token), Tracked(consumer_token)) {
        Ok((prod, cons)) => (prod, cons),
        Err(_) => {
            return;
        }
    };

    // Request space for one byte
    let mut wgr = prod.grant_exact(1);
    
}

}