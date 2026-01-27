use state_machines_macros::tokenized_state_machine;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::raw_ptr::*;
use vstd::{prelude::*, *};
use vstd::layout::*;
use vstd::shared::*;

verus! {
pub struct ProducerState {
    pub split: nat,
    pub grant: Option<raw_ptr::PointsToRaw>,
}

pub struct ConsumerState {
    pub split: nat,
    pub grant: Option<raw_ptr::PointsToRaw>,
}

tokenized_state_machine!(PointsToRawExample {
    fields {
        #[sharding(constant)]
        pub length: nat,

        #[sharding(variable)]
        pub split: nat,

        #[sharding(constant)]
        pub base_addr: nat,

        #[sharding(constant)]
        pub provenance: raw_ptr::Provenance,

        #[sharding(storage_option)]
        pub buffer_dealloc: Option<raw_ptr::Dealloc>,

        #[sharding(variable)]
        pub buffer_perm: raw_ptr::PointsToRaw,

        #[sharding(variable)]
        pub producer: ProducerState,

        #[sharding(variable)]
        pub consumer: ConsumerState,
    }

    #[invariant]
    pub fn valid_split(&self) -> bool {
        0 <= self.split && self.split < self.length
    }

    init! {
        initialize(
            length: nat,
            base_addr: nat,
            provenance: raw_ptr::Provenance,
            buffer_perm: raw_ptr::PointsToRaw,
            buffer_dealloc: raw_ptr::Dealloc,
        )
        {
            require(
                {
                    &&& length > 0 // TODO: 元の BBQueue はこの制約は持っていない
                    &&& buffer_perm.is_range(base_addr as int, length as int)
                }
            );

            init length = length;
            init split = 0;

            init base_addr = base_addr;
            init provenance = provenance;
            init buffer_perm = buffer_perm;
            init buffer_dealloc = Some(buffer_dealloc);
            init producer = ProducerState {
                split: 0,
                grant: None,
            };

            init consumer = ConsumerState {
                split: 0,
                grant: None,
            };
        }
    }

    transition!{
        do_split(at: nat) {
            require(at > 0 && at < pre.length);

            update split = at;
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, length: nat, base_addr: nat, provenance: raw_ptr::Provenance, buffer_perm: raw_ptr::PointsToRaw, buffer_dealloc: raw_ptr::Dealloc) { }

    #[inductive(do_split)]
    fn do_split_inductive(pre: Self, post: Self, at: nat) {
    }
});


pub tracked struct GhostSplitStuff {
    pub tracked perm: PermissionUsize,
    pub tracked token: PointsToRawExample::split,
}

impl GhostSplitStuff {
    pub open spec fn wf(self, inst: PointsToRawExample::Instance, cell: PAtomicUsize) -> bool {
        &&& self.perm@.patomic == cell.id()
        &&& self.token.instance_id() == inst.id()
        &&& self.perm@.value as nat == self.token.value()
    }
}

struct_with_invariants!{
    pub struct ExBuffer {
        length: usize,
        buffer_ptr: *mut u8,
        split: PAtomicUsize,

        buffer_perm_inv: Tracked< Shared<AtomicInvariant<_, PointsToRawExample::buffer_perm, _>> >,
        split_inv: Tracked< Shared<AtomicInvariant<_, GhostSplitStuff, _>> >,

        instance: Tracked<PointsToRawExample::Instance>,
        producer: Tracked<Option<PointsToRawExample::producer>>,
        consumer: Tracked<Option<PointsToRawExample::consumer>>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            &&& self.instance@.length() == self.length
            &&& self.instance@.length() <= usize::MAX
            &&& self.split_inv@@.namespace() != self.buffer_perm_inv@@.namespace()
        }

        invariant on buffer_perm_inv with (instance)
            specifically (self.buffer_perm_inv@@)
            is (v: PointsToRawExample::buffer_perm)
        {
            &&& v.instance_id() === instance@.id()
        }

        invariant on split_inv with (instance, split)
            specifically (self.split_inv@@)
            is (v: GhostSplitStuff)
        {
            v.wf(instance@, split)
        }
    }
}

impl ExBuffer
{
    fn new(length: usize) -> (r: Self)
        requires
            valid_layout(length, 1),
            length > 0,
        ensures
            r.wf(),
    {
        let (buffer_ptr, Tracked(buffer_perm), Tracked(buffer_dealloc)) = allocate(length, 1);
        let tracked (
            Tracked(instance),
            Tracked(split_token),
            Tracked(buffer_perm_token),
            Tracked(producer_token),
            Tracked(consumer_token),
        ) = PointsToRawExample::Instance::initialize(
            length as nat,
            buffer_ptr as nat,
            buffer_ptr@.provenance,
            buffer_perm,
            buffer_dealloc,
            Some(buffer_dealloc),
        );

        let tracked_inst: Tracked<PointsToRawExample::Instance> = Tracked(instance.clone());

        let tr_inst = Tracked(instance);
        let tracked buffer_perm_inv = AtomicInvariant::new(tr_inst, buffer_perm_token, 0);
        let tracked buffer_perm_inv = Shared::new(buffer_perm_inv); // Shared は Ghost object を中に入れて、duplicate して &T を取り出すことができる。

        let (split, Tracked(split_perm)) = PAtomicUsize::new(0);
        let tracked gss = GhostSplitStuff { perm: split_perm, token: split_token };
        let tracked split_inv = AtomicInvariant::new((tr_inst, split), gss, 1);
        let tracked split_inv = Shared::new(split_inv);

        // Initialize the queue
        Self {
            length,
            buffer_ptr,
            split,
            buffer_perm_inv: Tracked(buffer_perm_inv),
            split_inv: Tracked(split_inv),
            instance: tr_inst,
            producer: Tracked(Some(producer_token)),
            consumer: Tracked(Some(consumer_token)),
        }
    }

    fn split(&self, at: usize)
        requires
            self.wf(),
            0 < at && at < self.length,
    {
        open_atomic_invariant!(self.buffer_perm_inv.borrow().borrow() => bp => {
            let tracked mut buffer_perm_token = bp;
            open_atomic_invariant!(self.split_inv.borrow().borrow() => s => {
                let tracked GhostSplitStuff { perm: mut split_perm, token: mut split_token } = s;

                self.split.store(Tracked(&mut split_perm), at);
                let tracked ret = self.instance.borrow().do_split(at as nat, &mut split_token);
                assert(split_token.value() == at);
                proof { s = GhostSplitStuff { perm: split_perm, token: split_token }; }
            });

            proof { bp = buffer_perm_token; }
        });

    }
}

fn main() {
    let ex_buffer = ExBuffer::new(10);
}
}