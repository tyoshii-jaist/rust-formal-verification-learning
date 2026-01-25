use state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
use vstd::invariant::*;
use vstd::raw_ptr::*;
use vstd::{prelude::*, *};
//use vstd::layout::*;
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
        do_split(to: nat) {
            require(pre.split == 0);
            require(to > 0 && to < pre.length);

            update split = to;
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, length: nat, base_addr: nat, provenance: raw_ptr::Provenance, buffer_perm: raw_ptr::PointsToRaw, buffer_dealloc: raw_ptr::Dealloc) { }

    #[inductive(do_split)]
    fn do_split_inductive(pre: Self, post: Self, to: nat) {
    }
});

pub tracked struct GhostStuff {
    pub tracked buffer_perm_token: PointsToRawExample::buffer_perm,
}

struct_with_invariants!{
    pub struct ExBuffer {
        length: usize,
        buffer_ptr: *mut u8,
        split: AtomicUsize<_, PointsToRawExample::split, _>,

        inv: Tracked< Shared<AtomicInvariant<_, GhostStuff, _>> >,

        instance: Tracked<PointsToRawExample::Instance>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            &&& self.instance@.length() == self.length
            &&& self.instance@.length() <= usize::MAX
        }

        invariant on split with (instance) is (v: usize, g: PointsToRawExample::split) {
            &&& g.instance_id() === instance@.id()
            &&& g.value() == v as int
        }

        invariant on inv with (instance)
            specifically (self.inv@@)
            is (v: GhostStuff)
        {
            &&& v.buffer_perm_token.instance_id() === instance@.id()
        }
    }
}

fn main() {
    let length = 10;

    let (buffer_ptr, Tracked(buffer_perm), Tracked(buffer_dealloc)) = allocate(length, 1);
    let tracked (
        Tracked(instance),
        Tracked(reserve_token),
        Tracked(grant_state_token),
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
}
}