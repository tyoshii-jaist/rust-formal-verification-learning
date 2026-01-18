use state_machines_macros::tokenized_state_machine;
//use vstd::atomic_ghost::*;
use vstd::invariant::*;
use vstd::raw_ptr::*;
use vstd::{prelude::*, *};
//use vstd::layout::*;
use vstd::shared::*;

verus! {
pub struct Grant {
    base_addr: nat,
    length: nat,
    buffer_perm: raw_ptr::PointsToRaw,
}

tokenized_state_machine!{PointsToRawExample {
    fields {
        #[sharding(constant)]
        pub length: nat,

        #[sharding(variable)]
        pub reserve: nat,

        #[sharding(constant)]
        pub base_addr: nat,

        #[sharding(constant)]
        pub provenance: raw_ptr::Provenance,

        #[sharding(storage_option)]
        pub buffer_dealloc: Option<raw_ptr::Dealloc>,

        #[sharding(variable)]
        pub buffer_perm: raw_ptr::PointsToRaw,

        #[sharding(variable)]
        pub producer_grant: Option<Grant>,
    }

    #[invariant]
    pub fn valid_reserve(&self) -> bool {
        self.reserve >= 0 && self.reserve < self.length
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
            init reserve = 0;
            init producer_grant = None;

            init base_addr = base_addr;
            init provenance = provenance;
            init buffer_perm = buffer_perm;
            init buffer_dealloc = Some(buffer_dealloc);
        }
    }

    transition!{
        do_reserve(to: nat) {
            require(pre.reserve == 0);
            require(to > 0 && to < pre.length);

            update reserve = to;
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, length: nat, base_addr: nat, provenance: raw_ptr::Provenance, buffer_perm: raw_ptr::PointsToRaw, buffer_dealloc: raw_ptr::Dealloc) { }

    #[inductive(do_reserve)]
    fn do_reserve_inductive(pre: Self, post: Self, to: nat) {
    }
}}

pub tracked struct GhostStuff {
    pub tracked buffer_perm_token: PointsToRawExample::buffer_perm,
}

impl GhostStuff {
    pub open spec fn wf(self, inst: PointsToRawExample::Instance) -> bool {
        &&& self.buffer_perm_token.instance_id() == inst.id()
    }
}

struct_with_invariants!{
    pub struct ExBuffer {
        length: usize,
        buffer_ptr: *mut u8,

        instance: Tracked<PointsToRawExample::Instance>,
        inv: Tracked< Shared<AtomicInvariant<_, GhostStuff, _>> >,
        producer_grant: Tracked<Option<PointsToRawExample::producer_grant>>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            &&& self.instance@.length() == self.length
            &&& self.instance@.length() <= usize::MAX
            &&& match self.producer_grant@ {
                    Some(prod) => prod.instance_id() == self.instance@.id(),
                    None => true,
                }
        }

        invariant on inv with (instance)
            specifically (self.inv@@)
            is (v: GhostStuff)
        {
            v.wf(instance@)
        }
    }
}

fn main() {
    let length = 10;

    let (buffer_ptr, Tracked(buffer_perm), Tracked(buffer_dealloc)) = allocate(length, 1);
    let tracked (
        Tracked(instance),
        Tracked(reserve_token),
        Tracked(producer_grant_token),
        Tracked(buffer_perm_token),
    ) = PointsToRawExample::Instance::initialize(
        length as nat,
        buffer_ptr as nat,
        buffer_ptr@.provenance,
        buffer_perm,
        buffer_dealloc,
        Some(buffer_dealloc),
    );

    assume(align_of::<[u8; 10]>() as int == 0);

    let tracked pt = buffer_perm.into_typed::<[u8; 10]>(0);
}
}