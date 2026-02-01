use state_machines_macros::tokenized_state_machine;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::raw_ptr::*;
use vstd::{prelude::*, *};
use vstd::layout::*;
use vstd::shared::*;
use vstd::tokens::UniqueValueToken;

verus! {
pub struct ProducerState {
    pub split: nat,
    pub grant: Option<raw_ptr::PointsToRaw>,
}

pub struct ConsumerState {
    pub split: nat,
    pub grant: Option<raw_ptr::PointsToRaw>,
}

pub struct GrantState {
    pub prod_start: int,
    pub prod_end: int,
    pub cons_start: int,
    pub cons_end: int,
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
        pub producer: ProducerState,

        #[sharding(variable)]
        pub consumer: ConsumerState,

        #[sharding(variable)]
        pub grant_state: GrantState,
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
            buffer_dealloc: raw_ptr::Dealloc,
        )
        {
            require(
                {
                    &&& length > 0
                }
            );

            init length = length;
            init split = 0;

            init base_addr = base_addr;
            init provenance = provenance;
            init buffer_dealloc = Some(buffer_dealloc);
            init producer = ProducerState {
                split: 0,
                grant: None,
            };

            init consumer = ConsumerState {
                split: 0,
                grant: None,
            };

            init grant_state = GrantState {
                prod_start: 0,
                prod_end: 0,
                cons_start: 0,
                cons_end: 0,
            };
        }
    }

    transition!{
        do_split(at: nat) {
            require(at > 0 && at < pre.length);

            update split = at;

            update grant_state = GrantState {
                prod_start: 0,
                prod_end: at as int,
                cons_start: at as int,
                cons_end: pre.length as int,
            };
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, length: nat, base_addr: nat, provenance: raw_ptr::Provenance, buffer_dealloc: raw_ptr::Dealloc) { }

    #[inductive(do_split)]
    fn do_split_inductive(pre: Self, post: Self, at: nat) {}
});

pub tracked struct GhostStuff<Tok>
where
    Tok: UniqueValueToken<nat>,
{
    pub tracked perm: PermissionUsize,
    pub tracked token: Tok,
}

impl<Tok> GhostStuff<Tok>
where
    Tok: UniqueValueToken<nat>,
{
    pub open spec fn wf(self, inst: PointsToRawExample::Instance, cell: PAtomicUsize) -> bool {
        &&& self.perm@.patomic == cell.id()
        &&& self.token.instance_id() == inst.id()
        &&& self.perm@.value as nat == self.token.value()
    }
}

pub tracked struct BufferPermission {
    pub tracked pool: PointsToRaw,
    pub tracked prod: PointsToRaw,
    pub tracked cons: PointsToRaw,
}

pub tracked struct GhostBufferPermission
{
    pub tracked token: PointsToRawExample::grant_state,
}

impl GhostBufferPermission
{
    pub open spec fn wf(self, inst: PointsToRawExample::Instance, buf_perm: BufferPermission) -> bool {
        let ps = self.token.value().prod_start;
        let pe = self.token.value().prod_end;
        let cs = self.token.value().cons_start;
        let ce = self.token.value().cons_end;
        {
            &&& self.token.instance_id() == inst.id()
            &&& buf_perm.prod.is_range(ps, pe - ps)
            &&& buf_perm.cons.is_range(cs, ce - cs)
        }
    }
}

struct_with_invariants!{
    pub struct ExBuffer {
        length: usize,
        buffer_ptr: *mut u8,
        split: PAtomicUsize,

        buf_perm_inv: Tracked< Shared<AtomicInvariant<_, GhostBufferPermission, _>> >,
        split_inv: Tracked< Shared<AtomicInvariant<_, GhostStuff<PointsToRawExample::split>, _>> >,

        instance: Tracked<PointsToRawExample::Instance>,
        buf_perm: Tracked<BufferPermission>,
        producer: Tracked<Option<PointsToRawExample::producer>>,
        consumer: Tracked<Option<PointsToRawExample::consumer>>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            &&& self.instance@.length() == self.length
            &&& self.instance@.length() <= usize::MAX
            &&& self.split_inv@@.namespace() != self.buf_perm_inv@@.namespace()
        }

        invariant on buf_perm_inv with (instance, buf_perm)
            specifically (self.buf_perm_inv@@)
            is (v: GhostBufferPermission)
        {
            v.wf(instance@, buf_perm@)
        }

        invariant on split_inv with (instance, split)
            specifically (self.split_inv@@)
            is (v: GhostStuff<PointsToRawExample::split>)
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
            r.producer@ is Some,
            r.producer@->Some_0.value().grant is None,
            r.consumer@ is Some,
            r.consumer@->Some_0.value().grant is None,
    {
        let (buffer_ptr, Tracked(points_to_raw), Tracked(buffer_dealloc)) = allocate(length, 1);
        let tracked (
            Tracked(instance),
            Tracked(split_token),
            Tracked(producer_token),
            Tracked(consumer_token),
            Tracked(grant_state_token),
        ) = PointsToRawExample::Instance::initialize(
            length as nat,
            buffer_ptr as nat,
            buffer_ptr@.provenance,
            buffer_dealloc,
            Some(buffer_dealloc),
        );

        let tracked_inst: Tracked<PointsToRawExample::Instance> = Tracked(instance.clone());

        let tr_inst = Tracked(instance);
        let tracked buf_perm = BufferPermission {
            pool: points_to_raw,
            prod: PointsToRaw::empty(buffer_ptr@.provenance),
            cons: PointsToRaw::empty(buffer_ptr@.provenance),
        };
        let buf_perm = Tracked(buf_perm);
        let tracked ghost_buffer_perm = GhostBufferPermission {
            token: grant_state_token,
        };
        let tracked buf_perm_inv = AtomicInvariant::new((tr_inst, buf_perm), ghost_buffer_perm, 0);
        let tracked buf_perm_inv = Shared::new(buf_perm_inv); // Shared は Ghost object を中に入れて、duplicate して &T を取り出すことができる。

        let (split, Tracked(split_perm)) = PAtomicUsize::new(0);
        let tracked gss = GhostStuff { perm: split_perm, token: split_token };
        let tracked split_inv = AtomicInvariant::new((tr_inst, split), gss, 1);
        let tracked split_inv = Shared::new(split_inv);

        // Initialize the queue
        Self {
            length,
            buffer_ptr,
            split,
            buf_perm_inv: Tracked(buf_perm_inv),
            split_inv: Tracked(split_inv),
            instance: tr_inst,
            buf_perm,
            producer: Tracked(Some(producer_token)),
            consumer: Tracked(Some(consumer_token)),
        }
    }

    fn split(&self, at: usize)
        requires
            self.wf(),
            0 < at && at < self.length,
    {
        open_atomic_invariant!(self.buf_perm_inv.borrow().borrow() => bp => {
            let tracked GhostBufferPermission {
                token: mut grant_state_token,
            } = bp;
            open_atomic_invariant!(self.split_inv.borrow().borrow() => s => {
                let tracked GhostStuff { perm: mut split_perm, token: mut split_token } = s;

                self.split.store(Tracked(&mut split_perm), at);
                let tracked ret = self.instance.borrow().do_split(at as nat, &mut split_token, &mut grant_state_token);
                assert(split_token.value() == at);
                proof { s = GhostStuff { perm: split_perm, token: split_token }; }
            });

            proof { bp = GhostBufferPermission { token: grant_state_token}; }
        });

    }
}

fn main() {
    let ex_buffer = ExBuffer::new(10);
}
}