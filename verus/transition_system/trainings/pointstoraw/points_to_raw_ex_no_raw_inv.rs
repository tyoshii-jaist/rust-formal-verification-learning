use state_machines_macros::tokenized_state_machine;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::raw_ptr::*;
use vstd::{prelude::*, *};
use vstd::layout::*;
use vstd::shared::*;
use vstd::tokens::UniqueValueToken;
use vstd::set_lib::*;

verus! {
pub struct ProducerState {
    pub divide: nat
}

impl ProducerState {
    pub open spec fn is_idle(&self) -> bool {
        self.divide == 0
    }
}

pub struct ConsumerState {
    pub divide: nat
}

impl ConsumerState {
    pub open spec fn is_idle(&self) -> bool {
        self.divide == 0
    }
}

pub struct GrantState {
    pub prod_start: int,
    pub prod_end: int,
    pub cons_start: int,
    pub cons_end: int,
}

tokenized_state_machine!(DividePermExample {
    fields {
        #[sharding(constant)]
        pub length: nat,

        #[sharding(variable)]
        pub divide: nat,

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
    pub fn valid_divide(&self) -> bool {
        0 <= self.divide && self.divide < self.length
    }

    #[invariant]
    pub fn valid_divide_with_grant_state(&self) -> bool {
        self.producer.divide == self.divide == self.grant_state.prod_end == self.grant_state.cons_start
    }

    #[invariant]
    pub fn valid_producer_start(&self) -> bool {
        self.grant_state.prod_start == 0
    }

    #[invariant]
    pub fn valid_consumer_end(&self) -> bool {
        ||| self.divide == 0 && self.grant_state.cons_end == 0
        ||| self.divide > 0 && self.grant_state.cons_end == self.length
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
            init divide = 0;

            init base_addr = base_addr;
            init provenance = provenance;
            init buffer_dealloc = Some(buffer_dealloc);
            init producer = ProducerState {
                divide: 0,
            };

            init consumer = ConsumerState {
                divide: 0,
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
        do_divide(at: nat) {
            require(at > 0 && at < pre.length);

            update divide = at;

            update producer = ProducerState {
                divide: at,
            };

            update grant_state = GrantState {
                prod_start: 0,
                prod_end: at as int,
                cons_start: at as int,
                cons_end: pre.length as int,
            };
        }
    }

    transition!{
        check_divide() {
            require(pre.producer.divide == 0);
            assert(pre.grant_state.prod_start == 0);
            assert(pre.grant_state.prod_end == pre.producer.divide);
            assert(pre.grant_state.cons_start == pre.producer.divide);
            assert(pre.grant_state.cons_end == 0);
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, length: nat, base_addr: nat, provenance: raw_ptr::Provenance, buffer_dealloc: raw_ptr::Dealloc) { }

    #[inductive(do_divide)]
    fn do_divide_inductive(pre: Self, post: Self, at: nat) {}

    #[inductive(check_divide)]
    fn check_divide_inductive(pre: Self, post: Self) {}
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
    pub open spec fn wf(self, inst: DividePermExample::Instance, cell: PAtomicUsize) -> bool {
        &&& self.perm@.patomic == cell.id()
        &&& self.token.instance_id() == inst.id()
        &&& self.perm@.value as nat == self.token.value()
    }
}

pub tracked struct GhostBufferPermission
{
    pub tracked pool: PointsToRaw,
    pub tracked token: DividePermExample::grant_state,
}

impl GhostBufferPermission
{
    pub open spec fn wf(self, inst: DividePermExample::Instance) -> bool {
        let ps = self.token.value().prod_start;
        let pe = self.token.value().prod_end;
        let cs = self.token.value().cons_start;
        let ce = self.token.value().cons_end;

        let whole_set = set_int_range(inst.base_addr() as int, inst.base_addr() as int + inst.length() as int);
        let prod_set = set_int_range(ps + inst.base_addr() as int, pe + inst.base_addr() as int);
        let cons_set = set_int_range(cs + inst.base_addr() as int, ce + inst.base_addr() as int);

        {
            &&& self.token.instance_id() == inst.id()
            &&& prod_set.disjoint(cons_set)
            &&& self.pool.dom()
              =~= Set::new(|i: int| whole_set.contains(i)
                                   && !prod_set.contains(i)
                                   && !cons_set.contains(i))
        }
    }
}

pub struct ExBuffer {
    inner: ExBufferInner,

    prod_token: Tracked<Option<DividePermExample::producer>>,
    cons_token: Tracked<Option<DividePermExample::consumer>>,
}

impl ExBuffer {
    pub closed spec fn wf(self) -> bool {
        self.inner.wf()
    }
}

struct_with_invariants!{
    pub struct ExBufferInner {
        length: usize,
        buffer_ptr: *mut u8,
        divide: PAtomicUsize,

        divide_inv: Tracked< Shared<AtomicInvariant<_, GhostStuff<DividePermExample::divide>, _>> >,
        buf_perm_inv: Tracked< Shared<AtomicInvariant<_, GhostBufferPermission, _>> >,

        instance: Tracked<DividePermExample::Instance>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            &&& self.instance@.length() == self.length
            &&& self.instance@.length() <= usize::MAX
            &&& self.divide_inv@@.namespace() != self.buf_perm_inv@@.namespace()
            &&& self.instance@.base_addr() == self.buffer_ptr as nat 
        }

        invariant on buf_perm_inv with (instance)
            specifically (self.buf_perm_inv@@)
            is (v: GhostBufferPermission)
        {
            v.wf(instance@)
        }

        invariant on divide_inv with (instance, divide)
            specifically (self.divide_inv@@)
            is (v: GhostStuff<DividePermExample::divide>)
        {
            v.wf(instance@, divide)
        }
    }
}

impl ExBuffer {
    pub closed spec fn is_splittable(&self) -> bool {
        &&& self.prod_token@ is Some
        &&& self.prod_token@->0.instance_id() == self.inner.instance@.id()
        &&& self.prod_token@->0.value().is_idle()
        &&& self.cons_token@ is Some
        &&& self.cons_token@->0.instance_id() == self.inner.instance@.id()
        &&& self.cons_token@->0.value().is_idle()
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
            r.prod_token@ is Some,
            r.inner.instance@.id() == r.prod_token@->0.instance_id(),
            r.cons_token@ is Some,
            r.inner.instance@.id() == r.cons_token@->0.instance_id(),
    {
        let (buffer_ptr, Tracked(points_to_raw), Tracked(buffer_dealloc)) = allocate(length, 1);
        let tracked (
            Tracked(instance),
            Tracked(divide_token),
            Tracked(producer_token),
            Tracked(consumer_token),
            Tracked(grant_state_token),
        ) = DividePermExample::Instance::initialize(
            length as nat,
            buffer_ptr as nat,
            buffer_ptr@.provenance,
            buffer_dealloc,
            Some(buffer_dealloc),
        );

        let tracked_inst: Tracked<DividePermExample::Instance> = Tracked(instance.clone());
        proof {
            assert(points_to_raw.is_range(buffer_ptr as int, length as int));
            assert(points_to_raw.dom() =~= Set::new(|i: int| buffer_ptr as int <= i && i < buffer_ptr as int + length as int));
        }
        let tr_inst = Tracked(instance);
        let tracked ghost_buffer_perm = GhostBufferPermission {
            pool: points_to_raw,
            token: grant_state_token,
        };
        let tracked buf_perm_inv = AtomicInvariant::new(tr_inst, ghost_buffer_perm, 0);
        let tracked buf_perm_inv = Shared::new(buf_perm_inv); // Shared は Ghost object を中に入れて、duplicate して &T を取り出すことができる。

        let (divide, Tracked(divide_perm)) = PAtomicUsize::new(0);
        let tracked gss = GhostStuff { perm: divide_perm, token: divide_token };
        let tracked divide_inv = AtomicInvariant::new((tr_inst, divide), gss, 1);
        let tracked divide_inv = Shared::new(divide_inv);

        // Initialize the queue
        Self {
            inner: ExBufferInner {
                length,
                buffer_ptr,
                divide,
                buf_perm_inv: Tracked(buf_perm_inv),
                divide_inv: Tracked(divide_inv),
                instance: tr_inst,
            },
            prod_token: Tracked(Some(producer_token)),
            cons_token: Tracked(Some(consumer_token)),
        }
    }

    fn try_split(self) -> (res: (Producer, Consumer))
        requires
            self.wf(),
            self.is_splittable(),
        ensures
            res.0.is_idle(),
            res.1.is_idle(),
    {
        let tracked prod_token = self.prod_token.borrow_mut().tracked_take();
        let tracked cons_token = self.cons_token.borrow_mut().tracked_take();

        (
            Producer {
                exb_inner: ExBufferInner {
                    length: self.inner.length,
                    buffer_ptr: self.inner.buffer_ptr,
                    divide: self.inner.divide,
                    buf_perm_inv: Tracked(self.inner.buf_perm_inv.borrow().clone()),
                    divide_inv: Tracked(self.inner.divide_inv.borrow().clone()),
                    instance: Tracked(self.inner.instance.borrow().clone()),
                },
                prod_token: Tracked(Some(prod_token)),
            },
            Consumer {
                exb_inner: ExBufferInner {
                    length: self.inner.length,
                    buffer_ptr: self.inner.buffer_ptr,
                    divide: self.inner.divide,
                    buf_perm_inv: Tracked(self.inner.buf_perm_inv.borrow().clone()),
                    divide_inv: Tracked(self.inner.divide_inv.borrow().clone()),
                    instance: Tracked(self.inner.instance.borrow().clone()),
                },
                cons_token: Tracked(Some(cons_token)),
            }
        )
    }
}

impl Producer {
    fn divide(self, at: usize)
        requires
            self.exb_inner.instance@.id() == self.prod_token@->0.instance_id(),
            self.prod_token@ is Some,
            self.prod_token@->0.value().is_idle(),
            0 < at && at < self.exb_inner.instance@.length(),
    {
        let mut slf = self;
        let tracked mut prod_points_to_raw: Option<PointsToRaw> = None;
        let tracked mut prod_token = slf.prod_token.borrow_mut().tracked_take();

        open_atomic_invariant!(slf.exb_inner.buf_perm_inv.borrow().borrow() => bp => {
            let tracked GhostBufferPermission {
                pool: mut current_pool,
                token: mut grant_state_token,
            } = bp;

            proof {
                slf.exb_inner.instance.borrow().check_divide(&mut prod_token, &mut grant_state_token);

                assert(grant_state_token.value().prod_start == 0);
                assert(grant_state_token.value().prod_end == 0);
                assert(grant_state_token.value().cons_start == 0);
                assert(grant_state_token.value().cons_end == 0);
            }

            open_atomic_invariant!(slf.exb_inner.divide_inv.borrow().borrow() => s => {
                let tracked GhostStuff { perm: mut divide_perm, token: mut divide_token } = s;

                slf.exb_inner.divide.store(Tracked(&mut divide_perm), at);
                let tracked ret = slf.exb_inner.instance.borrow().do_divide(at as nat, &mut divide_token, &mut prod_token, &mut grant_state_token);
                assert(divide_token.value() == at);
                assert(grant_state_token.value().prod_start == 0);
                assert(grant_state_token.value().prod_end == at as int);
                assert(grant_state_token.value().cons_start == at as int);
                assert(grant_state_token.value().cons_end == slf.exb_inner.instance@.length());

                proof { s = GhostStuff { perm: divide_perm, token: divide_token }; }
            });

            let tracked (points_to_raw_prod, mut pool_rest) = current_pool.split(set_int_range(
                slf.exb_inner.buffer_ptr as int + grant_state_token.value().prod_start,
                slf.exb_inner.buffer_ptr as int + grant_state_token.value().prod_end));

            let tracked (_points_to_raw_cons, pool_rest) = pool_rest.split(set_int_range(
                slf.exb_inner.buffer_ptr as int + grant_state_token.value().cons_start,
                slf.exb_inner.buffer_ptr as int + grant_state_token.value().cons_end));

            proof { bp = GhostBufferPermission { pool: pool_rest, token: grant_state_token}; }
        });

        slf.prod_token = Tracked(Some(prod_token));
    }
}

pub struct Producer {
    exb_inner: ExBufferInner,
    prod_token: Tracked<Option<DividePermExample::producer>>,
}

impl Producer {
    pub closed spec fn is_idle(&self) -> bool {
        &&& self.prod_token@ is Some
        &&& self.prod_token@->0.instance_id() == self.exb_inner.instance@.id()
        &&& self.prod_token@->0.value().is_idle()
    }
}

pub struct Consumer {
    exb_inner: ExBufferInner,
    cons_token: Tracked<Option<DividePermExample::consumer>>,
}

impl Consumer {
    pub closed spec fn is_idle(&self) -> bool {
        &&& self.cons_token@ is Some
        &&& self.cons_token@->0.instance_id() == self.exb_inner.instance@.id()
        &&& self.cons_token@->0.value().is_idle()
    }
}


fn main() {
    let ex_buffer = ExBuffer::new(10);
}
}