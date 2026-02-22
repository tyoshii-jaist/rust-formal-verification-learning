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
global layout u8 is size == 1, align == 1;


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

impl GrantState {
    pub open spec fn is_idle(&self) -> bool {
        self.prod_start == self.prod_end == self.cons_start == self.cons_end == 0
    }
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
    pub open spec fn wf(self, inst: DividePermExample::Instance, cell: &PAtomicUsize) -> bool {
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
    buffer_ptr: *mut u8,
    divide: PAtomicUsize,

    divide_gs: Tracked<Option<GhostStuff<DividePermExample::divide>>>,
    buf_points_to_raw: Tracked<Option<PointsToRaw>>,
    grant_state_token: Tracked<Option<DividePermExample::grant_state>>,
    prod_token: Tracked<Option<DividePermExample::producer>>,
    cons_token: Tracked<Option<DividePermExample::consumer>>,
    instance: Tracked<DividePermExample::Instance>,
}

struct_with_invariants!{
    pub struct ExBufferShared<'a> {
        divide: &'a PAtomicUsize,
        divide_inv: Tracked< Shared<AtomicInvariant<_, GhostStuff<DividePermExample::divide>, _>> >,
        buf_perm_inv: Tracked< Shared<AtomicInvariant<_, GhostBufferPermission, _>> >,

        instance: Tracked<DividePermExample::Instance>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            &&& self.divide_inv@@.namespace() != self.buf_perm_inv@@.namespace()
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
    pub closed spec fn wf(self) -> bool {
        &&& self.instance@.length() <= usize::MAX
        &&& self.instance@.base_addr() == self.buffer_ptr as nat
        &&& self.buffer_ptr as int + self.instance@.length() <= usize::MAX + 1
    }

    pub closed spec fn is_splittable(&self) -> bool {
        &&& self.prod_token@ is Some
        &&& self.prod_token@->0.instance_id() == self.instance@.id()
        &&& self.prod_token@->0.value().is_idle()
        &&& self.cons_token@ is Some
        &&& self.cons_token@->0.instance_id() == self.instance@.id()
        &&& self.cons_token@->0.value().is_idle()
        &&& self.grant_state_token@ is Some
        &&& self.grant_state_token@->0.instance_id() == self.instance@.id()
        &&& self.grant_state_token@->0.value().is_idle()
        &&& self.buf_points_to_raw@ is Some
        &&& self.buf_points_to_raw@->0.is_range(self.buffer_ptr as int, self.instance@.length() as int)
        &&& self.buf_points_to_raw@->0.dom() =~= Set::new(|i: int| self.buffer_ptr as int <= i && i < self.buffer_ptr as int + self.instance@.length() as int)
        &&& self.divide_gs@ is Some
        &&& self.divide_gs@->0.wf(self.instance@, &self.divide)
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
            r.is_splittable(),
            r.instance@.length() == length,
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
        let (divide, Tracked(divide_perm)) = PAtomicUsize::new(0);
        let tracked divide_gs = GhostStuff { perm: divide_perm, token: divide_token };

        // Initialize the queue
        Self {
            buffer_ptr,
            divide,
            divide_gs: Tracked(Some(divide_gs)),
            buf_points_to_raw: Tracked(Some(points_to_raw)),
            grant_state_token: Tracked(Some(grant_state_token)),
            prod_token: Tracked(Some(producer_token)),
            cons_token: Tracked(Some(consumer_token)),
            instance: Tracked(instance),
        }
    }

    fn try_split<'a>(&'a mut self) -> (res: (Producer<'a>, Consumer<'a>))
        requires
            old(self).wf(),
            old(self).is_splittable(),
        ensures
            res.0.is_idle(),
            res.1.is_idle(),
            res.0.shared.instance@.length() == old(self).instance@.length(),
            res.1.shared.instance@.length() == old(self).instance@.length(),
    {
        let tracked prod_token = self.prod_token.borrow_mut().tracked_take();
        let tracked cons_token = self.cons_token.borrow_mut().tracked_take();
        let tracked grant_state_token = self.grant_state_token.borrow_mut().tracked_take();
        let tracked buf_points_to_raw = self.buf_points_to_raw.borrow_mut().tracked_take();
        let tracked divide_gs = self.divide_gs.borrow_mut().tracked_take();
        let Tracked(inst) = self.instance;

        let tracked ghost_buffer_perm = GhostBufferPermission {
            pool: buf_points_to_raw,
            token: grant_state_token,
        };
        let tracked buf_perm_inv = AtomicInvariant::new(self.instance, ghost_buffer_perm, 0);
        let tracked buf_perm_inv = Shared::new(buf_perm_inv); // Shared は Ghost object を中に入れて、duplicate して &T を取り出すことができる。

        let tracked divide_inv = AtomicInvariant::new((self.instance, &self.divide), divide_gs, 1);
        let tracked divide_inv = Shared::new(divide_inv);
        (
            Producer {
                buffer_ptr: self.buffer_ptr,
                shared: ExBufferShared {
                    divide: &self.divide,
                    buf_perm_inv: Tracked(buf_perm_inv.clone()),
                    divide_inv: Tracked(divide_inv.clone()),
                    instance: Tracked(self.instance.borrow().clone()),
                },
                prod_token: Tracked(Some(prod_token)),
            },
            Consumer {
                buffer_ptr: self.buffer_ptr,
                shared: ExBufferShared {
                    divide: &self.divide,
                    buf_perm_inv: Tracked(buf_perm_inv),
                    divide_inv: Tracked(divide_inv),
                    instance: Tracked(self.instance.borrow().clone()),
                },
                cons_token: Tracked(Some(cons_token)),
            }
        )
    }
}

impl<'a> Producer<'a> {
    fn divide(self, at: usize) -> (r: GrantP<'a>)
        requires
            self.is_idle(),
            0 < at && at < self.shared.instance@.length(),
        ensures
            r.prod_token@ is Some,
            r.prod_token@->0.instance_id() == self.shared.instance@.id(),
            r.prod_token@->0.value().divide == at,
            r.buffer_ptr == self.buffer_ptr,
            r.points_to_raw_token@ is Some,
            r.points_to_raw_token@->0.dom() =~= Set::new(|i: int|
                i >= r.buffer_ptr as int && i < r.buffer_ptr as int + r.prod_token@->0.value().divide as int),
            r.points_to_raw_token@->0.is_range(r.buffer_ptr as int, r.prod_token@->0.value().divide as int),
            0 < r.prod_token@->0.value().divide && r.prod_token@->0.value().divide < self.shared.instance@.length(),
    {
        let mut slf = self;
        let tracked mut prod_points_to_raw: Option<PointsToRaw> = None;
        let tracked mut prod_token = slf.prod_token.borrow_mut().tracked_take();

        open_atomic_invariant!(slf.shared.buf_perm_inv.borrow().borrow() => bp => {
            let tracked GhostBufferPermission {
                pool: mut current_pool,
                token: mut grant_state_token,
            } = bp;

            proof {
                slf.shared.instance.borrow().check_divide(&mut prod_token, &mut grant_state_token);

                assert(grant_state_token.value().prod_start == 0);
                assert(grant_state_token.value().prod_end == 0);
                assert(grant_state_token.value().cons_start == 0);
                assert(grant_state_token.value().cons_end == 0);
            }

            open_atomic_invariant!(slf.shared.divide_inv.borrow().borrow() => s => {
                let tracked GhostStuff { perm: mut divide_perm, token: mut divide_token } = s;

                slf.shared.divide.store(Tracked(&mut divide_perm), at);
                let tracked ret = slf.shared.instance.borrow().do_divide(at as nat, &mut divide_token, &mut prod_token, &mut grant_state_token);
                assert(divide_token.value() == at);
                assert(grant_state_token.value().prod_start == 0);
                assert(grant_state_token.value().prod_end == at as int);
                assert(grant_state_token.value().cons_start == at as int);
                assert(grant_state_token.value().cons_end == slf.shared.instance@.length());

                proof { s = GhostStuff { perm: divide_perm, token: divide_token }; }
            });

            let tracked (points_to_raw_prod, mut pool_rest) = current_pool.split(set_int_range(
                slf.buffer_ptr as int + grant_state_token.value().prod_start,
                slf.buffer_ptr as int + grant_state_token.value().prod_end));

            proof {
                prod_points_to_raw = Some(points_to_raw_prod);
            }

            let tracked (_points_to_raw_cons, pool_rest) = pool_rest.split(set_int_range(
                slf.buffer_ptr as int + grant_state_token.value().cons_start,
                slf.buffer_ptr as int + grant_state_token.value().cons_end));

            proof { bp = GhostBufferPermission { pool: pool_rest, token: grant_state_token}; }
        });

        let tracked prod_points_to_raw = match prod_points_to_raw {
            Some(token) => token,
            None => {
                assert(false);
                proof_from_false()
            }
        };

        GrantP {
            buffer_ptr: slf.buffer_ptr,
            shared: ExBufferShared {
                divide: slf.shared.divide,
                buf_perm_inv: Tracked(slf.shared.buf_perm_inv.borrow().clone()),
                divide_inv: Tracked(slf.shared.divide_inv.borrow().clone()),
                instance: Tracked(slf.shared.instance.borrow().clone()),
            },
            points_to_raw_token: Tracked(Some(prod_points_to_raw)),
            prod_token: Tracked(Some(prod_token)),
        }
    }
}

pub struct Producer<'a> {
    buffer_ptr: *mut u8,
    shared: ExBufferShared<'a>,
    prod_token: Tracked<Option<DividePermExample::producer>>,
}

impl<'a> Producer<'a> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.prod_token@ is Some
        &&& self.prod_token@->0.instance_id() == self.shared.instance@.id()
        &&& self.buffer_ptr as int == self.shared.instance@.base_addr()
        &&& self.buffer_ptr as int + self.shared.instance@.length() <= usize::MAX + 1
        &&& self.shared.wf()
    }
    pub closed spec fn is_idle(&self) -> bool {
        &&& self.prod_token@->0.value().is_idle()
        &&& self.wf()
    }
}

pub struct GrantP<'a> {
    buffer_ptr: *mut u8,
    points_to_raw_token: Tracked<Option<PointsToRaw>>,
    shared: ExBufferShared<'a>,
    prod_token: Tracked<Option<DividePermExample::producer>>,
}

pub struct Consumer<'a> {
    buffer_ptr: *mut u8,
    shared: ExBufferShared<'a>,
    cons_token: Tracked<Option<DividePermExample::consumer>>,
}

impl<'a> Consumer<'a> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.cons_token@ is Some
        &&& self.cons_token@->0.instance_id() == self.shared.instance@.id()
        &&& self.buffer_ptr as int == self.shared.instance@.base_addr()
        &&& self.shared.wf()
 
    }
    pub closed spec fn is_idle(&self) -> bool {
        &&& self.cons_token@->0.value().is_idle()
        &&& self.wf()
    }
}


fn main() {
    let size = 10;
    let mut ex_buffer = ExBuffer::new(size);
    let (prod, cons) = ex_buffer.try_split();

    let divide_at = 6;
    let mut grp = prod.divide(divide_at);

    let tracked mut points_to_raw = grp.points_to_raw_token.borrow_mut().tracked_take();
    assert(points_to_raw.is_range(grp.buffer_ptr as int, divide_at as int));

    //let tracked mut points_to_map = Map::<int, vstd::raw_ptr::PointsTo<u8>>::tracked_empty();
    for idx in 0..divide_at
        invariant
            idx <= divide_at,
            grp.buffer_ptr as int + divide_at <= usize::MAX + 1,
            points_to_raw.is_range(grp.buffer_ptr as int + idx as int, divide_at - idx),
            /*
            forall |i: int|
                i >= grp.buffer_ptr as int && i < grp.buffer_ptr as int + idx as int
                    <==> points_to_map.contains_key(i),
            forall |i: int|
                i >= grp.buffer_ptr as int && i < grp.buffer_ptr as int + idx as int
                    ==> points_to_map.index(i as int).ptr() as int == i as int,
            forall |i: int|
                i >= grp.buffer_ptr as int && i < grp.buffer_ptr as int + idx as int
                    ==> points_to_map.index(i as int).ptr()@.provenance == buffer_perm.provenance(), 
            grp.buffer_ptr @.provenance == buffer_perm.provenance(),
            */
        decreases
            divide_at - idx,
    {
        let range_base_addr = grp.buffer_ptr as usize + idx as usize;

        let tracked splitted = points_to_raw.split(set_int_range(range_base_addr as int, range_base_addr + 1 as int));
        let tracked top = splitted.0;
        let tracked rest = splitted.1;
        assert(top.is_range(range_base_addr as usize as int, 1));
    
        let tracked mut top_pointsto = top.into_typed::<u8>(range_base_addr as usize);

        proof {
            points_to_raw = rest;
            //points_to_map.tracked_insert(range_base_addr as int, top_pointsto);
        }
        
        let current_ptr: *mut u8 = with_exposed_provenance(range_base_addr as usize, expose_provenance(grp.buffer_ptr));
        assert(equal(top_pointsto.ptr().addr(), current_ptr as usize));
        assert(equal(top_pointsto.ptr()@.provenance, current_ptr@.provenance));
        assert(equal(top_pointsto.ptr(), current_ptr));
        ptr_mut_write(current_ptr, Tracked(&mut top_pointsto), 255);
        //assert(points_to_map.contains_key(range_base_addr as int));
        //assert(points_to_map.index(range_base_addr as int).ptr() as int == range_base_addr as nat);
        //assert(top_pointsto.ptr()@.provenance == top.provenance());
        //assert(top.provenance() == points_to_raw.provenance());
    }
}
}
