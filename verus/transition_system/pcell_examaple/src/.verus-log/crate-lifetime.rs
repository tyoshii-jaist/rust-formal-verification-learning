#![feature(negative_impls)]
#![feature(with_negative_coherence)]
#![feature(box_patterns)]
#![feature(ptr_metadata)]
#![feature(never_type)]
#![feature(allocator_api)]
#![feature(unboxed_closures)]
#![feature(fn_traits)]
#![feature(tuple_trait)]
#![feature(f16)]
#![feature(f128)]
#![allow(non_camel_case_types)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
#![allow(unused_parens)]
#![allow(unused_braces)]
#![allow(dead_code)]
#![allow(unreachable_code)]
#![allow(unconditional_recursion)]
#![allow(unused_mut)]
#![allow(unused_labels)]
use std::marker::PhantomData;
use std::marker::Tuple;
use std::rc::Rc;
use std::sync::Arc;
use std::alloc::Allocator;
use std::alloc::Global;
use std::mem::ManuallyDrop;
use std::ptr::Pointee;
use std::ptr::Thin;
fn op<A, B>(a: A) -> B { panic!() }
fn static_ref<T>(t: T) -> &'static T { panic!() }
fn tracked_new<T>(t: T) -> Tracked<T> { panic!() }
fn tracked_exec_borrow<'a, T>(t: &'a T) -> &'a Tracked<T> { panic!() }
fn clone<T>(t: &T) -> T { panic!() }
fn rc_new<T>(t: T) -> std::rc::Rc<T> { panic!() }
fn arc_new<T>(t: T) -> std::sync::Arc<T> { panic!() }
fn box_new<T>(t: T) -> Box<T> { panic!() }
struct Tracked<A> { a: PhantomData<A> }
impl<A> Tracked<A> {
    pub fn get(self) -> A { panic!() }
    pub fn borrow(&self) -> &A { panic!() }
    pub fn borrow_mut(&mut self) -> &mut A { panic!() }
}
struct Ghost<A> { a: PhantomData<A> }
impl<A> Clone for Ghost<A> { fn clone(&self) -> Self { panic!() } }
impl<A> Copy for Ghost<A> { }
impl<A: Copy> Clone for Tracked<A> { fn clone(&self) -> Self { panic!() } }
impl<A: Copy> Copy for Tracked<A> { }
#[derive(Clone, Copy)] struct int;
#[derive(Clone, Copy)] struct nat;
struct FnSpec<Args, Output> { x: PhantomData<(Args, Output)> }
struct InvariantBlockGuard;
fn open_atomic_invariant_begin<'a, X, V>(_inv: &'a X) -> (InvariantBlockGuard, V) { panic!(); }
fn open_local_invariant_begin<'a, X, V>(_inv: &'a X) -> (InvariantBlockGuard, V) { panic!(); }
fn open_invariant_end<V>(_guard: InvariantBlockGuard, _v: V) { panic!() }
fn index<'a, V, Idx, Output>(v: &'a V, index: Idx) -> &'a Output { panic!() }
trait IndexSet{
fn index_set<Idx, V>(&mut self, index: Idx, val: V) { panic!() }
}
impl<A:?Sized> IndexSet for A {}
struct C<const N: usize, A: ?Sized>(Box<A>);
struct Arr<A: ?Sized, const N: usize>(Box<A>);
fn use_type_invariant<A>(a: A) -> A { a }

struct FnProof<'a, P, M, N, A, O>(PhantomData<P>, PhantomData<M>, PhantomData<N>, PhantomData<&'a fn(A) -> O>);
struct FOpts<const B: u8, C, const D: u8, const E: u8, const G: u8>(PhantomData<C>);
trait ProofFnOnce {}
trait ProofFnMut: ProofFnOnce {}
trait ProofFn: ProofFnMut {}
struct ProofFnConfirm;
trait ConfirmCopy<const D: u8, F> {}
trait ConfirmUsage<A, O, const B: u8, F> {}
impl<const B: u8, C, const E: u8, const G: u8> Clone for FOpts<B, C, 4, E, G> { fn clone(&self) -> Self { panic!() } }
impl<const B: u8, C, const E: u8, const G: u8> Copy for FOpts<B, C, 4, E, G> {}
impl<const B: u8, C, const D: u8, const E: u8, const G: u8> ProofFnOnce for FOpts<B, C, D, E, G> {}
impl<C, const D: u8, const E: u8, const G: u8> ProofFnMut for FOpts<2, C, D, E, G> {}
impl<C, const D: u8, const E: u8, const G: u8> ProofFnMut for FOpts<3, C, D, E, G> {}
impl<C, const D: u8, const E: u8, const G: u8> ProofFn for FOpts<3, C, D, E, G> {}
impl<'a, P: Copy, M, N, A, O> Clone for FnProof<'a, P, M, N, A, O> { fn clone(&self) -> Self { panic!() } }
impl<'a, P: Copy, M, N, A, O> Copy for FnProof<'a, P, M, N, A, O> {}
impl<'a, P: ProofFnOnce, M, N, A: Tuple, O> FnOnce<A> for FnProof<'a, P, M, N, A, O> {
    type Output = O;
    extern "rust-call" fn call_once(self, _: A) -> <Self as FnOnce<A>>::Output { panic!() }
}
impl<'a, P: ProofFnMut, M, N, A: Tuple, O> FnMut<A> for FnProof<'a, P, M, N, A, O> {
    extern "rust-call" fn call_mut(&mut self, _: A) -> <Self as FnOnce<A>>::Output { panic!() }
}
impl<'a, P: ProofFn, M, N, A: Tuple, O> Fn<A> for FnProof<'a, P, M, N, A, O> {
    extern "rust-call" fn call(&self, _: A) -> <Self as FnOnce<A>>::Output { panic!() }
}
impl<F: Copy> ConfirmCopy<4, F> for ProofFnConfirm {}
impl<F> ConfirmCopy<0, F> for ProofFnConfirm {}
impl<A: Tuple, O, F: FnOnce<A, Output = O>> ConfirmUsage<A, O, 1, F> for ProofFnConfirm {}
impl<A: Tuple, O, F: FnMut<A, Output = O>> ConfirmUsage<A, O, 2, F> for ProofFnConfirm {}
impl<A: Tuple, O, F: Fn<A, Output = O>> ConfirmUsage<A, O, 3, F> for ProofFnConfirm {}
pub fn closure_to_fn_proof<'a, const B: u8, const D: u8, const E: u8, const G: u8, M, N, A, O, F: 'a>(_f: F) -> FnProof<'a, FOpts<B, (), D, E, G>, M, N, A, O>
where ProofFnConfirm: ConfirmUsage<A, O, B, F>, ProofFnConfirm: ConfirmCopy<D, F>, M: Tuple, A: Tuple,
{ panic!() }

fn main() {}



trait T374_AtomicInvariantPredicate<A339_K, A328_V, A340_G, > where A339_K: , A328_V: , A340_G: ,  {
}

trait T375_InvariantPredicate<A339_K, A328_V, > where A339_K: , A328_V: ,  {
}

trait T378_FnWithRequiresEnsures<A376_Args, A377_Output, > where Self: Sized, A376_Args: , A377_Output: ,  {
}

trait T380_SliceAdditionalSpecFns<A330_T, > where Self: T379_View, Self: T379_View<A328_V = D352_Seq<A330_T, >>, A330_T: ,  {
}

trait T382_ValueToken<A381_Value, > where Self: Sized, A381_Value: ,  {
}

trait T383_UniqueValueToken<A381_Value, > where Self: T382_ValueToken<A381_Value, >, A381_Value: ,  {
}

trait T379_View {
    type A328_V : ;
}

trait T384_DeepView {
    type A328_V : ;
}

trait T385_Clone where Self: Sized,  {
}

trait T332_Allocator {
}

trait T386_OptionAdditionalFns<A330_T, > where Self: Sized, A330_T: ,  {
}

trait T387_VecAdditionalSpecFns<A330_T, > where Self: T379_View, Self: T379_View<A328_V = D352_Seq<A330_T, >>, A330_T: ,  {
}

struct D272_PAtomicU64(
);

struct D254_JoinHandle<A264_Ret, >(
    PhantomData<A264_Ret>,
) where A264_Ret: , ;

struct D183_PermissionU64(
);

struct D181_OpenInvariantCredit(
);

enum D176_Option<A4_T, > where A4_T: ,  {
    C195_None(
    ),
    C194_Some(
        A4_T,
    ),
}

struct D151_AtomicU64<A284_K, A285_G, A286_Pred, > where A284_K: , A285_G: , A286_Pred: ,  {
    y191_patomic: D272_PAtomicU64,
    y185_atomic_inv: Tracked<D304_AtomicInvariant<(A284_K, int, ), (D183_PermissionU64, A285_G, ), D303_AtomicPredU64<A286_Pred, >, >, >,
}

struct D303_AtomicPredU64<A286_Pred, > where A286_Pred: ,  {
    y305_p: A286_Pred,
}

struct D304_AtomicInvariant<A284_K, A269_V, A286_Pred, >(
    PhantomData<A284_K>,
    PhantomData<A269_V>,
    PhantomData<A286_Pred>,
) where A284_K: , A269_V: , A286_Pred: , ;

struct D123_PCell<A269_V, >(
    PhantomData<A269_V>,
) where A269_V: , ;

struct D124_Vec<A4_T, A276_A, >(
    PhantomData<A4_T>,
    PhantomData<A276_A>,
) where A4_T: , A276_A: , A276_A: Allocator, ;

struct D168_Consumer<A4_T, > where A4_T: ,  {
    y165_queue: Arc<D156_Queue<A4_T, >, Global, >,
    y158_head: usize,
    y169_consumer: Tracked<D59_consumer<A4_T, >, >,
}

struct D164_Producer<A4_T, > where A4_T: ,  {
    y165_queue: Arc<D156_Queue<A4_T, >, Global, >,
    y159_tail: usize,
    y166_producer: Tracked<D52_producer<A4_T, >, >,
}

struct D154_InvariantPredicate_auto_Queue_tail {
}

struct D150_InvariantPredicate_auto_Queue_head {
}

struct D156_Queue<A4_T, > where A4_T: ,  {
    y160_buffer: D124_Vec<D123_PCell<A4_T, >, Global, >,
    y158_head: D151_AtomicU64<Tracked<D66_Instance<A4_T, >, >, D37_head<A4_T, >, D150_InvariantPredicate_auto_Queue_head, >,
    y159_tail: D151_AtomicU64<Tracked<D66_Instance<A4_T, >, >, D45_tail<A4_T, >, D154_InvariantPredicate_auto_Queue_tail, >,
    y157_instance: Tracked<D66_Instance<A4_T, >, >,
}

struct D70_PointsTo<A269_V, >(
    PhantomData<A269_V>,
) where A269_V: , ;

struct D71_Map<A284_K, A269_V, > where A284_K: , A269_V: ,  {
    y306_mapping: FnSpec<(A284_K, ), D176_Option<A269_V, >, >,
}

struct D59_consumer<A4_T, > where A4_T: ,  {
    y307_dummy_instance: D66_Instance<A4_T, >,
    y308_no_copy: D309_NoCopy,
}

struct D309_NoCopy(
);

struct D52_producer<A4_T, > where A4_T: ,  {
    y307_dummy_instance: D66_Instance<A4_T, >,
    y308_no_copy: D309_NoCopy,
}

struct D45_tail<A4_T, > where A4_T: ,  {
    y307_dummy_instance: D66_Instance<A4_T, >,
    y308_no_copy: D309_NoCopy,
}

struct D37_head<A4_T, > where A4_T: ,  {
    y307_dummy_instance: D66_Instance<A4_T, >,
    y308_no_copy: D309_NoCopy,
}

struct D66_Instance<A4_T, > where A4_T: ,  {
    y310_send_sync: PhantomData<D311_SyncSendIfSyncSend<D70_PointsTo<A4_T, >, >>,
    y312_state: PhantomData<D176_Option<Ghost<D313_State<A4_T, >, >, >>,
    y314_location: PhantomData<int>,
}

struct D311_SyncSendIfSyncSend<A4_T, >(
    PhantomData<A4_T>,
) where A4_T: , ;

enum D319_Config<A4_T, > where A4_T: ,  {
    C315_initialize(
        D317_Seq<D316_CellId, >,
        D71_Map<nat, D70_PointsTo<A4_T, >, >,
    ),
    C318_dummy_to_use_type_params(
        D313_State<A4_T, >,
    ),
}

struct D316_CellId(
);

struct D317_Seq<A276_A, >(
    PhantomData<A276_A>,
) where A276_A: , ;

enum D324_Step<A4_T, > where A4_T: ,  {
    C320_produce_start(
    ),
    C321_produce_end(
        D70_PointsTo<A4_T, >,
    ),
    C322_consume_start(
    ),
    C323_consume_end(
        D70_PointsTo<A4_T, >,
    ),
    C318_dummy_to_use_type_params(
        D313_State<A4_T, >,
    ),
}

struct D313_State<A4_T, > where A4_T: ,  {
    y325_backing_cells: D317_Seq<D316_CellId, >,
    y326_storage: D71_Map<nat, D70_PointsTo<A4_T, >, >,
    y158_head: nat,
    y159_tail: nat,
    y166_producer: D109_ProducerState,
    y169_consumer: D111_ConsumerState,
}

enum D111_ConsumerState {
    C112_Idle(
        nat,
    ),
    C113_Consuming(
        nat,
    ),
}

enum D109_ProducerState {
    C112_Idle(
        nat,
    ),
    C110_Producing(
        nat,
    ),
}

struct D329_Option<A328_V, >(
    Box<A328_V, >,
) where A328_V: , ;

struct D333_Vec<A330_T, A331_A, >(
    Box<A330_T, >,
    Box<A331_A, >,
) where A330_T: , A331_A: , A331_A: T332_Allocator, ;

struct D334_PAtomicU64(
);

struct D335_PermissionU64(
);

struct D336_PermissionDataU64(
);

struct D338_AtomicPredU64<A337_Pred, >(
    Box<A337_Pred, >,
) where A337_Pred: , ;

struct D341_AtomicU64<A339_K, A340_G, A337_Pred, >(
    Box<A339_K, >,
    Box<A340_G, >,
    Box<A337_Pred, >,
) where A339_K: , A340_G: , A337_Pred: , ;

struct D342_PCell<A328_V, >(
    Box<A328_V, >,
) where A328_V: , ;

struct D343_PointsTo<A328_V, >(
    Box<A328_V, >,
) where A328_V: , ;

struct D344_PointsToData<A328_V, >(
    Box<A328_V, >,
) where A328_V: , ;

struct D345_CellId(
);

struct D346_AtomicInvariant<A339_K, A328_V, A337_Pred, >(
    Box<A339_K, >,
    Box<A328_V, >,
    Box<A337_Pred, >,
) where A339_K: , A328_V: , A337_Pred: , ;

struct D347_OpenInvariantCredit(
);

struct D348_Map<A339_K, A328_V, >(
    Box<A339_K, >,
    Box<A328_V, >,
) where A339_K: , A328_V: , ;

struct D349_Provenance(
);

struct D350_PtrData<A330_T, >(
    Box<A330_T, >,
) where A330_T : ?Sized, ;

struct D351_MemContents<A330_T, >(
    Box<A330_T, >,
) where A330_T: , ;

struct D352_Seq<A331_A, >(
    Box<A331_A, >,
) where A331_A: , ;

struct D353_Set<A331_A, >(
    Box<A331_A, >,
) where A331_A: , ;

struct D354_SyncSendIfSyncSend<A330_T, >(
    Box<A330_T, >,
) where A330_T: , ;

struct D355_NoCopy(
);

struct D357_JoinHandle<A356_Ret, >(
    Box<A356_Ret, >,
) where A356_Ret: , ;

struct D358_InstanceId(
);

struct D359_State<A330_T, >(
    Box<A330_T, >,
) where A330_T: , ;

struct D360_Step<A330_T, >(
    Box<A330_T, >,
) where A330_T: , ;

struct D361_Config<A330_T, >(
    Box<A330_T, >,
) where A330_T: , ;

struct D362_Instance<A330_T, >(
    Box<A330_T, >,
) where A330_T: , ;

struct D363_head<A330_T, >(
    Box<A330_T, >,
) where A330_T: , ;

struct D364_tail<A330_T, >(
    Box<A330_T, >,
) where A330_T: , ;

struct D365_producer<A330_T, >(
    Box<A330_T, >,
) where A330_T: , ;

struct D366_consumer<A330_T, >(
    Box<A330_T, >,
) where A330_T: , ;

struct D367_ProducerState(
);

struct D368_ConsumerState(
);

struct D369_Queue<A330_T, >(
    Box<A330_T, >,
) where A330_T: , ;

struct D370_InvariantPredicate_auto_Queue_head(
);

struct D371_InvariantPredicate_auto_Queue_tail(
);

struct D372_Producer<A330_T, >(
    Box<A330_T, >,
) where A330_T: , ;

struct D373_Consumer<A330_T, >(
    Box<A330_T, >,
) where A330_T: , ;

impl<A4_T, > Copy for D311_SyncSendIfSyncSend<A4_T, > where A4_T: ,  {
}

impl<A4_T, > Clone for D311_SyncSendIfSyncSend<A4_T, > where A4_T: ,  {
    fn clone(&self) -> Self { panic!() }
}

impl<A4_T, > Copy for D176_Option<A4_T, > where A4_T: , A4_T: Copy,  {
}

impl<A4_T, > Clone for D176_Option<A4_T, > where A4_T: , A4_T: Clone,  {
    fn clone(&self) -> Self { panic!() }
}

impl<A4_T, A276_A, > Clone for D124_Vec<A4_T, A276_A, > where A4_T: , A276_A: , A4_T: Clone, A276_A: Allocator, A276_A: Clone,  {
    fn clone(&self) -> Self { panic!() }
}

impl<A4_T, > Copy for D66_Instance<A4_T, > where A4_T: ,  {
}

impl<A4_T, > Clone for D66_Instance<A4_T, > where A4_T: ,  {
    fn clone(&self) -> Self { panic!() }
}

impl<A339_K, A340_G, A337_Pred, > T375_InvariantPredicate<(Box<A339_K, >, Box<int, >, ), (Box<D335_PermissionU64, >, Box<A340_G, >, ), > for D338_AtomicPredU64<A337_Pred, > where A339_K: , A340_G: , A337_Pred: , A337_Pred: T374_AtomicInvariantPredicate<A339_K, u64, A340_G, >,  {
}

impl<A376_Args, A377_Output, A388_F, > T378_FnWithRequiresEnsures<A376_Args, A377_Output, > for A388_F where A377_Output: , A388_F: , A376_Args: ,  {
}

impl<A330_T, > T379_View for C<3, (Box<A330_T, >, ), > where A330_T : ?Sized,  {
    type A328_V = D350_PtrData<A330_T, >;
}

impl<A330_T, > T379_View for C<12, (Box<C<3, (Box<A330_T, >, ), >, >, ), > where A330_T : ?Sized,  {
    type A328_V = D350_PtrData<A330_T, >;
}

impl<A330_T, > T379_View for C<1, (Box<A330_T, >, ), > where A330_T: ,  {
    type A328_V = D352_Seq<A330_T, >;
}

impl<A330_T, > T384_DeepView for C<1, (Box<A330_T, >, ), > where A330_T: , A330_T: T384_DeepView,  {
    type A328_V = D352_Seq<<A330_T as T384_DeepView>::A328_V, >;
}

impl<A330_T, > T380_SliceAdditionalSpecFns<A330_T, > for C<1, (Box<A330_T, >, ), > where A330_T: ,  {
}

impl<A330_T, > T385_Clone for D354_SyncSendIfSyncSend<A330_T, > where A330_T: ,  {
}

impl<A331_A, > T379_View for C<4, (Box<A331_A, >, ), > where A331_A: T379_View, A331_A : ?Sized,  {
    type A328_V = <A331_A as T379_View>::A328_V;
}

impl<A331_A, > T384_DeepView for C<4, (Box<A331_A, >, ), > where A331_A: T384_DeepView, A331_A : ?Sized,  {
    type A328_V = <A331_A as T384_DeepView>::A328_V;
}

impl<A331_A, > T379_View for C<6, (Box<A331_A, >, Box<C<13, (), >, >, ), > where A331_A: T379_View, A331_A : ?Sized,  {
    type A328_V = <A331_A as T379_View>::A328_V;
}

impl<A331_A, > T384_DeepView for C<6, (Box<A331_A, >, Box<C<13, (), >, >, ), > where A331_A: T384_DeepView, A331_A : ?Sized,  {
    type A328_V = <A331_A as T384_DeepView>::A328_V;
}

impl<A331_A, > T379_View for C<7, (Box<A331_A, >, Box<C<13, (), >, >, ), > where A331_A: , A331_A: T379_View,  {
    type A328_V = <A331_A as T379_View>::A328_V;
}

impl<A331_A, > T384_DeepView for C<7, (Box<A331_A, >, Box<C<13, (), >, >, ), > where A331_A: , A331_A: T384_DeepView,  {
    type A328_V = <A331_A as T384_DeepView>::A328_V;
}

impl<A331_A, > T379_View for C<8, (Box<A331_A, >, Box<C<13, (), >, >, ), > where A331_A: , A331_A: T379_View,  {
    type A328_V = <A331_A as T379_View>::A328_V;
}

impl<A331_A, > T384_DeepView for C<8, (Box<A331_A, >, Box<C<13, (), >, >, ), > where A331_A: , A331_A: T384_DeepView,  {
    type A328_V = <A331_A as T384_DeepView>::A328_V;
}

impl<A330_T, A331_A, > T379_View for D333_Vec<A330_T, A331_A, > where A330_T: , A331_A: , A331_A: T332_Allocator,  {
    type A328_V = D352_Seq<A330_T, >;
}

impl<A330_T, A331_A, > T384_DeepView for D333_Vec<A330_T, A331_A, > where A330_T: , A331_A: , A330_T: T384_DeepView, A331_A: T332_Allocator,  {
    type A328_V = D352_Seq<<A330_T as T384_DeepView>::A328_V, >;
}

impl T379_View for () {
    type A328_V = ();
}

impl T384_DeepView for () {
    type A328_V = ();
}

impl T379_View for bool {
    type A328_V = bool;
}

impl T384_DeepView for bool {
    type A328_V = bool;
}

impl T379_View for u64 {
    type A328_V = u64;
}

impl T384_DeepView for u64 {
    type A328_V = u64;
}

impl T379_View for usize {
    type A328_V = usize;
}

impl T384_DeepView for usize {
    type A328_V = usize;
}

impl T379_View for i32 {
    type A328_V = i32;
}

impl T384_DeepView for i32 {
    type A328_V = i32;
}

impl<A389_A0, > T379_View for (Box<A389_A0, >, ) where A389_A0: , A389_A0: T379_View,  {
    type A328_V = (Box<<A389_A0 as T379_View>::A328_V, >, );
}

impl<A389_A0, > T384_DeepView for (Box<A389_A0, >, ) where A389_A0: , A389_A0: T384_DeepView,  {
    type A328_V = (Box<<A389_A0 as T384_DeepView>::A328_V, >, );
}

impl<A389_A0, A390_A1, > T379_View for (Box<A389_A0, >, Box<A390_A1, >, ) where A389_A0: , A390_A1: , A389_A0: T379_View, A390_A1: T379_View,  {
    type A328_V = (Box<<A389_A0 as T379_View>::A328_V, >, Box<<A390_A1 as T379_View>::A328_V, >, );
}

impl<A389_A0, A390_A1, > T384_DeepView for (Box<A389_A0, >, Box<A390_A1, >, ) where A389_A0: , A390_A1: , A389_A0: T384_DeepView, A390_A1: T384_DeepView,  {
    type A328_V = (Box<<A389_A0 as T384_DeepView>::A328_V, >, Box<<A390_A1 as T384_DeepView>::A328_V, >, );
}

impl<A330_T, > T379_View for D329_Option<A330_T, > where A330_T: ,  {
    type A328_V = D329_Option<A330_T, >;
}

impl<A330_T, > T384_DeepView for D329_Option<A330_T, > where A330_T: , A330_T: T384_DeepView,  {
    type A328_V = D329_Option<<A330_T as T384_DeepView>::A328_V, >;
}

impl<A330_T, > T386_OptionAdditionalFns<A330_T, > for D329_Option<A330_T, > where A330_T: ,  {
}

impl<A330_T, A331_A, > T387_VecAdditionalSpecFns<A330_T, > for D333_Vec<A330_T, A331_A, > where A330_T: , A331_A: , A331_A: T332_Allocator,  {
}

impl T385_Clone for usize {
}

impl T385_Clone for u64 {
}

impl T385_Clone for i32 {
}

impl T385_Clone for bool {
}

impl<A330_T, > T385_Clone for C<12, (Box<C<3, (Box<A330_T, >, ), >, >, ), > where A330_T : ?Sized,  {
}

impl<A330_T, > T385_Clone for C<3, (Box<A330_T, >, ), > where A330_T : ?Sized,  {
}

impl<A330_T, > T385_Clone for C<4, (Box<A330_T, >, ), > where A330_T : ?Sized,  {
}

impl<A330_T, > T385_Clone for D329_Option<A330_T, > where A330_T: , A330_T: T385_Clone,  {
}

impl T385_Clone for C<13, (), > {
}

impl<A330_T, A331_A, > T385_Clone for D333_Vec<A330_T, A331_A, > where A330_T: , A331_A: , A330_T: T385_Clone, A331_A: T332_Allocator, A331_A: T385_Clone,  {
}

impl<A331_A, > T332_Allocator for C<4, (Box<A331_A, >, ), > where A331_A: T332_Allocator, A331_A : ?Sized,  {
}

impl T332_Allocator for C<13, (), > {
}

impl<A331_A, > T385_Clone for C<10, (Box<A331_A, >, ), > where A331_A: ,  {
}

impl<A331_A, > T385_Clone for C<9, (Box<A331_A, >, ), > where A331_A: ,  {
}

impl<A330_T, A331_A, > T385_Clone for C<6, (Box<A330_T, >, Box<A331_A, >, ), > where A330_T: , A331_A: , A330_T: T385_Clone, A331_A: T332_Allocator, A331_A: T385_Clone,  {
}

impl<A330_T, > T382_ValueToken<nat, > for D363_head<A330_T, > where A330_T: ,  {
}

impl<A330_T, > T383_UniqueValueToken<nat, > for D363_head<A330_T, > where A330_T: ,  {
}

impl<A330_T, > T382_ValueToken<nat, > for D364_tail<A330_T, > where A330_T: ,  {
}

impl<A330_T, > T383_UniqueValueToken<nat, > for D364_tail<A330_T, > where A330_T: ,  {
}

impl<A330_T, > T382_ValueToken<D367_ProducerState, > for D365_producer<A330_T, > where A330_T: ,  {
}

impl<A330_T, > T383_UniqueValueToken<D367_ProducerState, > for D365_producer<A330_T, > where A330_T: ,  {
}

impl<A330_T, > T382_ValueToken<D368_ConsumerState, > for D366_consumer<A330_T, > where A330_T: ,  {
}

impl<A330_T, > T383_UniqueValueToken<D368_ConsumerState, > for D366_consumer<A330_T, > where A330_T: ,  {
}

impl<A330_T, > T385_Clone for D362_Instance<A330_T, > where A330_T: ,  {
}

impl<A330_T, > T374_AtomicInvariantPredicate<C<10, (Box<D362_Instance<A330_T, >, >, ), >, u64, D363_head<A330_T, >, > for D370_InvariantPredicate_auto_Queue_head where A330_T: ,  {
}

impl<A330_T, > T374_AtomicInvariantPredicate<C<10, (Box<D362_Instance<A330_T, >, >, ), >, u64, D364_tail<A330_T, >, > for D371_InvariantPredicate_auto_Queue_tail where A330_T: ,  {
}

fn f3_produce_start<A4_T, >(
    x5_pre: (),
    x6_post: (),
) where A4_T: , 
{
    panic!()
}

fn f8_produce_end<A4_T, >(
    x5_pre: (),
    x6_post: (),
    x9_perm: (),
) where A4_T: , 
{
    panic!()
}

fn f11_consume_start<A4_T, >(
    x5_pre: (),
    x6_post: (),
) where A4_T: , 
{
    panic!()
}

fn f13_consume_end<A4_T, >(
    x5_pre: (),
    x6_post: (),
    x9_perm: (),
) where A4_T: , 
{
    panic!()
}

fn f15_initialize<A4_T, >(
    x16_post: (),
    x17_backing_cells: (),
    x18_storage: (),
) where A4_T: , 
{
    panic!()
}

fn f20_initialize<A4_T, >(
    x21_backing_cells: (),
    x22_storage: (),
) where A4_T: , 
{
    panic!()
}

fn f24_produce_start<A4_T, >(
    x5_pre: (),
) where A4_T: , 
{
    panic!()
}

fn f26_produce_end<A4_T, >(
    x5_pre: (),
    x27_perm: (),
) where A4_T: , 
{
    panic!()
}

fn f29_consume_start<A4_T, >(
    x5_pre: (),
) where A4_T: , 
{
    panic!()
}

fn f31_consume_end<A4_T, >(
    x5_pre: (),
    x27_perm: (),
) where A4_T: , 
{
    panic!()
}

fn f33_agree<'a34__, 'a35__, A4_T, >(
    x36_self: &'a34__ D37_head<A4_T, >,
    x38_other: &'a35__ D37_head<A4_T, >,
) where A4_T: , 
{
    panic!()
}

fn f40_arbitrary<A4_T, >(
) -> D37_head<A4_T, > where A4_T: , 
{
    panic!()
}

fn f42_unique<'a34__, 'a35__, A4_T, >(
    x36_self: &'a34__  mut D37_head<A4_T, >,
    x38_other: &'a35__ D37_head<A4_T, >,
) where A4_T: , 
{
    panic!()
}

fn f44_agree<'a34__, 'a35__, A4_T, >(
    x36_self: &'a34__ D45_tail<A4_T, >,
    x38_other: &'a35__ D45_tail<A4_T, >,
) where A4_T: , 
{
    panic!()
}

fn f47_arbitrary<A4_T, >(
) -> D45_tail<A4_T, > where A4_T: , 
{
    panic!()
}

fn f49_unique<'a34__, 'a35__, A4_T, >(
    x36_self: &'a34__  mut D45_tail<A4_T, >,
    x38_other: &'a35__ D45_tail<A4_T, >,
) where A4_T: , 
{
    panic!()
}

fn f51_agree<'a34__, 'a35__, A4_T, >(
    x36_self: &'a34__ D52_producer<A4_T, >,
    x38_other: &'a35__ D52_producer<A4_T, >,
) where A4_T: , 
{
    panic!()
}

fn f54_arbitrary<A4_T, >(
) -> D52_producer<A4_T, > where A4_T: , 
{
    panic!()
}

fn f56_unique<'a34__, 'a35__, A4_T, >(
    x36_self: &'a34__  mut D52_producer<A4_T, >,
    x38_other: &'a35__ D52_producer<A4_T, >,
) where A4_T: , 
{
    panic!()
}

fn f58_agree<'a34__, 'a35__, A4_T, >(
    x36_self: &'a34__ D59_consumer<A4_T, >,
    x38_other: &'a35__ D59_consumer<A4_T, >,
) where A4_T: , 
{
    panic!()
}

fn f61_arbitrary<A4_T, >(
) -> D59_consumer<A4_T, > where A4_T: , 
{
    panic!()
}

fn f63_unique<'a34__, 'a35__, A4_T, >(
    x36_self: &'a34__  mut D59_consumer<A4_T, >,
    x38_other: &'a35__ D59_consumer<A4_T, >,
) where A4_T: , 
{
    panic!()
}

fn f65_clone<'a34__, A4_T, >(
    x36_self: &'a34__ D66_Instance<A4_T, >,
) -> D66_Instance<A4_T, > where A4_T: , 
{
    panic!()
}

fn f68_initialize<A4_T, >(
    x21_backing_cells: (),
    x22_storage: (),
    x69_param_token_storage: D71_Map<nat, D70_PointsTo<A4_T, >, >,
) -> (Tracked<D66_Instance<A4_T, >, >, Tracked<D37_head<A4_T, >, >, Tracked<D45_tail<A4_T, >, >, Tracked<D52_producer<A4_T, >, >, Tracked<D59_consumer<A4_T, >, >, ) where A4_T: , 
{
    panic!()
}

fn f73_produce_start<'a34__, 'a35__, 'a74__, A4_T, >(
    x36_self: &'a34__ D66_Instance<A4_T, >,
    x75_param_token_head: &'a35__ D37_head<A4_T, >,
    x76_param_token_producer: &'a74__  mut D52_producer<A4_T, >,
) -> D70_PointsTo<A4_T, > where A4_T: , 
{
    panic!()
}

fn f78_produce_end<'a34__, 'a35__, 'a74__, A4_T, >(
    x36_self: &'a34__ D66_Instance<A4_T, >,
    x27_perm: (),
    x79_param_token_0_storage: D70_PointsTo<A4_T, >,
    x80_param_token_tail: &'a35__  mut D45_tail<A4_T, >,
    x81_param_token_producer: &'a74__  mut D52_producer<A4_T, >,
) where A4_T: , 
{
    panic!()
}

fn f83_consume_start<'a34__, 'a35__, 'a74__, A4_T, >(
    x36_self: &'a34__ D66_Instance<A4_T, >,
    x84_param_token_tail: &'a35__ D45_tail<A4_T, >,
    x85_param_token_consumer: &'a74__  mut D59_consumer<A4_T, >,
) -> (Ghost<D71_Map<nat, D70_PointsTo<A4_T, >, >, >, Tracked<D70_PointsTo<A4_T, >, >, ) where A4_T: , 
{
    panic!()
}

fn f87_consume_end<'a34__, 'a35__, 'a74__, A4_T, >(
    x36_self: &'a34__ D66_Instance<A4_T, >,
    x27_perm: (),
    x79_param_token_0_storage: D70_PointsTo<A4_T, >,
    x88_param_token_head: &'a35__  mut D37_head<A4_T, >,
    x89_param_token_consumer: &'a74__  mut D59_consumer<A4_T, >,
) where A4_T: , 
{
    panic!()
}

fn f91_clone<'a34__, A4_T, >(
    x36_self: &'a34__ D66_Instance<A4_T, >,
) -> D66_Instance<A4_T, > where A4_T: , 
{
    panic!()
}

fn f93_produce_start_asserts<A4_T, >(
    x5_pre: (),
) where A4_T: , 
{
}

fn f95_produce_end_asserts<A4_T, >(
    x5_pre: (),
    x27_perm: (),
) where A4_T: , 
{
}

fn f97_consume_start_asserts<A4_T, >(
    x5_pre: (),
) where A4_T: , 
{
}

fn f99_consume_end_asserts<A4_T, >(
    x5_pre: (),
    x27_perm: (),
) where A4_T: , 
{
}

fn f101_lemma_msg_not_overlapping<A4_T, >(
    x102_s: (),
) where A4_T: , 
{
    panic!()
}

fn f104_lemma_msg_in_bounds<A4_T, >(
    x102_s: (),
) where A4_T: , 
{
    panic!()
}

fn f106_lemma_msg_valid_storage_all<A4_T, >(
    x102_s: (),
) where A4_T: , 
{
    panic!()
}

fn f108_initialize_inductive<A4_T, >(
    x16_post: (),
    x17_backing_cells: (),
    x18_storage: (),
) where A4_T: , 
{
}

fn f115_produce_start_inductive<A4_T, >(
    x5_pre: (),
    x6_post: (),
) where A4_T: , 
{
}

fn f117_produce_end_inductive<A4_T, >(
    x5_pre: (),
    x6_post: (),
    x9_perm: (),
) where A4_T: , 
{
}

fn f119_consume_start_inductive<A4_T, >(
    x5_pre: (),
    x6_post: (),
) where A4_T: , 
{
}

fn f121_consume_end_inductive<A4_T, >(
    x5_pre: (),
    x6_post: (),
    x9_perm: (),
) where A4_T: , 
{
}

fn f171_new_queue<A4_T, >(
    x131_len: usize,
) -> (D164_Producer<A4_T, >, D168_Consumer<A4_T, >, ) where A4_T: , 
{
    let mut x122_backing_cells_vec: D124_Vec<D123_PCell<A4_T, >, Global, > = f125_new::<D123_PCell<A4_T, >, >();
    let x126_verus_tmp: D71_Map<nat, D70_PointsTo<A4_T, >, >;
    {
        (x126_verus_tmp) = (f127_tracked_empty::<nat, D70_PointsTo<A4_T, >, >())
    };
    let mut x128_perms: D71_Map<nat, D70_PointsTo<A4_T, >, >;
    {
        let mut x129_verus_tmp_perms: D71_Map<nat, D70_PointsTo<A4_T, >, > = x126_verus_tmp;
        (x128_perms) = (x129_verus_tmp_perms);
    };
    while op::<_, bool>((&(f130_len::<D123_PCell<A4_T, >, Global, >(&(x122_backing_cells_vec), )), &(x131_len), )) 
    {
        let (x132_cell, x133_cell_perm, ): (D123_PCell<A4_T, >, Tracked<D70_PointsTo<A4_T, >, >, ) = f134_empty::<A4_T, >();
        f135_push::<D123_PCell<A4_T, >, Global, >(&mut(x122_backing_cells_vec), x132_cell, );
        {
            f136_tracked_insert::<nat, D70_PointsTo<A4_T, >, >(&mut(x128_perms), op::<_, ()>(()), x133_cell_perm.get(), );
        };
        {
            (|| 
            {
            });
        };
        {
            (|| 
            {
            });
        };
        {
            (|| 
            {
            });
        };
    };
    let x137_verus_tmp: (Tracked<D66_Instance<A4_T, >, >, Tracked<D37_head<A4_T, >, >, Tracked<D45_tail<A4_T, >, >, Tracked<D52_producer<A4_T, >, >, Tracked<D59_consumer<A4_T, >, >, );
    {
        (x137_verus_tmp) = (f68_initialize::<A4_T, >(op::<_, ()>(()), op::<_, ()>(()), x128_perms, ))
    };
    let mut x138_instance: D66_Instance<A4_T, >;
    let mut x139_head_token: D37_head<A4_T, >;
    let mut x140_tail_token: D45_tail<A4_T, >;
    let mut x141_producer_token: D52_producer<A4_T, >;
    let mut x142_consumer_token: D59_consumer<A4_T, >;
    {
        let (x143_verus_tmp_instance, x144_verus_tmp_head_token, x145_verus_tmp_tail_token, x146_verus_tmp_producer_token, x147_verus_tmp_consumer_token, ): (Tracked<D66_Instance<A4_T, >, >, Tracked<D37_head<A4_T, >, >, Tracked<D45_tail<A4_T, >, >, Tracked<D52_producer<A4_T, >, >, Tracked<D59_consumer<A4_T, >, >, ) = x137_verus_tmp;
        (x138_instance) = (x143_verus_tmp_instance.get());
        (x139_head_token) = (x144_verus_tmp_head_token.get());
        (x140_tail_token) = (x145_verus_tmp_tail_token.get());
        (x141_producer_token) = (x146_verus_tmp_producer_token.get());
        (x142_consumer_token) = (x147_verus_tmp_consumer_token.get());
    };
    let x148_tracked_inst: Tracked<D66_Instance<A4_T, >, > = tracked_new::<D66_Instance<A4_T, >, >(f65_clone::<A4_T, >(&(x138_instance), ), );
    let x149_head_atomic: D151_AtomicU64<Tracked<D66_Instance<A4_T, >, >, D37_head<A4_T, >, D150_InvariantPredicate_auto_Queue_head, > = f152_new::<Tracked<D66_Instance<A4_T, >, >, D37_head<A4_T, >, D150_InvariantPredicate_auto_Queue_head, >(op::<_, Ghost<Tracked<D66_Instance<A4_T, >, >, >>(()), op::<_, u64>(()), tracked_new::<D37_head<A4_T, >, >(x139_head_token, ), );
    let x153_tail_atomic: D151_AtomicU64<Tracked<D66_Instance<A4_T, >, >, D45_tail<A4_T, >, D154_InvariantPredicate_auto_Queue_tail, > = f152_new::<Tracked<D66_Instance<A4_T, >, >, D45_tail<A4_T, >, D154_InvariantPredicate_auto_Queue_tail, >(op::<_, Ghost<Tracked<D66_Instance<A4_T, >, >, >>(()), op::<_, u64>(()), tracked_new::<D45_tail<A4_T, >, >(x140_tail_token, ), );
    let x155_queue: D156_Queue<A4_T, > = D156_Queue::<A4_T, > { y157_instance: tracked_new::<D66_Instance<A4_T, >, >(x138_instance, ), y158_head: x149_head_atomic, y159_tail: x153_tail_atomic, y160_buffer: x122_backing_cells_vec,  } ;
    let x161_queue_arc: Arc<D156_Queue<A4_T, >, Global, > = f162_new::<D156_Queue<A4_T, >, >(x155_queue, );
    let x163_prod: D164_Producer<A4_T, > = D164_Producer::<A4_T, > { y165_queue: x161_queue_arc.clone(), y159_tail: op::<_, usize>(()), y166_producer: tracked_new::<D52_producer<A4_T, >, >(x141_producer_token, ),  } ;
    let x167_cons: D168_Consumer<A4_T, > = D168_Consumer::<A4_T, > { y165_queue: x161_queue_arc, y158_head: op::<_, usize>(()), y169_consumer: tracked_new::<D59_consumer<A4_T, >, >(x142_consumer_token, ),  } ;
    (x163_prod, x167_cons, )
}

fn f213_enqueue<'a34__, A4_T, >(
    x36_self: &'a34__  mut D164_Producer<A4_T, >,
    x202_t: A4_T,
) where A4_T: , 
{
    loop 
    {
        let x172_queue: &D156_Queue<A4_T, > = &(*((x36_self).y165_queue));
        let x173_len: usize = f130_len::<D123_PCell<A4_T, >, Global, >(&((x172_queue).y160_buffer), );
        {
            (|| 
            {
            });
        };
        let x174_next_tail: usize = if op::<_, bool>((&(op::<_, usize>(((x36_self).y159_tail, op::<_, usize>(()), ))), &(x173_len), )) 
        {
            op::<_, usize>(())
        } else 
        {
            op::<_, usize>(((x36_self).y159_tail, op::<_, usize>(()), ))
        };
        let x175_cell_perm: D176_Option<D70_PointsTo<A4_T, >, >;
        let x177_head: u64 = 
        {
            let x178_result: u64;
            let x179_atomic: &&D151_AtomicU64<Tracked<D66_Instance<A4_T, >, >, D37_head<A4_T, >, D150_InvariantPredicate_auto_Queue_head, > = &(&((x172_queue).y158_head));
            let x180_credit: Tracked<D181_OpenInvariantCredit, > = f182_create_open_invariant_credit();
            {
                f196_spend_open_invariant_credit(x180_credit, );
                {
                    let (guard, mut x184_pair): (_, (D183_PermissionU64, D37_head<A4_T, >, )) = open_atomic_invariant_begin((x179_atomic).y185_atomic_inv.borrow());
                    
                    {
                        let x186_verus_tmp: (D183_PermissionU64, D37_head<A4_T, >, );
                        {
                            (x186_verus_tmp) = (x184_pair)
                        };
                        let mut x187_perm: D183_PermissionU64;
                        let mut x188_head_token: D37_head<A4_T, >;
                        {
                            let (x189_verus_tmp_perm, mut x190_verus_tmp_head_token, ): (D183_PermissionU64, D37_head<A4_T, >, ) = x186_verus_tmp;
                            (x187_perm) = (x189_verus_tmp_perm);
                            (x188_head_token) = (x190_verus_tmp_head_token);
                        };
                        (x178_result) = (f192_load(&((x179_atomic).y191_patomic), tracked_new::<&D183_PermissionU64, >(&(x187_perm), ), ));
                        {
                            {
                                (x175_cell_perm) = (if op::<_, bool>(()) 
                                {
                                    let x193_cp: D70_PointsTo<A4_T, > = f73_produce_start::<A4_T, >(&(*((x172_queue).y157_instance.borrow())), &(x188_head_token), (x36_self).y166_producer.borrow_mut(), );
                                    D176_Option::C194_Some::<D70_PointsTo<A4_T, >, >(x193_cp, )
                                } else 
                                {
                                    D176_Option::C195_None::<D70_PointsTo<A4_T, >, >()
                                });
                            }
                        };
                        {
                            (x184_pair) = ((x187_perm, x188_head_token, ));
                        }
                    };
                    open_invariant_end(guard, x184_pair);
                }
            };
            x178_result
        };
        if op::<_, bool>((&(x177_head), &(op::<_, u64>((x174_next_tail, ))), )) 
        {
            let x197_verus_tmp: D70_PointsTo<A4_T, >;
            {
                (x197_verus_tmp) = (
                match x175_cell_perm {
                    D176_Option::C194_Some(x198_cp, ) => 
                    {
                        x198_cp
                    }
                    D176_Option::C195_None() => 
                    {
                        f199_proof_from_false::<D70_PointsTo<A4_T, >, >()
                    }
                })
            };
            let mut x200_cell_perm: D70_PointsTo<A4_T, >;
            {
                let mut x201_verus_tmp_cell_perm: D70_PointsTo<A4_T, > = x197_verus_tmp;
                (x200_cell_perm) = (x201_verus_tmp_cell_perm);
            };
            f203_put::<A4_T, >(&((*index::<D124_Vec<D123_PCell<A4_T, >, Global, >, usize, D123_PCell<A4_T, >>(&((x172_queue).y160_buffer), (x36_self).y159_tail))), tracked_new::<& mut D70_PointsTo<A4_T, >, >(&mut(x200_cell_perm), ), x202_t, );
            {
                let x204_atomic: &&D151_AtomicU64<Tracked<D66_Instance<A4_T, >, >, D45_tail<A4_T, >, D154_InvariantPredicate_auto_Queue_tail, > = &(&((x172_queue).y159_tail));
                let x205_credit: Tracked<D181_OpenInvariantCredit, > = f182_create_open_invariant_credit();
                {
                    f196_spend_open_invariant_credit(x205_credit, );
                    {
                        let (guard, mut x206_pair): (_, (D183_PermissionU64, D45_tail<A4_T, >, )) = open_atomic_invariant_begin((x204_atomic).y185_atomic_inv.borrow());
                        
                        {
                            let x207_verus_tmp: (D183_PermissionU64, D45_tail<A4_T, >, );
                            {
                                (x207_verus_tmp) = (x206_pair)
                            };
                            let mut x208_perm: D183_PermissionU64;
                            let mut x140_tail_token: D45_tail<A4_T, >;
                            {
                                let (mut x209_verus_tmp_perm, mut x210_verus_tmp_tail_token, ): (D183_PermissionU64, D45_tail<A4_T, >, ) = x207_verus_tmp;
                                (x208_perm) = (x209_verus_tmp_perm);
                                (x140_tail_token) = (x210_verus_tmp_tail_token);
                            };
                            f211_store(&((x204_atomic).y191_patomic), tracked_new::<& mut D183_PermissionU64, >(&mut(x208_perm), ), op::<_, u64>((x174_next_tail, )), );
                            {
                                {
                                    f78_produce_end::<A4_T, >(&(*((x172_queue).y157_instance.borrow())), op::<_, ()>(()), x200_cell_perm, &mut(x140_tail_token), (x36_self).y166_producer.borrow_mut(), );
                                }
                            };
                            {
                                (x206_pair) = ((x208_perm, x140_tail_token, ));
                            }
                        };
                        open_invariant_end(guard, x206_pair);
                    }
                };
            };
            ((x36_self).y159_tail) = (x174_next_tail);
            return;
        } else 
        {
        }
    }
}

fn f245_dequeue<'a34__, A4_T, >(
    x36_self: &'a34__  mut D168_Consumer<A4_T, >,
) -> A4_T where A4_T: , 
{
    loop 
    {
        let x214_queue: &D156_Queue<A4_T, > = &(*((x36_self).y165_queue));
        let x215_len: usize = f130_len::<D123_PCell<A4_T, >, Global, >(&((x214_queue).y160_buffer), );
        {
            (|| 
            {
            });
        };
        let x216_next_head: usize = if op::<_, bool>((&(op::<_, usize>(((x36_self).y158_head, op::<_, usize>(()), ))), &(x215_len), )) 
        {
            op::<_, usize>(())
        } else 
        {
            op::<_, usize>(((x36_self).y158_head, op::<_, usize>(()), ))
        };
        let x217_cell_perm: D176_Option<D70_PointsTo<A4_T, >, >;
        let x218_tail: u64 = 
        {
            let x219_result: u64;
            let x220_atomic: &&D151_AtomicU64<Tracked<D66_Instance<A4_T, >, >, D45_tail<A4_T, >, D154_InvariantPredicate_auto_Queue_tail, > = &(&((x214_queue).y159_tail));
            let x221_credit: Tracked<D181_OpenInvariantCredit, > = f182_create_open_invariant_credit();
            {
                f196_spend_open_invariant_credit(x221_credit, );
                {
                    let (guard, mut x222_pair): (_, (D183_PermissionU64, D45_tail<A4_T, >, )) = open_atomic_invariant_begin((x220_atomic).y185_atomic_inv.borrow());
                    
                    {
                        let x223_verus_tmp: (D183_PermissionU64, D45_tail<A4_T, >, );
                        {
                            (x223_verus_tmp) = (x222_pair)
                        };
                        let mut x224_perm: D183_PermissionU64;
                        let mut x225_tail_token: D45_tail<A4_T, >;
                        {
                            let (x226_verus_tmp_perm, mut x227_verus_tmp_tail_token, ): (D183_PermissionU64, D45_tail<A4_T, >, ) = x223_verus_tmp;
                            (x224_perm) = (x226_verus_tmp_perm);
                            (x225_tail_token) = (x227_verus_tmp_tail_token);
                        };
                        (x219_result) = (f192_load(&((x220_atomic).y191_patomic), tracked_new::<&D183_PermissionU64, >(&(x224_perm), ), ));
                        {
                            {
                                (x217_cell_perm) = (if op::<_, bool>(()) 
                                {
                                    let (_, x228_verus_tmp_cp, ): (Ghost<D71_Map<nat, D70_PointsTo<A4_T, >, >, >, Tracked<D70_PointsTo<A4_T, >, >, ) = f83_consume_start::<A4_T, >(&(*((x214_queue).y157_instance.borrow())), &(x225_tail_token), (x36_self).y169_consumer.borrow_mut(), );
                                    let x229_cp: D70_PointsTo<A4_T, > = x228_verus_tmp_cp.get();
                                    D176_Option::C194_Some::<D70_PointsTo<A4_T, >, >(x229_cp, )
                                } else 
                                {
                                    D176_Option::C195_None::<D70_PointsTo<A4_T, >, >()
                                });
                            }
                        };
                        {
                            (x222_pair) = ((x224_perm, x225_tail_token, ));
                        }
                    };
                    open_invariant_end(guard, x222_pair);
                }
            };
            x219_result
        };
        if op::<_, bool>((&(op::<_, u64>(((x36_self).y158_head, ))), &(x218_tail), )) 
        {
            let x230_verus_tmp: D70_PointsTo<A4_T, >;
            {
                (x230_verus_tmp) = (
                match x217_cell_perm {
                    D176_Option::C194_Some(x231_cp, ) => 
                    {
                        x231_cp
                    }
                    D176_Option::C195_None() => 
                    {
                        f199_proof_from_false::<D70_PointsTo<A4_T, >, >()
                    }
                })
            };
            let mut x232_cell_perm: D70_PointsTo<A4_T, >;
            {
                let mut x233_verus_tmp_cell_perm: D70_PointsTo<A4_T, > = x230_verus_tmp;
                (x232_cell_perm) = (x233_verus_tmp_cell_perm);
            };
            let x234_t: A4_T = f235_take::<A4_T, >(&((*index::<D124_Vec<D123_PCell<A4_T, >, Global, >, usize, D123_PCell<A4_T, >>(&((x214_queue).y160_buffer), (x36_self).y158_head))), tracked_new::<& mut D70_PointsTo<A4_T, >, >(&mut(x232_cell_perm), ), );
            {
                let x236_atomic: &&D151_AtomicU64<Tracked<D66_Instance<A4_T, >, >, D37_head<A4_T, >, D150_InvariantPredicate_auto_Queue_head, > = &(&((x214_queue).y158_head));
                let x237_credit: Tracked<D181_OpenInvariantCredit, > = f182_create_open_invariant_credit();
                {
                    f196_spend_open_invariant_credit(x237_credit, );
                    {
                        let (guard, mut x238_pair): (_, (D183_PermissionU64, D37_head<A4_T, >, )) = open_atomic_invariant_begin((x236_atomic).y185_atomic_inv.borrow());
                        
                        {
                            let x239_verus_tmp: (D183_PermissionU64, D37_head<A4_T, >, );
                            {
                                (x239_verus_tmp) = (x238_pair)
                            };
                            let mut x240_perm: D183_PermissionU64;
                            let mut x241_head_token: D37_head<A4_T, >;
                            {
                                let (mut x242_verus_tmp_perm, mut x243_verus_tmp_head_token, ): (D183_PermissionU64, D37_head<A4_T, >, ) = x239_verus_tmp;
                                (x240_perm) = (x242_verus_tmp_perm);
                                (x241_head_token) = (x243_verus_tmp_head_token);
                            };
                            f211_store(&((x236_atomic).y191_patomic), tracked_new::<& mut D183_PermissionU64, >(&mut(x240_perm), ), op::<_, u64>((x216_next_head, )), );
                            {
                                {
                                    f87_consume_end::<A4_T, >(&(*((x214_queue).y157_instance.borrow())), op::<_, ()>(()), x232_cell_perm, &mut(x241_head_token), (x36_self).y169_consumer.borrow_mut(), );
                                }
                            };
                            {
                                (x238_pair) = ((x240_perm, x241_head_token, ));
                            }
                        };
                        open_invariant_end(guard, x238_pair);
                    }
                };
            };
            ((x36_self).y158_head) = (x216_next_head);
            return x234_t;
        } else 
        {
        }
    }
}

fn f261_main(
)
{
    let (mut x246_producer, mut x247_consumer, ): (D164_Producer<u64, >, D168_Consumer<u64, >, ) = f171_new_queue::<u64, >(op::<_, usize>(()), );
    f213_enqueue::<u64, >(&mut(x246_producer), op::<_, u64>(()), );
    f213_enqueue::<u64, >(&mut(x246_producer), op::<_, u64>(()), );
    f213_enqueue::<u64, >(&mut(x246_producer), op::<_, u64>(()), );
    let x248_x: u64 = f245_dequeue::<u64, >(&mut(x247_consumer), );
    f249_print_u64(x248_x, );
    let x250_x: u64 = f245_dequeue::<u64, >(&mut(x247_consumer), );
    f249_print_u64(x250_x, );
    let x251_x: u64 = f245_dequeue::<u64, >(&mut(x247_consumer), );
    f249_print_u64(x251_x, );
    let x252_producer: D164_Producer<u64, > = x246_producer;
    let x253__join_handle: D254_JoinHandle<(), > = f257_spawn::<_, (), >((move || 
    {
        let mut x255_producer: D164_Producer<u64, > = x252_producer;
        let mut x256_i: u64 = op::<_, u64>(());
        while op::<_, bool>((&(x256_i), &(op::<_, u64>(())), )) 
        {
            f213_enqueue::<u64, >(&mut(x255_producer), x256_i, );
            (x256_i) = (op::<_, u64>((x256_i, op::<_, u64>(()), )));
        }
    }), );
    let mut x258_i: i32 = op::<_, i32>(());
    while op::<_, bool>((&(x258_i), &(op::<_, i32>(())), )) 
    {
        let x259_x: u64 = f245_dequeue::<u64, >(&mut(x247_consumer), );
        f249_print_u64(x259_x, );
        (x258_i) = (op::<_, i32>((x258_i, op::<_, i32>(()), )));
    }
}

fn f257_spawn<A263_F, A264_Ret, >(
    x265_f: A263_F,
) -> D254_JoinHandle<A264_Ret, > where A263_F: , A264_Ret: , A263_F: 'static, A264_Ret: 'static, A263_F: FnOnce() -> A264_Ret, 
{
    panic!()
}

fn f249_print_u64(
    x267_i: u64,
) -> ()
{
    panic!()
}

fn f235_take<'a34__, 'a35__, A269_V, >(
    x36_self: &'a34__ D123_PCell<A269_V, >,
    x270_verus_tmp_perm: Tracked<&'a35__  mut D70_PointsTo<A269_V, >, >,
) -> A269_V where A269_V: , 
{
    panic!()
}

fn f211_store<'a34__, 'a35__, >(
    x36_self: &'a34__ D272_PAtomicU64,
    x270_verus_tmp_perm: Tracked<&'a35__  mut D183_PermissionU64, >,
    x273_v: u64,
) -> () where 
{
    panic!()
}

fn f203_put<'a34__, 'a35__, A269_V, >(
    x36_self: &'a34__ D123_PCell<A269_V, >,
    x270_verus_tmp_perm: Tracked<&'a35__  mut D70_PointsTo<A269_V, >, >,
    x273_v: A269_V,
) -> () where A269_V: , 
{
    panic!()
}

fn f199_proof_from_false<A276_A, >(
) -> A276_A where A276_A: , 
{
    panic!()
}

fn f196_spend_open_invariant_credit(
    x278_credit: Tracked<D181_OpenInvariantCredit, >,
) -> ()
{
    panic!()
}

fn f192_load<'a34__, 'a35__, >(
    x36_self: &'a34__ D272_PAtomicU64,
    x270_verus_tmp_perm: Tracked<&'a35__ D183_PermissionU64, >,
) -> u64 where 
{
    panic!()
}

fn f182_create_open_invariant_credit(
) -> Tracked<D181_OpenInvariantCredit, >
{
    panic!()
}

fn f162_new<A4_T, >(
    x282_t: A4_T,
) -> Arc<A4_T, Global, > where A4_T: , 
{
    panic!()
}

fn f152_new<A284_K, A285_G, A286_Pred, >(
    x287_verus_tmp_k: Ghost<A284_K, >,
    x288_u: u64,
    x289_verus_tmp_g: Tracked<A285_G, >,
) -> D151_AtomicU64<A284_K, A285_G, A286_Pred, > where A284_K: , A285_G: , A286_Pred: , 
{
    panic!()
}

fn f136_tracked_insert<'a34__, A284_K, A269_V, >(
    x36_self: &'a34__  mut D71_Map<A284_K, A269_V, >,
    x291_key: (),
    x292_value: A269_V,
) -> () where A284_K: , A269_V: , 
{
    panic!()
}

fn f135_push<'a34__, A4_T, A276_A, >(
    x294_vec: &'a34__  mut D124_Vec<A4_T, A276_A, >,
    x295_value: A4_T,
) -> () where A4_T: , A276_A: , A276_A: Allocator, 
{
    panic!()
}

fn f134_empty<A269_V, >(
) -> (D123_PCell<A269_V, >, Tracked<D70_PointsTo<A269_V, >, >, ) where A269_V: , 
{
    panic!()
}

fn f130_len<'a34__, A4_T, A276_A, >(
    x294_vec: &'a34__ D124_Vec<A4_T, A276_A, >,
) -> usize where A4_T: , A276_A: , A276_A: Allocator, 
{
    panic!()
}

fn f127_tracked_empty<A284_K, A269_V, >(
) -> D71_Map<A284_K, A269_V, > where A284_K: , A269_V: , 
{
    panic!()
}

fn f125_new<A4_T, >(
) -> D124_Vec<A4_T, Global, > where A4_T: , 
{
    panic!()
}

fn f301_assert_safety(
    x302_b: (),
) -> ()
{
    panic!()
}
