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



trait T187_AtomicInvariantPredicate<A162_K, A151_V, A163_G, > where A162_K: , A151_V: , A163_G: ,  {
}

trait T188_InvariantPredicate<A162_K, A151_V, > where A162_K: , A151_V: ,  {
}

trait T190_SliceAdditionalSpecFns<A153_T, > where Self: T189_View, Self: T189_View<A151_V = D175_Seq<A153_T, >>, A153_T: ,  {
}

trait T192_ValueToken<A191_Value, > where Self: Sized, A191_Value: ,  {
}

trait T193_UniqueValueToken<A191_Value, > where Self: T192_ValueToken<A191_Value, >, A191_Value: ,  {
}

trait T189_View {
    type A151_V : ;
}

trait T194_DeepView {
    type A151_V : ;
}

trait T195_Clone where Self: Sized,  {
}

trait T155_Allocator {
}

trait T196_OptionAdditionalFns<A153_T, > where Self: Sized, A153_T: ,  {
}

trait T197_VecAdditionalSpecFns<A153_T, > where Self: T189_View, Self: T189_View<A151_V = D175_Seq<A153_T, >>, A153_T: ,  {
}

struct D123_PAtomicU64(
);

struct D73_PCell<A109_V, >(
    PhantomData<A109_V>,
) where A109_V: , ;

struct D74_Vec<A4_T, A113_A, >(
    PhantomData<A4_T>,
    PhantomData<A113_A>,
) where A4_T: , A113_A: , A113_A: Allocator, ;

struct D57_PermissionU64(
);

struct D55_OpenInvariantCredit(
);

struct D52_AtomicU64<A102_K, A103_G, A104_Pred, > where A102_K: , A103_G: , A104_Pred: ,  {
    y65_patomic: D123_PAtomicU64,
    y59_atomic_inv: Tracked<D127_AtomicInvariant<(A102_K, int, ), (D57_PermissionU64, A103_G, ), D126_AtomicPredU64<A104_Pred, >, >, >,
}

struct D126_AtomicPredU64<A104_Pred, > where A104_Pred: ,  {
    y128_p: A104_Pred,
}

struct D127_AtomicInvariant<A102_K, A109_V, A104_Pred, >(
    PhantomData<A102_K>,
    PhantomData<A109_V>,
    PhantomData<A104_Pred>,
) where A102_K: , A109_V: , A104_Pred: , ;

struct D51_InvariantPredicate_auto_VBBuffer_start {
}

struct D71_VBBuffer<A4_T, > where A4_T: ,  {
    y95_buffer: D74_Vec<D73_PCell<A4_T, >, Global, >,
    y53_start: D52_AtomicU64<Tracked<D31_Instance<A4_T, >, >, D23_start<A4_T, >, D51_InvariantPredicate_auto_VBBuffer_start, >,
    y67_instance: Tracked<D31_Instance<A4_T, >, >,
}

struct D35_PointsTo<A109_V, >(
    PhantomData<A109_V>,
) where A109_V: , ;

struct D36_Map<A102_K, A109_V, > where A102_K: , A109_V: ,  {
    y129_mapping: FnSpec<(A102_K, ), D130_Option<A109_V, >, >,
}

enum D130_Option<A4_T, > where A4_T: ,  {
    C131_None(
    ),
    C132_Some(
        A4_T,
    ),
}

struct D23_start<A4_T, > where A4_T: ,  {
    y133_dummy_instance: D31_Instance<A4_T, >,
    y134_no_copy: D135_NoCopy,
}

struct D135_NoCopy(
);

struct D31_Instance<A4_T, > where A4_T: ,  {
    y136_send_sync: PhantomData<D137_SyncSendIfSyncSend<D35_PointsTo<A4_T, >, >>,
    y138_state: PhantomData<D130_Option<Ghost<D139_State<A4_T, >, >, >>,
    y140_location: PhantomData<int>,
}

struct D137_SyncSendIfSyncSend<A4_T, >(
    PhantomData<A4_T>,
) where A4_T: , ;

enum D145_Config<A4_T, > where A4_T: ,  {
    C141_initialize(
        D143_Seq<D142_CellId, >,
        D36_Map<nat, D35_PointsTo<A4_T, >, >,
    ),
    C144_dummy_to_use_type_params(
        D139_State<A4_T, >,
    ),
}

struct D142_CellId(
);

struct D143_Seq<A113_A, >(
    PhantomData<A113_A>,
) where A113_A: , ;

enum D147_Step<A4_T, > where A4_T: ,  {
    C146_checkout_first(
    ),
    C144_dummy_to_use_type_params(
        D139_State<A4_T, >,
    ),
}

struct D139_State<A4_T, > where A4_T: ,  {
    y148_backing_cells: D143_Seq<D142_CellId, >,
    y149_storage: D36_Map<nat, D35_PointsTo<A4_T, >, >,
    y53_start: nat,
}

struct D152_Option<A151_V, >(
    Box<A151_V, >,
) where A151_V: , ;

struct D156_Vec<A153_T, A154_A, >(
    Box<A153_T, >,
    Box<A154_A, >,
) where A153_T: , A154_A: , A154_A: T155_Allocator, ;

struct D157_PAtomicU64(
);

struct D158_PermissionU64(
);

struct D159_PermissionDataU64(
);

struct D161_AtomicPredU64<A160_Pred, >(
    Box<A160_Pred, >,
) where A160_Pred: , ;

struct D164_AtomicU64<A162_K, A163_G, A160_Pred, >(
    Box<A162_K, >,
    Box<A163_G, >,
    Box<A160_Pred, >,
) where A162_K: , A163_G: , A160_Pred: , ;

struct D165_PCell<A151_V, >(
    Box<A151_V, >,
) where A151_V: , ;

struct D166_PointsTo<A151_V, >(
    Box<A151_V, >,
) where A151_V: , ;

struct D167_PointsToData<A151_V, >(
    Box<A151_V, >,
) where A151_V: , ;

struct D168_CellId(
);

struct D169_AtomicInvariant<A162_K, A151_V, A160_Pred, >(
    Box<A162_K, >,
    Box<A151_V, >,
    Box<A160_Pred, >,
) where A162_K: , A151_V: , A160_Pred: , ;

struct D170_OpenInvariantCredit(
);

struct D171_Map<A162_K, A151_V, >(
    Box<A162_K, >,
    Box<A151_V, >,
) where A162_K: , A151_V: , ;

struct D172_Provenance(
);

struct D173_PtrData<A153_T, >(
    Box<A153_T, >,
) where A153_T : ?Sized, ;

struct D174_MemContents<A153_T, >(
    Box<A153_T, >,
) where A153_T: , ;

struct D175_Seq<A154_A, >(
    Box<A154_A, >,
) where A154_A: , ;

struct D176_Set<A154_A, >(
    Box<A154_A, >,
) where A154_A: , ;

struct D177_SyncSendIfSyncSend<A153_T, >(
    Box<A153_T, >,
) where A153_T: , ;

struct D178_NoCopy(
);

struct D179_InstanceId(
);

struct D180_State<A153_T, >(
    Box<A153_T, >,
) where A153_T: , ;

struct D181_Step<A153_T, >(
    Box<A153_T, >,
) where A153_T: , ;

struct D182_Config<A153_T, >(
    Box<A153_T, >,
) where A153_T: , ;

struct D183_Instance<A153_T, >(
    Box<A153_T, >,
) where A153_T: , ;

struct D184_start<A153_T, >(
    Box<A153_T, >,
) where A153_T: , ;

struct D185_VBBuffer<A153_T, >(
    Box<A153_T, >,
) where A153_T: , ;

struct D186_InvariantPredicate_auto_VBBuffer_start(
);

impl<A4_T, > Copy for D137_SyncSendIfSyncSend<A4_T, > where A4_T: ,  {
}

impl<A4_T, > Clone for D137_SyncSendIfSyncSend<A4_T, > where A4_T: ,  {
    fn clone(&self) -> Self { panic!() }
}

impl<A4_T, > Copy for D130_Option<A4_T, > where A4_T: , A4_T: Copy,  {
}

impl<A4_T, > Clone for D130_Option<A4_T, > where A4_T: , A4_T: Clone,  {
    fn clone(&self) -> Self { panic!() }
}

impl<A4_T, A113_A, > Clone for D74_Vec<A4_T, A113_A, > where A4_T: , A113_A: , A4_T: Clone, A113_A: Allocator, A113_A: Clone,  {
    fn clone(&self) -> Self { panic!() }
}

impl<A4_T, > Copy for D31_Instance<A4_T, > where A4_T: ,  {
}

impl<A4_T, > Clone for D31_Instance<A4_T, > where A4_T: ,  {
    fn clone(&self) -> Self { panic!() }
}

impl<A162_K, A163_G, A160_Pred, > T188_InvariantPredicate<(Box<A162_K, >, Box<int, >, ), (Box<D158_PermissionU64, >, Box<A163_G, >, ), > for D161_AtomicPredU64<A160_Pred, > where A162_K: , A163_G: , A160_Pred: , A160_Pred: T187_AtomicInvariantPredicate<A162_K, u64, A163_G, >,  {
}

impl<A153_T, > T189_View for C<3, (Box<A153_T, >, ), > where A153_T : ?Sized,  {
    type A151_V = D173_PtrData<A153_T, >;
}

impl<A153_T, > T189_View for C<12, (Box<C<3, (Box<A153_T, >, ), >, >, ), > where A153_T : ?Sized,  {
    type A151_V = D173_PtrData<A153_T, >;
}

impl<A153_T, > T189_View for C<1, (Box<A153_T, >, ), > where A153_T: ,  {
    type A151_V = D175_Seq<A153_T, >;
}

impl<A153_T, > T194_DeepView for C<1, (Box<A153_T, >, ), > where A153_T: , A153_T: T194_DeepView,  {
    type A151_V = D175_Seq<<A153_T as T194_DeepView>::A151_V, >;
}

impl<A153_T, > T190_SliceAdditionalSpecFns<A153_T, > for C<1, (Box<A153_T, >, ), > where A153_T: ,  {
}

impl<A153_T, > T195_Clone for D177_SyncSendIfSyncSend<A153_T, > where A153_T: ,  {
}

impl<A154_A, > T189_View for C<4, (Box<A154_A, >, ), > where A154_A: T189_View, A154_A : ?Sized,  {
    type A151_V = <A154_A as T189_View>::A151_V;
}

impl<A154_A, > T194_DeepView for C<4, (Box<A154_A, >, ), > where A154_A: T194_DeepView, A154_A : ?Sized,  {
    type A151_V = <A154_A as T194_DeepView>::A151_V;
}

impl<A154_A, > T189_View for C<6, (Box<A154_A, >, Box<C<13, (), >, >, ), > where A154_A: T189_View, A154_A : ?Sized,  {
    type A151_V = <A154_A as T189_View>::A151_V;
}

impl<A154_A, > T194_DeepView for C<6, (Box<A154_A, >, Box<C<13, (), >, >, ), > where A154_A: T194_DeepView, A154_A : ?Sized,  {
    type A151_V = <A154_A as T194_DeepView>::A151_V;
}

impl<A154_A, > T189_View for C<7, (Box<A154_A, >, Box<C<13, (), >, >, ), > where A154_A: , A154_A: T189_View,  {
    type A151_V = <A154_A as T189_View>::A151_V;
}

impl<A154_A, > T194_DeepView for C<7, (Box<A154_A, >, Box<C<13, (), >, >, ), > where A154_A: , A154_A: T194_DeepView,  {
    type A151_V = <A154_A as T194_DeepView>::A151_V;
}

impl<A154_A, > T189_View for C<8, (Box<A154_A, >, Box<C<13, (), >, >, ), > where A154_A: , A154_A: T189_View,  {
    type A151_V = <A154_A as T189_View>::A151_V;
}

impl<A154_A, > T194_DeepView for C<8, (Box<A154_A, >, Box<C<13, (), >, >, ), > where A154_A: , A154_A: T194_DeepView,  {
    type A151_V = <A154_A as T194_DeepView>::A151_V;
}

impl<A153_T, A154_A, > T189_View for D156_Vec<A153_T, A154_A, > where A153_T: , A154_A: , A154_A: T155_Allocator,  {
    type A151_V = D175_Seq<A153_T, >;
}

impl<A153_T, A154_A, > T194_DeepView for D156_Vec<A153_T, A154_A, > where A153_T: , A154_A: , A153_T: T194_DeepView, A154_A: T155_Allocator,  {
    type A151_V = D175_Seq<<A153_T as T194_DeepView>::A151_V, >;
}

impl T189_View for () {
    type A151_V = ();
}

impl T194_DeepView for () {
    type A151_V = ();
}

impl T189_View for bool {
    type A151_V = bool;
}

impl T194_DeepView for bool {
    type A151_V = bool;
}

impl T189_View for u32 {
    type A151_V = u32;
}

impl T194_DeepView for u32 {
    type A151_V = u32;
}

impl T189_View for u64 {
    type A151_V = u64;
}

impl T194_DeepView for u64 {
    type A151_V = u64;
}

impl T189_View for usize {
    type A151_V = usize;
}

impl T194_DeepView for usize {
    type A151_V = usize;
}

impl<A198_A0, > T189_View for (Box<A198_A0, >, ) where A198_A0: , A198_A0: T189_View,  {
    type A151_V = (Box<<A198_A0 as T189_View>::A151_V, >, );
}

impl<A198_A0, > T194_DeepView for (Box<A198_A0, >, ) where A198_A0: , A198_A0: T194_DeepView,  {
    type A151_V = (Box<<A198_A0 as T194_DeepView>::A151_V, >, );
}

impl<A198_A0, A199_A1, > T189_View for (Box<A198_A0, >, Box<A199_A1, >, ) where A198_A0: , A199_A1: , A198_A0: T189_View, A199_A1: T189_View,  {
    type A151_V = (Box<<A198_A0 as T189_View>::A151_V, >, Box<<A199_A1 as T189_View>::A151_V, >, );
}

impl<A198_A0, A199_A1, > T194_DeepView for (Box<A198_A0, >, Box<A199_A1, >, ) where A198_A0: , A199_A1: , A198_A0: T194_DeepView, A199_A1: T194_DeepView,  {
    type A151_V = (Box<<A198_A0 as T194_DeepView>::A151_V, >, Box<<A199_A1 as T194_DeepView>::A151_V, >, );
}

impl<A153_T, > T189_View for D152_Option<A153_T, > where A153_T: ,  {
    type A151_V = D152_Option<A153_T, >;
}

impl<A153_T, > T194_DeepView for D152_Option<A153_T, > where A153_T: , A153_T: T194_DeepView,  {
    type A151_V = D152_Option<<A153_T as T194_DeepView>::A151_V, >;
}

impl<A153_T, > T196_OptionAdditionalFns<A153_T, > for D152_Option<A153_T, > where A153_T: ,  {
}

impl<A153_T, A154_A, > T197_VecAdditionalSpecFns<A153_T, > for D156_Vec<A153_T, A154_A, > where A153_T: , A154_A: , A154_A: T155_Allocator,  {
}

impl T195_Clone for usize {
}

impl T195_Clone for u32 {
}

impl T195_Clone for u64 {
}

impl T195_Clone for bool {
}

impl<A153_T, > T195_Clone for C<12, (Box<C<3, (Box<A153_T, >, ), >, >, ), > where A153_T : ?Sized,  {
}

impl<A153_T, > T195_Clone for C<3, (Box<A153_T, >, ), > where A153_T : ?Sized,  {
}

impl<A153_T, > T195_Clone for C<4, (Box<A153_T, >, ), > where A153_T : ?Sized,  {
}

impl<A153_T, > T195_Clone for D152_Option<A153_T, > where A153_T: , A153_T: T195_Clone,  {
}

impl T195_Clone for C<13, (), > {
}

impl<A153_T, A154_A, > T195_Clone for D156_Vec<A153_T, A154_A, > where A153_T: , A154_A: , A153_T: T195_Clone, A154_A: T155_Allocator, A154_A: T195_Clone,  {
}

impl<A154_A, > T155_Allocator for C<4, (Box<A154_A, >, ), > where A154_A: T155_Allocator, A154_A : ?Sized,  {
}

impl T155_Allocator for C<13, (), > {
}

impl<A154_A, > T195_Clone for C<10, (Box<A154_A, >, ), > where A154_A: ,  {
}

impl<A154_A, > T195_Clone for C<9, (Box<A154_A, >, ), > where A154_A: ,  {
}

impl<A153_T, A154_A, > T195_Clone for C<6, (Box<A153_T, >, Box<A154_A, >, ), > where A153_T: , A154_A: , A153_T: T195_Clone, A154_A: T155_Allocator, A154_A: T195_Clone,  {
}

impl<A153_T, > T192_ValueToken<nat, > for D184_start<A153_T, > where A153_T: ,  {
}

impl<A153_T, > T193_UniqueValueToken<nat, > for D184_start<A153_T, > where A153_T: ,  {
}

impl<A153_T, > T195_Clone for D183_Instance<A153_T, > where A153_T: ,  {
}

impl<A153_T, > T187_AtomicInvariantPredicate<C<10, (Box<D183_Instance<A153_T, >, >, ), >, u64, D184_start<A153_T, >, > for D186_InvariantPredicate_auto_VBBuffer_start where A153_T: ,  {
}

fn f3_checkout_first<A4_T, >(
    x5_pre: (),
    x6_post: (),
) where A4_T: , 
{
    panic!()
}

fn f8_initialize<A4_T, >(
    x9_post: (),
    x10_backing_cells: (),
    x11_storage: (),
) where A4_T: , 
{
    panic!()
}

fn f13_initialize<A4_T, >(
    x14_backing_cells: (),
    x15_storage: (),
) where A4_T: , 
{
    panic!()
}

fn f17_checkout_first<A4_T, >(
    x5_pre: (),
) where A4_T: , 
{
    panic!()
}

fn f19_agree<'a20__, 'a21__, A4_T, >(
    x22_self: &'a20__ D23_start<A4_T, >,
    x24_other: &'a21__ D23_start<A4_T, >,
) where A4_T: , 
{
    panic!()
}

fn f26_arbitrary<A4_T, >(
) -> D23_start<A4_T, > where A4_T: , 
{
    panic!()
}

fn f28_unique<'a20__, 'a21__, A4_T, >(
    x22_self: &'a20__  mut D23_start<A4_T, >,
    x24_other: &'a21__ D23_start<A4_T, >,
) where A4_T: , 
{
    panic!()
}

fn f30_clone<'a20__, A4_T, >(
    x22_self: &'a20__ D31_Instance<A4_T, >,
) -> D31_Instance<A4_T, > where A4_T: , 
{
    panic!()
}

fn f33_initialize<A4_T, >(
    x14_backing_cells: (),
    x15_storage: (),
    x34_param_token_storage: D36_Map<nat, D35_PointsTo<A4_T, >, >,
) -> (Tracked<D31_Instance<A4_T, >, >, Tracked<D23_start<A4_T, >, >, ) where A4_T: , 
{
    panic!()
}

fn f38_checkout_first<'a20__, A4_T, >(
    x22_self: &'a20__ D31_Instance<A4_T, >,
) where A4_T: , 
{
    panic!()
}

fn f40_clone<'a20__, A4_T, >(
    x22_self: &'a20__ D31_Instance<A4_T, >,
) -> D31_Instance<A4_T, > where A4_T: , 
{
    panic!()
}

fn f42_lemma_msg_valid_storage_all<A4_T, >(
    x43_s: (),
) where A4_T: , 
{
    panic!()
}

fn f45_initialize_inductive<A4_T, >(
    x9_post: (),
    x10_backing_cells: (),
    x11_storage: (),
) where A4_T: , 
{
}

fn f47_checkout_first_inductive<A4_T, >(
    x5_pre: (),
    x6_post: (),
) where A4_T: , 
{
}

fn f70_checkout_first<'a20__, A4_T, >(
    x22_self: &'a20__  mut D71_VBBuffer<A4_T, >,
) where A4_T: , 
{
    let x48_start: u64 = 
    {
        let x49_result: u64;
        let x50_atomic: &&D52_AtomicU64<Tracked<D31_Instance<A4_T, >, >, D23_start<A4_T, >, D51_InvariantPredicate_auto_VBBuffer_start, > = &(&((x22_self).y53_start));
        let x54_credit: Tracked<D55_OpenInvariantCredit, > = f56_create_open_invariant_credit();
        {
            f68_spend_open_invariant_credit(x54_credit, );
            {
                let (guard, mut x58_pair): (_, (D57_PermissionU64, D23_start<A4_T, >, )) = open_atomic_invariant_begin((x50_atomic).y59_atomic_inv.borrow());
                
                {
                    let x60_verus_tmp: (D57_PermissionU64, D23_start<A4_T, >, );
                    {
                        (x60_verus_tmp) = (x58_pair)
                    };
                    let mut x61_perm: D57_PermissionU64;
                    let mut x62_start_token: D23_start<A4_T, >;
                    {
                        let (x63_verus_tmp_perm, mut x64_verus_tmp_start_token, ): (D57_PermissionU64, D23_start<A4_T, >, ) = x60_verus_tmp;
                        (x61_perm) = (x63_verus_tmp_perm);
                        (x62_start_token) = (x64_verus_tmp_start_token);
                    };
                    (x49_result) = (f66_load(&((x50_atomic).y65_patomic), tracked_new::<&D57_PermissionU64, >(&(x61_perm), ), ));
                    {
                        {
                            let _: () = f38_checkout_first::<A4_T, >(&(*((x22_self).y67_instance.borrow())), );
                        }
                    };
                    {
                        (x58_pair) = ((x61_perm, x62_start_token, ));
                    }
                };
                open_invariant_end(guard, x58_pair);
            }
        };
        x49_result
    };
}

fn f97_new_buf<A4_T, >(
    x81_len: usize,
) -> D71_VBBuffer<A4_T, > where A4_T: , 
{
    let mut x72_backing_cells_vec: D74_Vec<D73_PCell<A4_T, >, Global, > = f75_new::<D73_PCell<A4_T, >, >();
    let x76_verus_tmp: D36_Map<nat, D35_PointsTo<A4_T, >, >;
    {
        (x76_verus_tmp) = (f77_tracked_empty::<nat, D35_PointsTo<A4_T, >, >())
    };
    let mut x78_perms: D36_Map<nat, D35_PointsTo<A4_T, >, >;
    {
        let mut x79_verus_tmp_perms: D36_Map<nat, D35_PointsTo<A4_T, >, > = x76_verus_tmp;
        (x78_perms) = (x79_verus_tmp_perms);
    };
    while op::<_, bool>((&(f80_len::<D73_PCell<A4_T, >, Global, >(&(x72_backing_cells_vec), )), &(x81_len), )) 
    {
        let (x82_cell, x83_cell_perm, ): (D73_PCell<A4_T, >, Tracked<D35_PointsTo<A4_T, >, >, ) = f84_empty::<A4_T, >();
        f85_push::<D73_PCell<A4_T, >, Global, >(&mut(x72_backing_cells_vec), x82_cell, );
        {
            f86_tracked_insert::<nat, D35_PointsTo<A4_T, >, >(&mut(x78_perms), op::<_, ()>(()), x83_cell_perm.get(), );
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
    let x87_verus_tmp: (Tracked<D31_Instance<A4_T, >, >, Tracked<D23_start<A4_T, >, >, );
    {
        (x87_verus_tmp) = (f33_initialize::<A4_T, >(op::<_, ()>(()), op::<_, ()>(()), x78_perms, ))
    };
    let mut x88_instance: D31_Instance<A4_T, >;
    let mut x89_start_token: D23_start<A4_T, >;
    {
        let (x90_verus_tmp_instance, x91_verus_tmp_start_token, ): (Tracked<D31_Instance<A4_T, >, >, Tracked<D23_start<A4_T, >, >, ) = x87_verus_tmp;
        (x88_instance) = (x90_verus_tmp_instance.get());
        (x89_start_token) = (x91_verus_tmp_start_token.get());
    };
    let x92_tracked_inst: Tracked<D31_Instance<A4_T, >, > = tracked_new::<D31_Instance<A4_T, >, >(f30_clone::<A4_T, >(&(x88_instance), ), );
    let x93_start_atomic: D52_AtomicU64<Tracked<D31_Instance<A4_T, >, >, D23_start<A4_T, >, D51_InvariantPredicate_auto_VBBuffer_start, > = f94_new::<Tracked<D31_Instance<A4_T, >, >, D23_start<A4_T, >, D51_InvariantPredicate_auto_VBBuffer_start, >(op::<_, Ghost<Tracked<D31_Instance<A4_T, >, >, >>(()), op::<_, u64>(()), tracked_new::<D23_start<A4_T, >, >(x89_start_token, ), );
    D71_VBBuffer::<A4_T, > { y67_instance: tracked_new::<D31_Instance<A4_T, >, >(x88_instance, ), y53_start: x93_start_atomic, y95_buffer: x72_backing_cells_vec,  } 
}

fn f100_main(
)
{
    let mut x98_vbuf: D71_VBBuffer<u32, > = f97_new_buf::<u32, >(op::<_, usize>(()), );
    let _: () = f70_checkout_first::<u32, >(&mut(x98_vbuf), );
}

fn f94_new<A102_K, A103_G, A104_Pred, >(
    x105_verus_tmp_k: Ghost<A102_K, >,
    x106_u: u64,
    x107_verus_tmp_g: Tracked<A103_G, >,
) -> D52_AtomicU64<A102_K, A103_G, A104_Pred, > where A102_K: , A103_G: , A104_Pred: , 
{
    panic!()
}

fn f86_tracked_insert<'a20__, A102_K, A109_V, >(
    x22_self: &'a20__  mut D36_Map<A102_K, A109_V, >,
    x110_key: (),
    x111_value: A109_V,
) -> () where A102_K: , A109_V: , 
{
    panic!()
}

fn f85_push<'a20__, A4_T, A113_A, >(
    x114_vec: &'a20__  mut D74_Vec<A4_T, A113_A, >,
    x115_value: A4_T,
) -> () where A4_T: , A113_A: , A113_A: Allocator, 
{
    panic!()
}

fn f84_empty<A109_V, >(
) -> (D73_PCell<A109_V, >, Tracked<D35_PointsTo<A109_V, >, >, ) where A109_V: , 
{
    panic!()
}

fn f80_len<'a20__, A4_T, A113_A, >(
    x114_vec: &'a20__ D74_Vec<A4_T, A113_A, >,
) -> usize where A4_T: , A113_A: , A113_A: Allocator, 
{
    panic!()
}

fn f77_tracked_empty<A102_K, A109_V, >(
) -> D36_Map<A102_K, A109_V, > where A102_K: , A109_V: , 
{
    panic!()
}

fn f75_new<A4_T, >(
) -> D74_Vec<A4_T, Global, > where A4_T: , 
{
    panic!()
}

fn f68_spend_open_invariant_credit(
    x121_credit: Tracked<D55_OpenInvariantCredit, >,
) -> ()
{
    panic!()
}

fn f66_load<'a20__, 'a21__, >(
    x22_self: &'a20__ D123_PAtomicU64,
    x124_verus_tmp_perm: Tracked<&'a21__ D57_PermissionU64, >,
) -> u64 where 
{
    panic!()
}

fn f56_create_open_invariant_credit(
) -> Tracked<D55_OpenInvariantCredit, >
{
    panic!()
}
