(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-option :pi.enabled false)
(set-option :rewriter.sort_disjunctions false)

;; Prelude

;; AIR prelude
(declare-sort %%Function%% 0)

(declare-sort FuelId 0)
(declare-sort Fuel 0)
(declare-const zero Fuel)
(declare-fun succ (Fuel) Fuel)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert
 (=>
  fuel_defaults
  (forall ((id FuelId)) (!
    (= (fuel_bool id) (fuel_bool_default id))
    :pattern ((fuel_bool id))
    :qid prelude_fuel_defaults
    :skolemid skolem_prelude_fuel_defaults
))))
(declare-datatypes ((fndef 0)) (((fndef_singleton))))
(declare-sort Poly 0)
(declare-sort Height 0)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun F (fndef) Poly)
(declare-fun %I (Poly) Int)
(declare-fun %B (Poly) Bool)
(declare-fun %F (Poly) fndef)
(declare-sort Type 0)
(declare-const BOOL Type)
(declare-const INT Type)
(declare-const NAT Type)
(declare-const CHAR Type)
(declare-const USIZE Type)
(declare-const ISIZE Type)
(declare-const TYPE%tuple%0. Type)
(declare-fun UINT (Int) Type)
(declare-fun SINT (Int) Type)
(declare-fun CONST_INT (Int) Type)
(declare-fun CONST_BOOL (Bool) Type)
(declare-sort Dcr 0)
(declare-const $ Dcr)
(declare-const $slice Dcr)
(declare-fun DST (Dcr) Dcr)
(declare-fun REF (Dcr) Dcr)
(declare-fun MUT_REF (Dcr) Dcr)
(declare-fun BOX (Dcr Type Dcr) Dcr)
(declare-fun RC (Dcr Type Dcr) Dcr)
(declare-fun ARC (Dcr Type Dcr) Dcr)
(declare-fun GHOST (Dcr) Dcr)
(declare-fun TRACKED (Dcr) Dcr)
(declare-fun NEVER (Dcr) Dcr)
(declare-fun CONST_PTR (Dcr) Dcr)
(declare-fun ARRAY (Dcr Type Dcr Type) Type)
(declare-fun SLICE (Dcr Type) Type)
(declare-const STRSLICE Type)
(declare-const ALLOCATOR_GLOBAL Type)
(declare-fun PTR (Dcr Type) Type)
(declare-fun has_type (Poly Type) Bool)
(declare-fun sized (Dcr) Bool)
(declare-fun as_type (Poly Type) Poly)
(declare-fun mk_fun (%%Function%%) %%Function%%)
(declare-fun const_int (Type) Int)
(declare-fun const_bool (Type) Bool)
(assert
 (forall ((d Dcr)) (!
   (=>
    (sized d)
    (sized (DST d))
   )
   :pattern ((sized (DST d)))
   :qid prelude_sized_decorate_struct_inherit
   :skolemid skolem_prelude_sized_decorate_struct_inherit
)))
(assert
 (forall ((d Dcr)) (!
   (sized (REF d))
   :pattern ((sized (REF d)))
   :qid prelude_sized_decorate_ref
   :skolemid skolem_prelude_sized_decorate_ref
)))
(assert
 (forall ((d Dcr)) (!
   (sized (MUT_REF d))
   :pattern ((sized (MUT_REF d)))
   :qid prelude_sized_decorate_mut_ref
   :skolemid skolem_prelude_sized_decorate_mut_ref
)))
(assert
 (forall ((d Dcr) (t Type) (d2 Dcr)) (!
   (sized (BOX d t d2))
   :pattern ((sized (BOX d t d2)))
   :qid prelude_sized_decorate_box
   :skolemid skolem_prelude_sized_decorate_box
)))
(assert
 (forall ((d Dcr) (t Type) (d2 Dcr)) (!
   (sized (RC d t d2))
   :pattern ((sized (RC d t d2)))
   :qid prelude_sized_decorate_rc
   :skolemid skolem_prelude_sized_decorate_rc
)))
(assert
 (forall ((d Dcr) (t Type) (d2 Dcr)) (!
   (sized (ARC d t d2))
   :pattern ((sized (ARC d t d2)))
   :qid prelude_sized_decorate_arc
   :skolemid skolem_prelude_sized_decorate_arc
)))
(assert
 (forall ((d Dcr)) (!
   (sized (GHOST d))
   :pattern ((sized (GHOST d)))
   :qid prelude_sized_decorate_ghost
   :skolemid skolem_prelude_sized_decorate_ghost
)))
(assert
 (forall ((d Dcr)) (!
   (sized (TRACKED d))
   :pattern ((sized (TRACKED d)))
   :qid prelude_sized_decorate_tracked
   :skolemid skolem_prelude_sized_decorate_tracked
)))
(assert
 (forall ((d Dcr)) (!
   (sized (NEVER d))
   :pattern ((sized (NEVER d)))
   :qid prelude_sized_decorate_never
   :skolemid skolem_prelude_sized_decorate_never
)))
(assert
 (forall ((d Dcr)) (!
   (sized (CONST_PTR d))
   :pattern ((sized (CONST_PTR d)))
   :qid prelude_sized_decorate_const_ptr
   :skolemid skolem_prelude_sized_decorate_const_ptr
)))
(assert
 (sized $)
)
(assert
 (forall ((i Int)) (!
   (= i (const_int (CONST_INT i)))
   :pattern ((CONST_INT i))
   :qid prelude_type_id_const_int
   :skolemid skolem_prelude_type_id_const_int
)))
(assert
 (forall ((b Bool)) (!
   (= b (const_bool (CONST_BOOL b)))
   :pattern ((CONST_BOOL b))
   :qid prelude_type_id_const_bool
   :skolemid skolem_prelude_type_id_const_bool
)))
(assert
 (forall ((b Bool)) (!
   (has_type (B b) BOOL)
   :pattern ((has_type (B b) BOOL))
   :qid prelude_has_type_bool
   :skolemid skolem_prelude_has_type_bool
)))
(assert
 (forall ((x Poly) (t Type)) (!
   (and
    (has_type (as_type x t) t)
    (=>
     (has_type x t)
     (= x (as_type x t))
   ))
   :pattern ((as_type x t))
   :qid prelude_as_type
   :skolemid skolem_prelude_as_type
)))
(assert
 (forall ((x %%Function%%)) (!
   (= (mk_fun x) x)
   :pattern ((mk_fun x))
   :qid prelude_mk_fun
   :skolemid skolem_prelude_mk_fun
)))
(assert
 (forall ((x Bool)) (!
   (= x (%B (B x)))
   :pattern ((B x))
   :qid prelude_unbox_box_bool
   :skolemid skolem_prelude_unbox_box_bool
)))
(assert
 (forall ((x Int)) (!
   (= x (%I (I x)))
   :pattern ((I x))
   :qid prelude_unbox_box_int
   :skolemid skolem_prelude_unbox_box_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x BOOL)
    (= x (B (%B x)))
   )
   :pattern ((has_type x BOOL))
   :qid prelude_box_unbox_bool
   :skolemid skolem_prelude_box_unbox_bool
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x INT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x INT))
   :qid prelude_box_unbox_int
   :skolemid skolem_prelude_box_unbox_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x NAT))
   :qid prelude_box_unbox_nat
   :skolemid skolem_prelude_box_unbox_nat
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x USIZE)
    (= x (I (%I x)))
   )
   :pattern ((has_type x USIZE))
   :qid prelude_box_unbox_usize
   :skolemid skolem_prelude_box_unbox_usize
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x ISIZE)
    (= x (I (%I x)))
   )
   :pattern ((has_type x ISIZE))
   :qid prelude_box_unbox_isize
   :skolemid skolem_prelude_box_unbox_isize
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_box_unbox_uint
   :skolemid skolem_prelude_box_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_box_unbox_sint
   :skolemid skolem_prelude_box_unbox_sint
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x CHAR)
    (= x (I (%I x)))
   )
   :pattern ((has_type x CHAR))
   :qid prelude_box_unbox_char
   :skolemid skolem_prelude_box_unbox_char
)))
(declare-fun ext_eq (Bool Type Poly Poly) Bool)
(assert
 (forall ((deep Bool) (t Type) (x Poly) (y Poly)) (!
   (= (= x y) (ext_eq deep t x y))
   :pattern ((ext_eq deep t x y))
   :qid prelude_ext_eq
   :skolemid skolem_prelude_ext_eq
)))
(declare-const SZ Int)
(assert
 (or
  (= SZ 32)
  (= SZ 64)
))
(declare-fun uHi (Int) Int)
(declare-fun iLo (Int) Int)
(declare-fun iHi (Int) Int)
(assert
 (= (uHi 8) 256)
)
(assert
 (= (uHi 16) 65536)
)
(assert
 (= (uHi 32) 4294967296)
)
(assert
 (= (uHi 64) 18446744073709551616)
)
(assert
 (= (uHi 128) (+ 1 340282366920938463463374607431768211455))
)
(assert
 (= (iLo 8) (- 128))
)
(assert
 (= (iLo 16) (- 32768))
)
(assert
 (= (iLo 32) (- 2147483648))
)
(assert
 (= (iLo 64) (- 9223372036854775808))
)
(assert
 (= (iLo 128) (- 170141183460469231731687303715884105728))
)
(assert
 (= (iHi 8) 128)
)
(assert
 (= (iHi 16) 32768)
)
(assert
 (= (iHi 32) 2147483648)
)
(assert
 (= (iHi 64) 9223372036854775808)
)
(assert
 (= (iHi 128) 170141183460469231731687303715884105728)
)
(declare-fun nClip (Int) Int)
(declare-fun uClip (Int Int) Int)
(declare-fun iClip (Int Int) Int)
(declare-fun charClip (Int) Int)
(assert
 (forall ((i Int)) (!
   (and
    (<= 0 (nClip i))
    (=>
     (<= 0 i)
     (= i (nClip i))
   ))
   :pattern ((nClip i))
   :qid prelude_nat_clip
   :skolemid skolem_prelude_nat_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= 0 (uClip bits i))
    (< (uClip bits i) (uHi bits))
    (=>
     (and
      (<= 0 i)
      (< i (uHi bits))
     )
     (= i (uClip bits i))
   ))
   :pattern ((uClip bits i))
   :qid prelude_u_clip
   :skolemid skolem_prelude_u_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= (iLo bits) (iClip bits i))
    (< (iClip bits i) (iHi bits))
    (=>
     (and
      (<= (iLo bits) i)
      (< i (iHi bits))
     )
     (= i (iClip bits i))
   ))
   :pattern ((iClip bits i))
   :qid prelude_i_clip
   :skolemid skolem_prelude_i_clip
)))
(assert
 (forall ((i Int)) (!
   (and
    (or
     (and
      (<= 0 (charClip i))
      (<= (charClip i) 55295)
     )
     (and
      (<= 57344 (charClip i))
      (<= (charClip i) 1114111)
    ))
    (=>
     (or
      (and
       (<= 0 i)
       (<= i 55295)
      )
      (and
       (<= 57344 i)
       (<= i 1114111)
     ))
     (= i (charClip i))
   ))
   :pattern ((charClip i))
   :qid prelude_char_clip
   :skolemid skolem_prelude_char_clip
)))
(declare-fun uInv (Int Int) Bool)
(declare-fun iInv (Int Int) Bool)
(declare-fun charInv (Int) Bool)
(assert
 (forall ((bits Int) (i Int)) (!
   (= (uInv bits i) (and
     (<= 0 i)
     (< i (uHi bits))
   ))
   :pattern ((uInv bits i))
   :qid prelude_u_inv
   :skolemid skolem_prelude_u_inv
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (= (iInv bits i) (and
     (<= (iLo bits) i)
     (< i (iHi bits))
   ))
   :pattern ((iInv bits i))
   :qid prelude_i_inv
   :skolemid skolem_prelude_i_inv
)))
(assert
 (forall ((i Int)) (!
   (= (charInv i) (or
     (and
      (<= 0 i)
      (<= i 55295)
     )
     (and
      (<= 57344 i)
      (<= i 1114111)
   )))
   :pattern ((charInv i))
   :qid prelude_char_inv
   :skolemid skolem_prelude_char_inv
)))
(assert
 (forall ((x Int)) (!
   (has_type (I x) INT)
   :pattern ((has_type (I x) INT))
   :qid prelude_has_type_int
   :skolemid skolem_prelude_has_type_int
)))
(assert
 (forall ((x Int)) (!
   (=>
    (<= 0 x)
    (has_type (I x) NAT)
   )
   :pattern ((has_type (I x) NAT))
   :qid prelude_has_type_nat
   :skolemid skolem_prelude_has_type_nat
)))
(assert
 (forall ((x Int)) (!
   (=>
    (uInv SZ x)
    (has_type (I x) USIZE)
   )
   :pattern ((has_type (I x) USIZE))
   :qid prelude_has_type_usize
   :skolemid skolem_prelude_has_type_usize
)))
(assert
 (forall ((x Int)) (!
   (=>
    (iInv SZ x)
    (has_type (I x) ISIZE)
   )
   :pattern ((has_type (I x) ISIZE))
   :qid prelude_has_type_isize
   :skolemid skolem_prelude_has_type_isize
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (uInv bits x)
    (has_type (I x) (UINT bits))
   )
   :pattern ((has_type (I x) (UINT bits)))
   :qid prelude_has_type_uint
   :skolemid skolem_prelude_has_type_uint
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (iInv bits x)
    (has_type (I x) (SINT bits))
   )
   :pattern ((has_type (I x) (SINT bits)))
   :qid prelude_has_type_sint
   :skolemid skolem_prelude_has_type_sint
)))
(assert
 (forall ((x Int)) (!
   (=>
    (charInv x)
    (has_type (I x) CHAR)
   )
   :pattern ((has_type (I x) CHAR))
   :qid prelude_has_type_char
   :skolemid skolem_prelude_has_type_char
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (<= 0 (%I x))
   )
   :pattern ((has_type x NAT))
   :qid prelude_unbox_int
   :skolemid skolem_prelude_unbox_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x USIZE)
    (uInv SZ (%I x))
   )
   :pattern ((has_type x USIZE))
   :qid prelude_unbox_usize
   :skolemid skolem_prelude_unbox_usize
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x ISIZE)
    (iInv SZ (%I x))
   )
   :pattern ((has_type x ISIZE))
   :qid prelude_unbox_isize
   :skolemid skolem_prelude_unbox_isize
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (uInv bits (%I x))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_unbox_uint
   :skolemid skolem_prelude_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (iInv bits (%I x))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_unbox_sint
   :skolemid skolem_prelude_unbox_sint
)))
(declare-fun Add (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun Mul (Int Int) Int)
(declare-fun EucDiv (Int Int) Int)
(declare-fun EucMod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (= (Add x y) (+ x y))
   :pattern ((Add x y))
   :qid prelude_add
   :skolemid skolem_prelude_add
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Sub x y) (- x y))
   :pattern ((Sub x y))
   :qid prelude_sub
   :skolemid skolem_prelude_sub
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Mul x y) (* x y))
   :pattern ((Mul x y))
   :qid prelude_mul
   :skolemid skolem_prelude_mul
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucDiv x y) (div x y))
   :pattern ((EucDiv x y))
   :qid prelude_eucdiv
   :skolemid skolem_prelude_eucdiv
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucMod x y) (mod x y))
   :pattern ((EucMod x y))
   :qid prelude_eucmod
   :skolemid skolem_prelude_eucmod
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (<= 0 y)
    )
    (<= 0 (Mul x y))
   )
   :pattern ((Mul x y))
   :qid prelude_mul_nats
   :skolemid skolem_prelude_mul_nats
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (< 0 y)
    )
    (and
     (<= 0 (EucDiv x y))
     (<= (EucDiv x y) x)
   ))
   :pattern ((EucDiv x y))
   :qid prelude_div_unsigned_in_bounds
   :skolemid skolem_prelude_div_unsigned_in_bounds
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (< 0 y)
    )
    (and
     (<= 0 (EucMod x y))
     (< (EucMod x y) y)
   ))
   :pattern ((EucMod x y))
   :qid prelude_mod_unsigned_in_bounds
   :skolemid skolem_prelude_mod_unsigned_in_bounds
)))
(declare-fun bitxor (Poly Poly) Int)
(declare-fun bitand (Poly Poly) Int)
(declare-fun bitor (Poly Poly) Int)
(declare-fun bitshr (Poly Poly) Int)
(declare-fun bitshl (Poly Poly) Int)
(declare-fun bitnot (Poly) Int)
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitxor x y))
   )
   :pattern ((uClip bits (bitxor x y)))
   :qid prelude_bit_xor_u_inv
   :skolemid skolem_prelude_bit_xor_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitxor x y))
   )
   :pattern ((iClip bits (bitxor x y)))
   :qid prelude_bit_xor_i_inv
   :skolemid skolem_prelude_bit_xor_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitor x y))
   )
   :pattern ((uClip bits (bitor x y)))
   :qid prelude_bit_or_u_inv
   :skolemid skolem_prelude_bit_or_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitor x y))
   )
   :pattern ((iClip bits (bitor x y)))
   :qid prelude_bit_or_i_inv
   :skolemid skolem_prelude_bit_or_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitand x y))
   )
   :pattern ((uClip bits (bitand x y)))
   :qid prelude_bit_and_u_inv
   :skolemid skolem_prelude_bit_and_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitand x y))
   )
   :pattern ((iClip bits (bitand x y)))
   :qid prelude_bit_and_i_inv
   :skolemid skolem_prelude_bit_and_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (<= 0 (%I y))
    )
    (uInv bits (bitshr x y))
   )
   :pattern ((uClip bits (bitshr x y)))
   :qid prelude_bit_shr_u_inv
   :skolemid skolem_prelude_bit_shr_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (<= 0 (%I y))
    )
    (iInv bits (bitshr x y))
   )
   :pattern ((iClip bits (bitshr x y)))
   :qid prelude_bit_shr_i_inv
   :skolemid skolem_prelude_bit_shr_i_inv
)))
(declare-fun singular_mod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (not (= y 0))
    (= (EucMod x y) (singular_mod x y))
   )
   :pattern ((singular_mod x y))
   :qid prelude_singularmod
   :skolemid skolem_prelude_singularmod
)))
(declare-fun closure_req (Type Dcr Type Poly Poly) Bool)
(declare-fun closure_ens (Type Dcr Type Poly Poly Poly) Bool)
(declare-fun default_ens (Type Dcr Type Poly Poly Poly) Bool)
(declare-fun height (Poly) Height)
(declare-fun height_lt (Height Height) Bool)
(declare-fun fun_from_recursive_field (Poly) Poly)
(declare-fun check_decrease_int (Int Int Bool) Bool)
(assert
 (forall ((cur Int) (prev Int) (otherwise Bool)) (!
   (= (check_decrease_int cur prev otherwise) (or
     (and
      (<= 0 cur)
      (< cur prev)
     )
     (and
      (= cur prev)
      otherwise
   )))
   :pattern ((check_decrease_int cur prev otherwise))
   :qid prelude_check_decrease_int
   :skolemid skolem_prelude_check_decrease_int
)))
(declare-fun check_decrease_height (Poly Poly Bool) Bool)
(assert
 (forall ((cur Poly) (prev Poly) (otherwise Bool)) (!
   (= (check_decrease_height cur prev otherwise) (or
     (height_lt (height cur) (height prev))
     (and
      (= (height cur) (height prev))
      otherwise
   )))
   :pattern ((check_decrease_height cur prev otherwise))
   :qid prelude_check_decrease_height
   :skolemid skolem_prelude_check_decrease_height
)))
(assert
 (forall ((x Height) (y Height)) (!
   (= (height_lt x y) (and
     ((_ partial-order 0) x y)
     (not (= x y))
   ))
   :pattern ((height_lt x y))
   :qid prelude_height_lt
   :skolemid skolem_prelude_height_lt
)))

;; MODULE 'module FifoQueue::show'

;; Fuel
(declare-const fuel%vstd!cell.impl&%2.is_init. FuelId)
(declare-const fuel%vstd!cell.impl&%2.is_uninit. FuelId)
(declare-const fuel%vstd!map.impl&%0.spec_index. FuelId)
(declare-const fuel%vstd!map.axiom_map_index_decreases_finite. FuelId)
(declare-const fuel%vstd!map.axiom_map_index_decreases_infinite. FuelId)
(declare-const fuel%vstd!map.axiom_map_insert_domain. FuelId)
(declare-const fuel%vstd!map.axiom_map_insert_same. FuelId)
(declare-const fuel%vstd!map.axiom_map_insert_different. FuelId)
(declare-const fuel%vstd!map.axiom_map_remove_domain. FuelId)
(declare-const fuel%vstd!map.axiom_map_remove_different. FuelId)
(declare-const fuel%vstd!map.axiom_map_ext_equal. FuelId)
(declare-const fuel%vstd!map.axiom_map_ext_equal_deep. FuelId)
(declare-const fuel%vstd!map_lib.impl&%0.contains_pair. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%6.is_init. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%6.is_uninit. FuelId)
(declare-const fuel%vstd!seq.impl&%0.spec_index. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_index_decreases. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_ext_equal. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_ext_equal_deep. FuelId)
(declare-const fuel%vstd!set.axiom_set_insert_same. FuelId)
(declare-const fuel%vstd!set.axiom_set_insert_different. FuelId)
(declare-const fuel%vstd!set.axiom_set_remove_same. FuelId)
(declare-const fuel%vstd!set.axiom_set_remove_insert. FuelId)
(declare-const fuel%vstd!set.axiom_set_remove_different. FuelId)
(declare-const fuel%vstd!set.axiom_set_ext_equal. FuelId)
(declare-const fuel%vstd!set.axiom_set_ext_equal_deep. FuelId)
(declare-const fuel%vstd!set.axiom_set_insert_finite. FuelId)
(declare-const fuel%vstd!set.axiom_set_remove_finite. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.initialize. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_start. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_end. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_start. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_end. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.inc_wrap. FuelId)
(declare-const fuel%producer_comsumer_example!impl&%0.arrow_Idle_0. FuelId)
(declare-const fuel%producer_comsumer_example!impl&%0.arrow_Producing_0. FuelId)
(declare-const fuel%producer_comsumer_example!impl&%1.arrow_Idle_0. FuelId)
(declare-const fuel%producer_comsumer_example!impl&%1.arrow_Consuming_0. FuelId)
(declare-const fuel%vstd!array.group_array_axioms. FuelId)
(declare-const fuel%vstd!function.group_function_axioms. FuelId)
(declare-const fuel%vstd!laws_cmp.group_laws_cmp. FuelId)
(declare-const fuel%vstd!laws_eq.bool_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u8_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i8_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u16_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i16_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u32_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i32_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u64_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i64_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u128_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i128_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.usize_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.isize_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.group_laws_eq. FuelId)
(declare-const fuel%vstd!layout.group_layout_axioms. FuelId)
(declare-const fuel%vstd!map.group_map_axioms. FuelId)
(declare-const fuel%vstd!multiset.group_multiset_axioms. FuelId)
(declare-const fuel%vstd!raw_ptr.group_raw_ptr_axioms. FuelId)
(declare-const fuel%vstd!seq.group_seq_axioms. FuelId)
(declare-const fuel%vstd!seq_lib.group_filter_ensures. FuelId)
(declare-const fuel%vstd!seq_lib.group_seq_lib_default. FuelId)
(declare-const fuel%vstd!set.group_set_axioms. FuelId)
(declare-const fuel%vstd!set_lib.group_set_lib_default. FuelId)
(declare-const fuel%vstd!slice.group_slice_axioms. FuelId)
(declare-const fuel%vstd!string.group_string_axioms. FuelId)
(declare-const fuel%vstd!std_specs.bits.group_bits_axioms. FuelId)
(declare-const fuel%vstd!std_specs.control_flow.group_control_flow_axioms. FuelId)
(declare-const fuel%vstd!std_specs.hash.group_hash_axioms. FuelId)
(declare-const fuel%vstd!std_specs.range.group_range_axioms. FuelId)
(declare-const fuel%vstd!std_specs.slice.group_slice_axioms. FuelId)
(declare-const fuel%vstd!std_specs.vec.group_vec_axioms. FuelId)
(declare-const fuel%vstd!std_specs.vecdeque.group_vec_dequeue_axioms. FuelId)
(declare-const fuel%vstd!group_vstd_default. FuelId)
(assert
 (distinct fuel%vstd!cell.impl&%2.is_init. fuel%vstd!cell.impl&%2.is_uninit. fuel%vstd!map.impl&%0.spec_index.
  fuel%vstd!map.axiom_map_index_decreases_finite. fuel%vstd!map.axiom_map_index_decreases_infinite.
  fuel%vstd!map.axiom_map_insert_domain. fuel%vstd!map.axiom_map_insert_same. fuel%vstd!map.axiom_map_insert_different.
  fuel%vstd!map.axiom_map_remove_domain. fuel%vstd!map.axiom_map_remove_different.
  fuel%vstd!map.axiom_map_ext_equal. fuel%vstd!map.axiom_map_ext_equal_deep. fuel%vstd!map_lib.impl&%0.contains_pair.
  fuel%vstd!raw_ptr.impl&%6.is_init. fuel%vstd!raw_ptr.impl&%6.is_uninit. fuel%vstd!seq.impl&%0.spec_index.
  fuel%vstd!seq.axiom_seq_index_decreases. fuel%vstd!seq.axiom_seq_ext_equal. fuel%vstd!seq.axiom_seq_ext_equal_deep.
  fuel%vstd!set.axiom_set_insert_same. fuel%vstd!set.axiom_set_insert_different. fuel%vstd!set.axiom_set_remove_same.
  fuel%vstd!set.axiom_set_remove_insert. fuel%vstd!set.axiom_set_remove_different.
  fuel%vstd!set.axiom_set_ext_equal. fuel%vstd!set.axiom_set_ext_equal_deep. fuel%vstd!set.axiom_set_insert_finite.
  fuel%vstd!set.axiom_set_remove_finite. fuel%producer_comsumer_example!FifoQueue.impl&%19.initialize.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_start. fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_end.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_start. fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_end.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.inc_wrap. fuel%producer_comsumer_example!impl&%0.arrow_Idle_0.
  fuel%producer_comsumer_example!impl&%0.arrow_Producing_0. fuel%producer_comsumer_example!impl&%1.arrow_Idle_0.
  fuel%producer_comsumer_example!impl&%1.arrow_Consuming_0. fuel%vstd!array.group_array_axioms.
  fuel%vstd!function.group_function_axioms. fuel%vstd!laws_cmp.group_laws_cmp. fuel%vstd!laws_eq.bool_laws.group_laws_eq.
  fuel%vstd!laws_eq.u8_laws.group_laws_eq. fuel%vstd!laws_eq.i8_laws.group_laws_eq.
  fuel%vstd!laws_eq.u16_laws.group_laws_eq. fuel%vstd!laws_eq.i16_laws.group_laws_eq.
  fuel%vstd!laws_eq.u32_laws.group_laws_eq. fuel%vstd!laws_eq.i32_laws.group_laws_eq.
  fuel%vstd!laws_eq.u64_laws.group_laws_eq. fuel%vstd!laws_eq.i64_laws.group_laws_eq.
  fuel%vstd!laws_eq.u128_laws.group_laws_eq. fuel%vstd!laws_eq.i128_laws.group_laws_eq.
  fuel%vstd!laws_eq.usize_laws.group_laws_eq. fuel%vstd!laws_eq.isize_laws.group_laws_eq.
  fuel%vstd!laws_eq.group_laws_eq. fuel%vstd!layout.group_layout_axioms. fuel%vstd!map.group_map_axioms.
  fuel%vstd!multiset.group_multiset_axioms. fuel%vstd!raw_ptr.group_raw_ptr_axioms.
  fuel%vstd!seq.group_seq_axioms. fuel%vstd!seq_lib.group_filter_ensures. fuel%vstd!seq_lib.group_seq_lib_default.
  fuel%vstd!set.group_set_axioms. fuel%vstd!set_lib.group_set_lib_default. fuel%vstd!slice.group_slice_axioms.
  fuel%vstd!string.group_string_axioms. fuel%vstd!std_specs.bits.group_bits_axioms.
  fuel%vstd!std_specs.control_flow.group_control_flow_axioms. fuel%vstd!std_specs.hash.group_hash_axioms.
  fuel%vstd!std_specs.range.group_range_axioms. fuel%vstd!std_specs.slice.group_slice_axioms.
  fuel%vstd!std_specs.vec.group_vec_axioms. fuel%vstd!std_specs.vecdeque.group_vec_dequeue_axioms.
  fuel%vstd!group_vstd_default.
))
(assert
 (=>
  (fuel_bool_default fuel%vstd!laws_eq.group_laws_eq.)
  (and
   (fuel_bool_default fuel%vstd!laws_eq.bool_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.u8_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.i8_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.u16_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.i16_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.u32_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.i32_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.u64_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.i64_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.u128_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.i128_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.usize_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.isize_laws.group_laws_eq.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!map.group_map_axioms.)
  (and
   (fuel_bool_default fuel%vstd!map.axiom_map_index_decreases_finite.)
   (fuel_bool_default fuel%vstd!map.axiom_map_index_decreases_infinite.)
   (fuel_bool_default fuel%vstd!map.axiom_map_insert_domain.)
   (fuel_bool_default fuel%vstd!map.axiom_map_insert_same.)
   (fuel_bool_default fuel%vstd!map.axiom_map_insert_different.)
   (fuel_bool_default fuel%vstd!map.axiom_map_remove_domain.)
   (fuel_bool_default fuel%vstd!map.axiom_map_remove_different.)
   (fuel_bool_default fuel%vstd!map.axiom_map_ext_equal.)
   (fuel_bool_default fuel%vstd!map.axiom_map_ext_equal_deep.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!seq.group_seq_axioms.)
  (and
   (fuel_bool_default fuel%vstd!seq.axiom_seq_index_decreases.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_ext_equal.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_ext_equal_deep.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!seq_lib.group_seq_lib_default.)
  (fuel_bool_default fuel%vstd!seq_lib.group_filter_ensures.)
))
(assert
 (=>
  (fuel_bool_default fuel%vstd!set.group_set_axioms.)
  (and
   (fuel_bool_default fuel%vstd!set.axiom_set_insert_same.)
   (fuel_bool_default fuel%vstd!set.axiom_set_insert_different.)
   (fuel_bool_default fuel%vstd!set.axiom_set_remove_same.)
   (fuel_bool_default fuel%vstd!set.axiom_set_remove_insert.)
   (fuel_bool_default fuel%vstd!set.axiom_set_remove_different.)
   (fuel_bool_default fuel%vstd!set.axiom_set_ext_equal.)
   (fuel_bool_default fuel%vstd!set.axiom_set_ext_equal_deep.)
   (fuel_bool_default fuel%vstd!set.axiom_set_insert_finite.)
   (fuel_bool_default fuel%vstd!set.axiom_set_remove_finite.)
)))
(assert
 (fuel_bool_default fuel%vstd!group_vstd_default.)
)
(assert
 (=>
  (fuel_bool_default fuel%vstd!group_vstd_default.)
  (and
   (fuel_bool_default fuel%vstd!seq.group_seq_axioms.)
   (fuel_bool_default fuel%vstd!seq_lib.group_seq_lib_default.)
   (fuel_bool_default fuel%vstd!map.group_map_axioms.)
   (fuel_bool_default fuel%vstd!set.group_set_axioms.)
   (fuel_bool_default fuel%vstd!set_lib.group_set_lib_default.)
   (fuel_bool_default fuel%vstd!multiset.group_multiset_axioms.)
   (fuel_bool_default fuel%vstd!function.group_function_axioms.)
   (fuel_bool_default fuel%vstd!laws_eq.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_cmp.group_laws_cmp.)
   (fuel_bool_default fuel%vstd!slice.group_slice_axioms.)
   (fuel_bool_default fuel%vstd!array.group_array_axioms.)
   (fuel_bool_default fuel%vstd!string.group_string_axioms.)
   (fuel_bool_default fuel%vstd!raw_ptr.group_raw_ptr_axioms.)
   (fuel_bool_default fuel%vstd!layout.group_layout_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.range.group_range_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.bits.group_bits_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.control_flow.group_control_flow_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.slice.group_slice_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.vec.group_vec_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.vecdeque.group_vec_dequeue_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.hash.group_hash_axioms.)
)))

;; Datatypes
(declare-sort vstd!cell.CellId. 0)
(declare-sort vstd!seq.Seq<vstd!cell.CellId.>. 0)
(declare-sort vstd!set.Set<nat.>. 0)
(declare-datatypes ((vstd!raw_ptr.MemContents. 0) (producer_comsumer_example!FifoQueue.State.
   0
  ) (producer_comsumer_example!ProducerState. 0) (producer_comsumer_example!ConsumerState.
   0
  ) (tuple%0. 0)
 ) (((vstd!raw_ptr.MemContents./Uninit) (vstd!raw_ptr.MemContents./Init (vstd!raw_ptr.MemContents./Init/?0
     Poly
   ))
  ) ((producer_comsumer_example!FifoQueue.State./State (producer_comsumer_example!FifoQueue.State./State/?backing_cells
     vstd!seq.Seq<vstd!cell.CellId.>.
    ) (producer_comsumer_example!FifoQueue.State./State/?storage Poly) (producer_comsumer_example!FifoQueue.State./State/?head
     Int
    ) (producer_comsumer_example!FifoQueue.State./State/?tail Int) (producer_comsumer_example!FifoQueue.State./State/?producer
     producer_comsumer_example!ProducerState.
    ) (producer_comsumer_example!FifoQueue.State./State/?consumer producer_comsumer_example!ConsumerState.)
   )
  ) ((producer_comsumer_example!ProducerState./Idle (producer_comsumer_example!ProducerState./Idle/?0
     Int
    )
   ) (producer_comsumer_example!ProducerState./Producing (producer_comsumer_example!ProducerState./Producing/?0
     Int
   ))
  ) ((producer_comsumer_example!ConsumerState./Idle (producer_comsumer_example!ConsumerState./Idle/?0
     Int
    )
   ) (producer_comsumer_example!ConsumerState./Consuming (producer_comsumer_example!ConsumerState./Consuming/?0
     Int
   ))
  ) ((tuple%0./tuple%0))
))
(declare-fun vstd!raw_ptr.MemContents./Init/0 (Dcr Type vstd!raw_ptr.MemContents.)
 Poly
)
(declare-fun producer_comsumer_example!FifoQueue.State./State/backing_cells (producer_comsumer_example!FifoQueue.State.)
 vstd!seq.Seq<vstd!cell.CellId.>.
)
(declare-fun producer_comsumer_example!FifoQueue.State./State/storage (producer_comsumer_example!FifoQueue.State.)
 Poly
)
(declare-fun producer_comsumer_example!FifoQueue.State./State/head (producer_comsumer_example!FifoQueue.State.)
 Int
)
(declare-fun producer_comsumer_example!FifoQueue.State./State/tail (producer_comsumer_example!FifoQueue.State.)
 Int
)
(declare-fun producer_comsumer_example!FifoQueue.State./State/producer (producer_comsumer_example!FifoQueue.State.)
 producer_comsumer_example!ProducerState.
)
(declare-fun producer_comsumer_example!FifoQueue.State./State/consumer (producer_comsumer_example!FifoQueue.State.)
 producer_comsumer_example!ConsumerState.
)
(declare-fun producer_comsumer_example!ProducerState./Idle/0 (producer_comsumer_example!ProducerState.)
 Int
)
(declare-fun producer_comsumer_example!ProducerState./Producing/0 (producer_comsumer_example!ProducerState.)
 Int
)
(declare-fun producer_comsumer_example!ConsumerState./Idle/0 (producer_comsumer_example!ConsumerState.)
 Int
)
(declare-fun producer_comsumer_example!ConsumerState./Consuming/0 (producer_comsumer_example!ConsumerState.)
 Int
)
(declare-fun TYPE%vstd!cell.PointsTo. (Dcr Type) Type)
(declare-const TYPE%vstd!cell.CellId. Type)
(declare-fun TYPE%vstd!map.Map. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%vstd!raw_ptr.MemContents. (Dcr Type) Type)
(declare-fun TYPE%vstd!seq.Seq. (Dcr Type) Type)
(declare-fun TYPE%vstd!set.Set. (Dcr Type) Type)
(declare-fun TYPE%producer_comsumer_example!FifoQueue.State. (Dcr Type) Type)
(declare-const TYPE%producer_comsumer_example!ProducerState. Type)
(declare-const TYPE%producer_comsumer_example!ConsumerState. Type)
(declare-fun Poly%vstd!cell.CellId. (vstd!cell.CellId.) Poly)
(declare-fun %Poly%vstd!cell.CellId. (Poly) vstd!cell.CellId.)
(declare-fun Poly%vstd!seq.Seq<vstd!cell.CellId.>. (vstd!seq.Seq<vstd!cell.CellId.>.)
 Poly
)
(declare-fun %Poly%vstd!seq.Seq<vstd!cell.CellId.>. (Poly) vstd!seq.Seq<vstd!cell.CellId.>.)
(declare-fun Poly%vstd!set.Set<nat.>. (vstd!set.Set<nat.>.) Poly)
(declare-fun %Poly%vstd!set.Set<nat.>. (Poly) vstd!set.Set<nat.>.)
(declare-fun Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.MemContents.) Poly)
(declare-fun %Poly%vstd!raw_ptr.MemContents. (Poly) vstd!raw_ptr.MemContents.)
(declare-fun Poly%producer_comsumer_example!FifoQueue.State. (producer_comsumer_example!FifoQueue.State.)
 Poly
)
(declare-fun %Poly%producer_comsumer_example!FifoQueue.State. (Poly) producer_comsumer_example!FifoQueue.State.)
(declare-fun Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!ProducerState.)
 Poly
)
(declare-fun %Poly%producer_comsumer_example!ProducerState. (Poly) producer_comsumer_example!ProducerState.)
(declare-fun Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!ConsumerState.)
 Poly
)
(declare-fun %Poly%producer_comsumer_example!ConsumerState. (Poly) producer_comsumer_example!ConsumerState.)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
(assert
 (forall ((x vstd!cell.CellId.)) (!
   (= x (%Poly%vstd!cell.CellId. (Poly%vstd!cell.CellId. x)))
   :pattern ((Poly%vstd!cell.CellId. x))
   :qid internal_vstd__cell__CellId_box_axiom_definition
   :skolemid skolem_internal_vstd__cell__CellId_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%vstd!cell.CellId.)
    (= x (Poly%vstd!cell.CellId. (%Poly%vstd!cell.CellId. x)))
   )
   :pattern ((has_type x TYPE%vstd!cell.CellId.))
   :qid internal_vstd__cell__CellId_unbox_axiom_definition
   :skolemid skolem_internal_vstd__cell__CellId_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!cell.CellId.)) (!
   (has_type (Poly%vstd!cell.CellId. x) TYPE%vstd!cell.CellId.)
   :pattern ((has_type (Poly%vstd!cell.CellId. x) TYPE%vstd!cell.CellId.))
   :qid internal_vstd__cell__CellId_has_type_always_definition
   :skolemid skolem_internal_vstd__cell__CellId_has_type_always_definition
)))
(assert
 (forall ((x vstd!seq.Seq<vstd!cell.CellId.>.)) (!
   (= x (%Poly%vstd!seq.Seq<vstd!cell.CellId.>. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
      x
   )))
   :pattern ((Poly%vstd!seq.Seq<vstd!cell.CellId.>. x))
   :qid internal_vstd__seq__Seq<vstd!cell.CellId.>_box_axiom_definition
   :skolemid skolem_internal_vstd__seq__Seq<vstd!cell.CellId.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!seq.Seq. $ TYPE%vstd!cell.CellId.))
    (= x (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (%Poly%vstd!seq.Seq<vstd!cell.CellId.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!seq.Seq. $ TYPE%vstd!cell.CellId.)))
   :qid internal_vstd__seq__Seq<vstd!cell.CellId.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__seq__Seq<vstd!cell.CellId.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!seq.Seq<vstd!cell.CellId.>.)) (!
   (has_type (Poly%vstd!seq.Seq<vstd!cell.CellId.>. x) (TYPE%vstd!seq.Seq. $ TYPE%vstd!cell.CellId.))
   :pattern ((has_type (Poly%vstd!seq.Seq<vstd!cell.CellId.>. x) (TYPE%vstd!seq.Seq. $
      TYPE%vstd!cell.CellId.
   )))
   :qid internal_vstd__seq__Seq<vstd!cell.CellId.>_has_type_always_definition
   :skolemid skolem_internal_vstd__seq__Seq<vstd!cell.CellId.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!set.Set<nat.>.)) (!
   (= x (%Poly%vstd!set.Set<nat.>. (Poly%vstd!set.Set<nat.>. x)))
   :pattern ((Poly%vstd!set.Set<nat.>. x))
   :qid internal_vstd__set__Set<nat.>_box_axiom_definition
   :skolemid skolem_internal_vstd__set__Set<nat.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!set.Set. $ NAT))
    (= x (Poly%vstd!set.Set<nat.>. (%Poly%vstd!set.Set<nat.>. x)))
   )
   :pattern ((has_type x (TYPE%vstd!set.Set. $ NAT)))
   :qid internal_vstd__set__Set<nat.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__set__Set<nat.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!set.Set<nat.>.)) (!
   (has_type (Poly%vstd!set.Set<nat.>. x) (TYPE%vstd!set.Set. $ NAT))
   :pattern ((has_type (Poly%vstd!set.Set<nat.>. x) (TYPE%vstd!set.Set. $ NAT)))
   :qid internal_vstd__set__Set<nat.>_has_type_always_definition
   :skolemid skolem_internal_vstd__set__Set<nat.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!raw_ptr.MemContents.)) (!
   (= x (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents. x)))
   :pattern ((Poly%vstd!raw_ptr.MemContents. x))
   :qid internal_vstd__raw_ptr__MemContents_box_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__MemContents_box_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!raw_ptr.MemContents. T&. T&))
    (= x (Poly%vstd!raw_ptr.MemContents. (%Poly%vstd!raw_ptr.MemContents. x)))
   )
   :pattern ((has_type x (TYPE%vstd!raw_ptr.MemContents. T&. T&)))
   :qid internal_vstd__raw_ptr__MemContents_unbox_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__MemContents_unbox_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (has_type (Poly%vstd!raw_ptr.MemContents. vstd!raw_ptr.MemContents./Uninit) (TYPE%vstd!raw_ptr.MemContents.
     T&. T&
   ))
   :pattern ((has_type (Poly%vstd!raw_ptr.MemContents. vstd!raw_ptr.MemContents./Uninit)
     (TYPE%vstd!raw_ptr.MemContents. T&. T&)
   ))
   :qid internal_vstd!raw_ptr.MemContents./Uninit_constructor_definition
   :skolemid skolem_internal_vstd!raw_ptr.MemContents./Uninit_constructor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_0! Poly)) (!
   (=>
    (has_type _0! T&)
    (has_type (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.MemContents./Init _0!)) (TYPE%vstd!raw_ptr.MemContents.
      T&. T&
   )))
   :pattern ((has_type (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.MemContents./Init _0!))
     (TYPE%vstd!raw_ptr.MemContents. T&. T&)
   ))
   :qid internal_vstd!raw_ptr.MemContents./Init_constructor_definition
   :skolemid skolem_internal_vstd!raw_ptr.MemContents./Init_constructor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x vstd!raw_ptr.MemContents.)) (!
   (=>
    (is-vstd!raw_ptr.MemContents./Init x)
    (= (vstd!raw_ptr.MemContents./Init/0 T&. T& x) (vstd!raw_ptr.MemContents./Init/?0 x))
   )
   :pattern ((vstd!raw_ptr.MemContents./Init/0 T&. T& x))
   :qid internal_vstd!raw_ptr.MemContents./Init/0_accessor_definition
   :skolemid skolem_internal_vstd!raw_ptr.MemContents./Init/0_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!raw_ptr.MemContents. T&. T&))
    (has_type (vstd!raw_ptr.MemContents./Init/0 T&. T& (%Poly%vstd!raw_ptr.MemContents.
       x
      )
     ) T&
   ))
   :pattern ((vstd!raw_ptr.MemContents./Init/0 T&. T& (%Poly%vstd!raw_ptr.MemContents.
      x
     )
    ) (has_type x (TYPE%vstd!raw_ptr.MemContents. T&. T&))
   )
   :qid internal_vstd!raw_ptr.MemContents./Init/0_invariant_definition
   :skolemid skolem_internal_vstd!raw_ptr.MemContents./Init/0_invariant_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x vstd!raw_ptr.MemContents.)) (!
   (=>
    (is-vstd!raw_ptr.MemContents./Init x)
    (height_lt (height (vstd!raw_ptr.MemContents./Init/0 T&. T& x)) (height (Poly%vstd!raw_ptr.MemContents.
       x
   ))))
   :pattern ((height (vstd!raw_ptr.MemContents./Init/0 T&. T& x)))
   :qid prelude_datatype_height_vstd!raw_ptr.MemContents./Init/0
   :skolemid skolem_prelude_datatype_height_vstd!raw_ptr.MemContents./Init/0
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.State.)) (!
   (= x (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
      x
   )))
   :pattern ((Poly%producer_comsumer_example!FifoQueue.State. x))
   :qid internal_producer_comsumer_example__FifoQueue__State_box_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__State_box_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&))
    (= x (Poly%producer_comsumer_example!FifoQueue.State. (%Poly%producer_comsumer_example!FifoQueue.State.
       x
   ))))
   :pattern ((has_type x (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&)))
   :qid internal_producer_comsumer_example__FifoQueue__State_unbox_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__State_unbox_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_backing_cells! vstd!seq.Seq<vstd!cell.CellId.>.) (_storage!
    Poly
   ) (_head! Int) (_tail! Int) (_producer! producer_comsumer_example!ProducerState.)
   (_consumer! producer_comsumer_example!ConsumerState.)
  ) (!
   (=>
    (and
     (has_type _storage! (TYPE%vstd!map.Map. $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&)))
     (<= 0 _head!)
     (<= 0 _tail!)
     (has_type (Poly%producer_comsumer_example!ProducerState. _producer!) TYPE%producer_comsumer_example!ProducerState.)
     (has_type (Poly%producer_comsumer_example!ConsumerState. _consumer!) TYPE%producer_comsumer_example!ConsumerState.)
    )
    (has_type (Poly%producer_comsumer_example!FifoQueue.State. (producer_comsumer_example!FifoQueue.State./State
       _backing_cells! _storage! _head! _tail! _producer! _consumer!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&)
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!FifoQueue.State. (producer_comsumer_example!FifoQueue.State./State
       _backing_cells! _storage! _head! _tail! _producer! _consumer!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&)
   ))
   :qid internal_producer_comsumer_example!FifoQueue.State./State_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.State./State_constructor_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.State.)) (!
   (= (producer_comsumer_example!FifoQueue.State./State/backing_cells x) (producer_comsumer_example!FifoQueue.State./State/?backing_cells
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.State./State/backing_cells x))
   :qid internal_producer_comsumer_example!FifoQueue.State./State/backing_cells_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.State./State/backing_cells_accessor_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.State.)) (!
   (= (producer_comsumer_example!FifoQueue.State./State/storage x) (producer_comsumer_example!FifoQueue.State./State/?storage
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.State./State/storage x))
   :qid internal_producer_comsumer_example!FifoQueue.State./State/storage_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.State./State/storage_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&))
    (has_type (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
       x
      )
     ) (TYPE%vstd!map.Map. $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&))
   ))
   :pattern ((producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
      x
     )
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.State./State/storage_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.State./State/storage_invariant_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.State.)) (!
   (= (producer_comsumer_example!FifoQueue.State./State/head x) (producer_comsumer_example!FifoQueue.State./State/?head
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.State./State/head x))
   :qid internal_producer_comsumer_example!FifoQueue.State./State/head_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.State./State/head_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&))
    (<= 0 (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
       x
   ))))
   :pattern ((producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
      x
     )
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.State./State/head_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.State./State/head_invariant_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.State.)) (!
   (= (producer_comsumer_example!FifoQueue.State./State/tail x) (producer_comsumer_example!FifoQueue.State./State/?tail
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.State./State/tail x))
   :qid internal_producer_comsumer_example!FifoQueue.State./State/tail_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.State./State/tail_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&))
    (<= 0 (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
       x
   ))))
   :pattern ((producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
      x
     )
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.State./State/tail_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.State./State/tail_invariant_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.State.)) (!
   (= (producer_comsumer_example!FifoQueue.State./State/producer x) (producer_comsumer_example!FifoQueue.State./State/?producer
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.State./State/producer x))
   :qid internal_producer_comsumer_example!FifoQueue.State./State/producer_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.State./State/producer_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&))
    (has_type (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!FifoQueue.State./State/producer
       (%Poly%producer_comsumer_example!FifoQueue.State. x)
      )
     ) TYPE%producer_comsumer_example!ProducerState.
   ))
   :pattern ((producer_comsumer_example!FifoQueue.State./State/producer (%Poly%producer_comsumer_example!FifoQueue.State.
      x
     )
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.State./State/producer_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.State./State/producer_invariant_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.State.)) (!
   (= (producer_comsumer_example!FifoQueue.State./State/consumer x) (producer_comsumer_example!FifoQueue.State./State/?consumer
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.State./State/consumer x))
   :qid internal_producer_comsumer_example!FifoQueue.State./State/consumer_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.State./State/consumer_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&))
    (has_type (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!FifoQueue.State./State/consumer
       (%Poly%producer_comsumer_example!FifoQueue.State. x)
      )
     ) TYPE%producer_comsumer_example!ConsumerState.
   ))
   :pattern ((producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
      x
     )
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.State./State/consumer_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.State./State/consumer_invariant_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.State.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.State./State x)
    (height_lt (height (producer_comsumer_example!FifoQueue.State./State/storage x)) (
      height (Poly%producer_comsumer_example!FifoQueue.State. x)
   )))
   :pattern ((height (producer_comsumer_example!FifoQueue.State./State/storage x)))
   :qid prelude_datatype_height_producer_comsumer_example!FifoQueue.State./State/storage
   :skolemid skolem_prelude_datatype_height_producer_comsumer_example!FifoQueue.State./State/storage
)))
(assert
 (forall ((T&. Dcr) (T& Type) (deep Bool) (x Poly) (y Poly)) (!
   (=>
    (and
     (has_type x (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&))
     (has_type y (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&))
     (ext_eq deep (TYPE%vstd!seq.Seq. $ TYPE%vstd!cell.CellId.) (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
       (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
         x
       ))
      ) (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
        (%Poly%producer_comsumer_example!FifoQueue.State. y)
     )))
     (ext_eq deep (TYPE%vstd!map.Map. $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&)) (producer_comsumer_example!FifoQueue.State./State/storage
       (%Poly%producer_comsumer_example!FifoQueue.State. x)
      ) (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
        y
     )))
     (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
        x
       )
      ) (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
        y
     )))
     (= (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
        x
       )
      ) (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
        y
     )))
     (= (producer_comsumer_example!FifoQueue.State./State/producer (%Poly%producer_comsumer_example!FifoQueue.State.
        x
       )
      ) (producer_comsumer_example!FifoQueue.State./State/producer (%Poly%producer_comsumer_example!FifoQueue.State.
        y
     )))
     (= (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
        x
       )
      ) (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
        y
    ))))
    (ext_eq deep (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&) x y)
   )
   :pattern ((ext_eq deep (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&) x y))
   :qid internal_producer_comsumer_example!FifoQueue.State./State_ext_equal_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.State./State_ext_equal_definition
)))
(assert
 (forall ((x producer_comsumer_example!ProducerState.)) (!
   (= x (%Poly%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!ProducerState.
      x
   )))
   :pattern ((Poly%producer_comsumer_example!ProducerState. x))
   :qid internal_producer_comsumer_example__ProducerState_box_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__ProducerState_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%producer_comsumer_example!ProducerState.)
    (= x (Poly%producer_comsumer_example!ProducerState. (%Poly%producer_comsumer_example!ProducerState.
       x
   ))))
   :pattern ((has_type x TYPE%producer_comsumer_example!ProducerState.))
   :qid internal_producer_comsumer_example__ProducerState_unbox_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__ProducerState_unbox_axiom_definition
)))
(assert
 (forall ((_0! Int)) (!
   (=>
    (<= 0 _0!)
    (has_type (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!ProducerState./Idle
       _0!
      )
     ) TYPE%producer_comsumer_example!ProducerState.
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!ProducerState./Idle
       _0!
      )
     ) TYPE%producer_comsumer_example!ProducerState.
   ))
   :qid internal_producer_comsumer_example!ProducerState./Idle_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!ProducerState./Idle_constructor_definition
)))
(assert
 (forall ((x producer_comsumer_example!ProducerState.)) (!
   (= (producer_comsumer_example!ProducerState./Idle/0 x) (producer_comsumer_example!ProducerState./Idle/?0
     x
   ))
   :pattern ((producer_comsumer_example!ProducerState./Idle/0 x))
   :qid internal_producer_comsumer_example!ProducerState./Idle/0_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!ProducerState./Idle/0_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%producer_comsumer_example!ProducerState.)
    (<= 0 (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
       x
   ))))
   :pattern ((producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
      x
     )
    ) (has_type x TYPE%producer_comsumer_example!ProducerState.)
   )
   :qid internal_producer_comsumer_example!ProducerState./Idle/0_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!ProducerState./Idle/0_invariant_definition
)))
(assert
 (forall ((_0! Int)) (!
   (=>
    (<= 0 _0!)
    (has_type (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!ProducerState./Producing
       _0!
      )
     ) TYPE%producer_comsumer_example!ProducerState.
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!ProducerState./Producing
       _0!
      )
     ) TYPE%producer_comsumer_example!ProducerState.
   ))
   :qid internal_producer_comsumer_example!ProducerState./Producing_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!ProducerState./Producing_constructor_definition
)))
(assert
 (forall ((x producer_comsumer_example!ProducerState.)) (!
   (= (producer_comsumer_example!ProducerState./Producing/0 x) (producer_comsumer_example!ProducerState./Producing/?0
     x
   ))
   :pattern ((producer_comsumer_example!ProducerState./Producing/0 x))
   :qid internal_producer_comsumer_example!ProducerState./Producing/0_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!ProducerState./Producing/0_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%producer_comsumer_example!ProducerState.)
    (<= 0 (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
       x
   ))))
   :pattern ((producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
      x
     )
    ) (has_type x TYPE%producer_comsumer_example!ProducerState.)
   )
   :qid internal_producer_comsumer_example!ProducerState./Producing/0_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!ProducerState./Producing/0_invariant_definition
)))
(assert
 (forall ((x producer_comsumer_example!ConsumerState.)) (!
   (= x (%Poly%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!ConsumerState.
      x
   )))
   :pattern ((Poly%producer_comsumer_example!ConsumerState. x))
   :qid internal_producer_comsumer_example__ConsumerState_box_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__ConsumerState_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%producer_comsumer_example!ConsumerState.)
    (= x (Poly%producer_comsumer_example!ConsumerState. (%Poly%producer_comsumer_example!ConsumerState.
       x
   ))))
   :pattern ((has_type x TYPE%producer_comsumer_example!ConsumerState.))
   :qid internal_producer_comsumer_example__ConsumerState_unbox_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__ConsumerState_unbox_axiom_definition
)))
(assert
 (forall ((_0! Int)) (!
   (=>
    (<= 0 _0!)
    (has_type (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!ConsumerState./Idle
       _0!
      )
     ) TYPE%producer_comsumer_example!ConsumerState.
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!ConsumerState./Idle
       _0!
      )
     ) TYPE%producer_comsumer_example!ConsumerState.
   ))
   :qid internal_producer_comsumer_example!ConsumerState./Idle_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!ConsumerState./Idle_constructor_definition
)))
(assert
 (forall ((x producer_comsumer_example!ConsumerState.)) (!
   (= (producer_comsumer_example!ConsumerState./Idle/0 x) (producer_comsumer_example!ConsumerState./Idle/?0
     x
   ))
   :pattern ((producer_comsumer_example!ConsumerState./Idle/0 x))
   :qid internal_producer_comsumer_example!ConsumerState./Idle/0_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!ConsumerState./Idle/0_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%producer_comsumer_example!ConsumerState.)
    (<= 0 (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
       x
   ))))
   :pattern ((producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
      x
     )
    ) (has_type x TYPE%producer_comsumer_example!ConsumerState.)
   )
   :qid internal_producer_comsumer_example!ConsumerState./Idle/0_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!ConsumerState./Idle/0_invariant_definition
)))
(assert
 (forall ((_0! Int)) (!
   (=>
    (<= 0 _0!)
    (has_type (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!ConsumerState./Consuming
       _0!
      )
     ) TYPE%producer_comsumer_example!ConsumerState.
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!ConsumerState./Consuming
       _0!
      )
     ) TYPE%producer_comsumer_example!ConsumerState.
   ))
   :qid internal_producer_comsumer_example!ConsumerState./Consuming_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!ConsumerState./Consuming_constructor_definition
)))
(assert
 (forall ((x producer_comsumer_example!ConsumerState.)) (!
   (= (producer_comsumer_example!ConsumerState./Consuming/0 x) (producer_comsumer_example!ConsumerState./Consuming/?0
     x
   ))
   :pattern ((producer_comsumer_example!ConsumerState./Consuming/0 x))
   :qid internal_producer_comsumer_example!ConsumerState./Consuming/0_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!ConsumerState./Consuming/0_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%producer_comsumer_example!ConsumerState.)
    (<= 0 (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
       x
   ))))
   :pattern ((producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
      x
     )
    ) (has_type x TYPE%producer_comsumer_example!ConsumerState.)
   )
   :qid internal_producer_comsumer_example!ConsumerState./Consuming/0_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!ConsumerState./Consuming/0_invariant_definition
)))
(assert
 (forall ((x tuple%0.)) (!
   (= x (%Poly%tuple%0. (Poly%tuple%0. x)))
   :pattern ((Poly%tuple%0. x))
   :qid internal_crate__tuple__0_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%tuple%0.)
    (= x (Poly%tuple%0. (%Poly%tuple%0. x)))
   )
   :pattern ((has_type x TYPE%tuple%0.))
   :qid internal_crate__tuple__0_unbox_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_unbox_axiom_definition
)))
(assert
 (forall ((x tuple%0.)) (!
   (has_type (Poly%tuple%0. x) TYPE%tuple%0.)
   :pattern ((has_type (Poly%tuple%0. x) TYPE%tuple%0.))
   :qid internal_crate__tuple__0_has_type_always_definition
   :skolemid skolem_internal_crate__tuple__0_has_type_always_definition
)))

;; Function-Decl vstd::seq::Seq::len
(declare-fun vstd!seq.Seq.len.? (Dcr Type Poly) Int)

;; Function-Decl vstd::seq::Seq::index
(declare-fun vstd!seq.Seq.index.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::impl&%0::spec_index
(declare-fun vstd!seq.impl&%0.spec_index.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::finite
(declare-fun vstd!set.impl&%0.finite.? (Dcr Type Poly) Bool)

;; Function-Decl vstd::map::impl&%0::dom
(declare-fun vstd!map.impl&%0.dom.? (Dcr Type Dcr Type Poly) Poly)

;; Function-Decl vstd::set::Set::contains
(declare-fun vstd!set.Set.contains.? (Dcr Type Poly Poly) Bool)

;; Function-Decl vstd::map::impl&%0::index
(declare-fun vstd!map.impl&%0.index.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::map::impl&%0::spec_index
(declare-fun vstd!map.impl&%0.spec_index.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::map::impl&%0::insert
(declare-fun vstd!map.impl&%0.insert.? (Dcr Type Dcr Type Poly Poly Poly) Poly)

;; Function-Decl vstd::set::Set::insert
(declare-fun vstd!set.Set.insert.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::map::impl&%0::remove
(declare-fun vstd!map.impl&%0.remove.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::set::Set::remove
(declare-fun vstd!set.Set.remove.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::cell::impl&%2::id
(declare-fun vstd!cell.impl&%2.id.? (Dcr Type Poly) vstd!cell.CellId.)

;; Function-Decl vstd::cell::impl&%2::mem_contents
(declare-fun vstd!cell.impl&%2.mem_contents.? (Dcr Type Poly) vstd!raw_ptr.MemContents.)

;; Function-Decl vstd::raw_ptr::impl&%6::is_init
(declare-fun vstd!raw_ptr.impl&%6.is_init.? (Dcr Type Poly) Bool)

;; Function-Decl vstd::cell::impl&%2::is_init
(declare-fun vstd!cell.impl&%2.is_init.? (Dcr Type Poly) Bool)

;; Function-Decl producer_comsumer_example::ProducerState::arrow_Idle_0
(declare-fun producer_comsumer_example!impl&%0.arrow_Idle_0.? (Poly) Int)

;; Function-Decl producer_comsumer_example::FifoQueue::State::inc_wrap
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? (Dcr Type Poly
  Poly
 ) Int
)

;; Function-Decl vstd::raw_ptr::impl&%6::is_uninit
(declare-fun vstd!raw_ptr.impl&%6.is_uninit.? (Dcr Type Poly) Bool)

;; Function-Decl vstd::cell::impl&%2::is_uninit
(declare-fun vstd!cell.impl&%2.is_uninit.? (Dcr Type Poly) Bool)

;; Function-Decl producer_comsumer_example::FifoQueue::State::produce_start
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.produce_start.? (Dcr Type
  Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::ProducerState::arrow_Producing_0
(declare-fun producer_comsumer_example!impl&%0.arrow_Producing_0.? (Poly) Int)

;; Function-Decl producer_comsumer_example::FifoQueue::State::produce_end
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.produce_end.? (Dcr Type Poly
  Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::ConsumerState::arrow_Idle_0
(declare-fun producer_comsumer_example!impl&%1.arrow_Idle_0.? (Poly) Int)

;; Function-Decl vstd::map_lib::impl&%0::contains_pair
(declare-fun vstd!map_lib.impl&%0.contains_pair.? (Dcr Type Dcr Type Poly Poly Poly)
 Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::consume_start
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.consume_start.? (Dcr Type
  Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::ConsumerState::arrow_Consuming_0
(declare-fun producer_comsumer_example!impl&%1.arrow_Consuming_0.? (Poly) Int)

;; Function-Decl producer_comsumer_example::FifoQueue::State::consume_end
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.consume_end.? (Dcr Type Poly
  Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::next
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.next.? (Dcr Type Poly Poly)
 Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::initialize
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.initialize.? (Dcr Type Poly
  Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::init
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.init.? (Dcr Type Poly) Bool)

;; Function-Axioms vstd::seq::Seq::len
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
    (<= 0 (vstd!seq.Seq.len.? A&. A& self!))
   )
   :pattern ((vstd!seq.Seq.len.? A&. A& self!))
   :qid internal_vstd!seq.Seq.len.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.len.?_pre_post_definition
)))

;; Function-Specs vstd::seq::Seq::index
(declare-fun req%vstd!seq.Seq.index. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%0 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (= (req%vstd!seq.Seq.index. A&. A& self! i!) (=>
     %%global_location_label%%0
     (and
      (<= 0 (%I i!))
      (< (%I i!) (vstd!seq.Seq.len.? A&. A& self!))
   )))
   :pattern ((req%vstd!seq.Seq.index. A&. A& self! i!))
   :qid internal_req__vstd!seq.Seq.index._definition
   :skolemid skolem_internal_req__vstd!seq.Seq.index._definition
)))

;; Function-Axioms vstd::seq::Seq::index
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
    )
    (has_type (vstd!seq.Seq.index.? A&. A& self! i!) A&)
   )
   :pattern ((vstd!seq.Seq.index.? A&. A& self! i!))
   :qid internal_vstd!seq.Seq.index.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.index.?_pre_post_definition
)))

;; Function-Specs vstd::seq::impl&%0::spec_index
(declare-fun req%vstd!seq.impl&%0.spec_index. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%1 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (= (req%vstd!seq.impl&%0.spec_index. A&. A& self! i!) (=>
     %%global_location_label%%1
     (and
      (<= 0 (%I i!))
      (< (%I i!) (vstd!seq.Seq.len.? A&. A& self!))
   )))
   :pattern ((req%vstd!seq.impl&%0.spec_index. A&. A& self! i!))
   :qid internal_req__vstd!seq.impl&__0.spec_index._definition
   :skolemid skolem_internal_req__vstd!seq.impl&__0.spec_index._definition
)))

;; Function-Axioms vstd::seq::impl&%0::spec_index
(assert
 (fuel_bool_default fuel%vstd!seq.impl&%0.spec_index.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!seq.impl&%0.spec_index.)
  (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
    (= (vstd!seq.impl&%0.spec_index.? A&. A& self! i!) (vstd!seq.Seq.index.? A&. A& self!
      i!
    ))
    :pattern ((vstd!seq.impl&%0.spec_index.? A&. A& self! i!))
    :qid internal_vstd!seq.impl&__0.spec_index.?_definition
    :skolemid skolem_internal_vstd!seq.impl&__0.spec_index.?_definition
))))
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
    )
    (has_type (vstd!seq.impl&%0.spec_index.? A&. A& self! i!) A&)
   )
   :pattern ((vstd!seq.impl&%0.spec_index.? A&. A& self! i!))
   :qid internal_vstd!seq.impl&__0.spec_index.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.impl&__0.spec_index.?_pre_post_definition
)))

;; Broadcast vstd::seq::axiom_seq_index_decreases
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_index_decreases.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type i! INT)
     )
     (=>
      (and
       (sized A&.)
       (and
        (<= 0 (%I i!))
        (< (%I i!) (vstd!seq.Seq.len.? A&. A& s!))
      ))
      (height_lt (height (vstd!seq.Seq.index.? A&. A& s! i!)) (height s!))
    ))
    :pattern ((height (vstd!seq.Seq.index.? A&. A& s! i!)))
    :qid user_vstd__seq__axiom_seq_index_decreases_0
    :skolemid skolem_user_vstd__seq__axiom_seq_index_decreases_0
))))

;; Broadcast vstd::seq::axiom_seq_ext_equal
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_ext_equal.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
     )
     (=>
      (sized A&.)
      (= (ext_eq false (TYPE%vstd!seq.Seq. A&. A&) s1! s2!) (and
        (= (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))
        (forall ((i$ Poly)) (!
          (=>
           (has_type i$ INT)
           (=>
            (and
             (<= 0 (%I i$))
             (< (%I i$) (vstd!seq.Seq.len.? A&. A& s1!))
            )
            (= (vstd!seq.Seq.index.? A&. A& s1! i$) (vstd!seq.Seq.index.? A&. A& s2! i$))
          ))
          :pattern ((vstd!seq.Seq.index.? A&. A& s1! i$))
          :pattern ((vstd!seq.Seq.index.? A&. A& s2! i$))
          :qid user_vstd__seq__axiom_seq_ext_equal_1
          :skolemid skolem_user_vstd__seq__axiom_seq_ext_equal_1
    ))))))
    :pattern ((ext_eq false (TYPE%vstd!seq.Seq. A&. A&) s1! s2!))
    :qid user_vstd__seq__axiom_seq_ext_equal_2
    :skolemid skolem_user_vstd__seq__axiom_seq_ext_equal_2
))))

;; Broadcast vstd::seq::axiom_seq_ext_equal_deep
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_ext_equal_deep.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
     )
     (=>
      (sized A&.)
      (= (ext_eq true (TYPE%vstd!seq.Seq. A&. A&) s1! s2!) (and
        (= (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))
        (forall ((i$ Poly)) (!
          (=>
           (has_type i$ INT)
           (=>
            (and
             (<= 0 (%I i$))
             (< (%I i$) (vstd!seq.Seq.len.? A&. A& s1!))
            )
            (ext_eq true A& (vstd!seq.Seq.index.? A&. A& s1! i$) (vstd!seq.Seq.index.? A&. A& s2!
              i$
          ))))
          :pattern ((vstd!seq.Seq.index.? A&. A& s1! i$))
          :pattern ((vstd!seq.Seq.index.? A&. A& s2! i$))
          :qid user_vstd__seq__axiom_seq_ext_equal_deep_3
          :skolemid skolem_user_vstd__seq__axiom_seq_ext_equal_deep_3
    ))))))
    :pattern ((ext_eq true (TYPE%vstd!seq.Seq. A&. A&) s1! s2!))
    :qid user_vstd__seq__axiom_seq_ext_equal_deep_4
    :skolemid skolem_user_vstd__seq__axiom_seq_ext_equal_deep_4
))))

;; Function-Axioms vstd::map::impl&%0::dom
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
    (has_type (vstd!map.impl&%0.dom.? K&. K& V&. V& self!) (TYPE%vstd!set.Set. K&. K&))
   )
   :pattern ((vstd!map.impl&%0.dom.? K&. K& V&. V& self!))
   :qid internal_vstd!map.impl&__0.dom.?_pre_post_definition
   :skolemid skolem_internal_vstd!map.impl&__0.dom.?_pre_post_definition
)))

;; Function-Specs vstd::map::impl&%0::index
(declare-fun req%vstd!map.impl&%0.index. (Dcr Type Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%2 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (= (req%vstd!map.impl&%0.index. K&. K& V&. V& self! key!) (=>
     %%global_location_label%%2
     (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& self!) key!)
   ))
   :pattern ((req%vstd!map.impl&%0.index. K&. K& V&. V& self! key!))
   :qid internal_req__vstd!map.impl&__0.index._definition
   :skolemid skolem_internal_req__vstd!map.impl&__0.index._definition
)))

;; Function-Axioms vstd::map::impl&%0::index
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
    )
    (has_type (vstd!map.impl&%0.index.? K&. K& V&. V& self! key!) V&)
   )
   :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& self! key!))
   :qid internal_vstd!map.impl&__0.index.?_pre_post_definition
   :skolemid skolem_internal_vstd!map.impl&__0.index.?_pre_post_definition
)))

;; Function-Specs vstd::map::impl&%0::spec_index
(declare-fun req%vstd!map.impl&%0.spec_index. (Dcr Type Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%3 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (= (req%vstd!map.impl&%0.spec_index. K&. K& V&. V& self! key!) (=>
     %%global_location_label%%3
     (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& self!) key!)
   ))
   :pattern ((req%vstd!map.impl&%0.spec_index. K&. K& V&. V& self! key!))
   :qid internal_req__vstd!map.impl&__0.spec_index._definition
   :skolemid skolem_internal_req__vstd!map.impl&__0.spec_index._definition
)))

;; Function-Axioms vstd::map::impl&%0::spec_index
(assert
 (fuel_bool_default fuel%vstd!map.impl&%0.spec_index.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!map.impl&%0.spec_index.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
    (= (vstd!map.impl&%0.spec_index.? K&. K& V&. V& self! key!) (vstd!map.impl&%0.index.?
      K&. K& V&. V& self! key!
    ))
    :pattern ((vstd!map.impl&%0.spec_index.? K&. K& V&. V& self! key!))
    :qid internal_vstd!map.impl&__0.spec_index.?_definition
    :skolemid skolem_internal_vstd!map.impl&__0.spec_index.?_definition
))))
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
    )
    (has_type (vstd!map.impl&%0.spec_index.? K&. K& V&. V& self! key!) V&)
   )
   :pattern ((vstd!map.impl&%0.spec_index.? K&. K& V&. V& self! key!))
   :qid internal_vstd!map.impl&__0.spec_index.?_pre_post_definition
   :skolemid skolem_internal_vstd!map.impl&__0.spec_index.?_pre_post_definition
)))

;; Broadcast vstd::map::axiom_map_index_decreases_finite
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_index_decreases_finite.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly)) (!
    (=>
     (and
      (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type key! K&)
     )
     (=>
      (and
       (and
        (and
         (sized K&.)
         (sized V&.)
        )
        (vstd!set.impl&%0.finite.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!))
       )
       (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
      )
      (height_lt (height (vstd!map.impl&%0.index.? K&. K& V&. V& m! key!)) (height m!))
    ))
    :pattern ((height (vstd!map.impl&%0.index.? K&. K& V&. V& m! key!)))
    :qid user_vstd__map__axiom_map_index_decreases_finite_5
    :skolemid skolem_user_vstd__map__axiom_map_index_decreases_finite_5
))))

;; Broadcast vstd::map::axiom_map_index_decreases_infinite
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_index_decreases_infinite.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly)) (!
    (=>
     (and
      (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type key! K&)
     )
     (=>
      (and
       (and
        (sized K&.)
        (sized V&.)
       )
       (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
      )
      (height_lt (height (vstd!map.impl&%0.index.? K&. K& V&. V& m! key!)) (height (fun_from_recursive_field
         m!
    )))))
    :pattern ((height (vstd!map.impl&%0.index.? K&. K& V&. V& m! key!)))
    :qid user_vstd__map__axiom_map_index_decreases_infinite_6
    :skolemid skolem_user_vstd__map__axiom_map_index_decreases_infinite_6
))))

;; Function-Axioms vstd::map::impl&%0::insert
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly) (value! Poly))
  (!
   (=>
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
     (has_type value! V&)
    )
    (has_type (vstd!map.impl&%0.insert.? K&. K& V&. V& self! key! value!) (TYPE%vstd!map.Map.
      K&. K& V&. V&
   )))
   :pattern ((vstd!map.impl&%0.insert.? K&. K& V&. V& self! key! value!))
   :qid internal_vstd!map.impl&__0.insert.?_pre_post_definition
   :skolemid skolem_internal_vstd!map.impl&__0.insert.?_pre_post_definition
)))

;; Function-Axioms vstd::set::Set::insert
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (has_type (vstd!set.Set.insert.? A&. A& self! a!) (TYPE%vstd!set.Set. A&. A&))
   )
   :pattern ((vstd!set.Set.insert.? A&. A& self! a!))
   :qid internal_vstd!set.Set.insert.?_pre_post_definition
   :skolemid skolem_internal_vstd!set.Set.insert.?_pre_post_definition
)))

;; Broadcast vstd::map::axiom_map_insert_domain
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_insert_domain.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly) (value! Poly))
   (!
    (=>
     (and
      (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type key! K&)
      (has_type value! V&)
     )
     (=>
      (and
       (sized K&.)
       (sized V&.)
      )
      (= (vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&. V& m!
         key! value!
        )
       ) (vstd!set.Set.insert.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
    )))
    :pattern ((vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&.
       V& m! key! value!
    )))
    :qid user_vstd__map__axiom_map_insert_domain_7
    :skolemid skolem_user_vstd__map__axiom_map_insert_domain_7
))))

;; Broadcast vstd::map::axiom_map_insert_same
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_insert_same.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly) (value! Poly))
   (!
    (=>
     (and
      (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type key! K&)
      (has_type value! V&)
     )
     (=>
      (and
       (sized K&.)
       (sized V&.)
      )
      (= (vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&. V&
         m! key! value!
        ) key!
       ) value!
    )))
    :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K&
       V&. V& m! key! value!
      ) key!
    ))
    :qid user_vstd__map__axiom_map_insert_same_8
    :skolemid skolem_user_vstd__map__axiom_map_insert_same_8
))))

;; Broadcast vstd::map::axiom_map_insert_different
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_insert_different.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key1! Poly) (key2! Poly)
    (value! Poly)
   ) (!
    (=>
     (and
      (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type key1! K&)
      (has_type key2! K&)
      (has_type value! V&)
     )
     (=>
      (and
       (and
        (sized K&.)
        (sized V&.)
       )
       (not (= key1! key2!))
      )
      (= (vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&. V&
         m! key2! value!
        ) key1!
       ) (vstd!map.impl&%0.index.? K&. K& V&. V& m! key1!)
    )))
    :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K&
       V&. V& m! key2! value!
      ) key1!
    ))
    :qid user_vstd__map__axiom_map_insert_different_9
    :skolemid skolem_user_vstd__map__axiom_map_insert_different_9
))))

;; Function-Axioms vstd::map::impl&%0::remove
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
    )
    (has_type (vstd!map.impl&%0.remove.? K&. K& V&. V& self! key!) (TYPE%vstd!map.Map.
      K&. K& V&. V&
   )))
   :pattern ((vstd!map.impl&%0.remove.? K&. K& V&. V& self! key!))
   :qid internal_vstd!map.impl&__0.remove.?_pre_post_definition
   :skolemid skolem_internal_vstd!map.impl&__0.remove.?_pre_post_definition
)))

;; Function-Axioms vstd::set::Set::remove
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (has_type (vstd!set.Set.remove.? A&. A& self! a!) (TYPE%vstd!set.Set. A&. A&))
   )
   :pattern ((vstd!set.Set.remove.? A&. A& self! a!))
   :qid internal_vstd!set.Set.remove.?_pre_post_definition
   :skolemid skolem_internal_vstd!set.Set.remove.?_pre_post_definition
)))

;; Broadcast vstd::map::axiom_map_remove_domain
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_remove_domain.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly)) (!
    (=>
     (and
      (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type key! K&)
     )
     (=>
      (and
       (sized K&.)
       (sized V&.)
      )
      (= (vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!map.impl&%0.remove.? K&. K& V&. V& m!
         key!
        )
       ) (vstd!set.Set.remove.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
    )))
    :pattern ((vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!map.impl&%0.remove.? K&. K& V&.
       V& m! key!
    )))
    :qid user_vstd__map__axiom_map_remove_domain_10
    :skolemid skolem_user_vstd__map__axiom_map_remove_domain_10
))))

;; Broadcast vstd::map::axiom_map_remove_different
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_remove_different.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key1! Poly) (key2! Poly))
   (!
    (=>
     (and
      (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type key1! K&)
      (has_type key2! K&)
     )
     (=>
      (and
       (and
        (sized K&.)
        (sized V&.)
       )
       (not (= key1! key2!))
      )
      (= (vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.remove.? K&. K& V&. V&
         m! key2!
        ) key1!
       ) (vstd!map.impl&%0.index.? K&. K& V&. V& m! key1!)
    )))
    :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.remove.? K&. K&
       V&. V& m! key2!
      ) key1!
    ))
    :qid user_vstd__map__axiom_map_remove_different_11
    :skolemid skolem_user_vstd__map__axiom_map_remove_different_11
))))

;; Broadcast vstd::map::axiom_map_ext_equal
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_ext_equal.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m1! Poly) (m2! Poly)) (!
    (=>
     (and
      (has_type m1! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type m2! (TYPE%vstd!map.Map. K&. K& V&. V&))
     )
     (=>
      (and
       (sized K&.)
       (sized V&.)
      )
      (= (ext_eq false (TYPE%vstd!map.Map. K&. K& V&. V&) m1! m2!) (and
        (ext_eq false (TYPE%vstd!set.Set. K&. K&) (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!)
         (vstd!map.impl&%0.dom.? K&. K& V&. V& m2!)
        )
        (forall ((k$ Poly)) (!
          (=>
           (has_type k$ K&)
           (=>
            (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!) k$)
            (= (vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$) (vstd!map.impl&%0.index.? K&. K&
              V&. V& m2! k$
          ))))
          :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$))
          :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m2! k$))
          :qid user_vstd__map__axiom_map_ext_equal_12
          :skolemid skolem_user_vstd__map__axiom_map_ext_equal_12
    ))))))
    :pattern ((ext_eq false (TYPE%vstd!map.Map. K&. K& V&. V&) m1! m2!))
    :qid user_vstd__map__axiom_map_ext_equal_13
    :skolemid skolem_user_vstd__map__axiom_map_ext_equal_13
))))

;; Broadcast vstd::map::axiom_map_ext_equal_deep
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_ext_equal_deep.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m1! Poly) (m2! Poly)) (!
    (=>
     (and
      (has_type m1! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type m2! (TYPE%vstd!map.Map. K&. K& V&. V&))
     )
     (=>
      (and
       (sized K&.)
       (sized V&.)
      )
      (= (ext_eq true (TYPE%vstd!map.Map. K&. K& V&. V&) m1! m2!) (and
        (ext_eq true (TYPE%vstd!set.Set. K&. K&) (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!)
         (vstd!map.impl&%0.dom.? K&. K& V&. V& m2!)
        )
        (forall ((k$ Poly)) (!
          (=>
           (has_type k$ K&)
           (=>
            (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!) k$)
            (ext_eq true V& (vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$) (vstd!map.impl&%0.index.?
              K&. K& V&. V& m2! k$
          ))))
          :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$))
          :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m2! k$))
          :qid user_vstd__map__axiom_map_ext_equal_deep_14
          :skolemid skolem_user_vstd__map__axiom_map_ext_equal_deep_14
    ))))))
    :pattern ((ext_eq true (TYPE%vstd!map.Map. K&. K& V&. V&) m1! m2!))
    :qid user_vstd__map__axiom_map_ext_equal_deep_15
    :skolemid skolem_user_vstd__map__axiom_map_ext_equal_deep_15
))))

;; Broadcast vstd::set::axiom_set_insert_same
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_insert_same.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (sized A&.)
      (vstd!set.Set.contains.? A&. A& (vstd!set.Set.insert.? A&. A& s! a!) a!)
    ))
    :pattern ((vstd!set.Set.contains.? A&. A& (vstd!set.Set.insert.? A&. A& s! a!) a!))
    :qid user_vstd__set__axiom_set_insert_same_16
    :skolemid skolem_user_vstd__set__axiom_set_insert_same_16
))))

;; Broadcast vstd::set::axiom_set_insert_different
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_insert_different.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a1! Poly) (a2! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a1! A&)
      (has_type a2! A&)
     )
     (=>
      (and
       (sized A&.)
       (not (= a1! a2!))
      )
      (= (vstd!set.Set.contains.? A&. A& (vstd!set.Set.insert.? A&. A& s! a2!) a1!) (vstd!set.Set.contains.?
        A&. A& s! a1!
    ))))
    :pattern ((vstd!set.Set.contains.? A&. A& (vstd!set.Set.insert.? A&. A& s! a2!) a1!))
    :qid user_vstd__set__axiom_set_insert_different_17
    :skolemid skolem_user_vstd__set__axiom_set_insert_different_17
))))

;; Broadcast vstd::set::axiom_set_remove_same
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_remove_same.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (sized A&.)
      (not (vstd!set.Set.contains.? A&. A& (vstd!set.Set.remove.? A&. A& s! a!) a!))
    ))
    :pattern ((vstd!set.Set.contains.? A&. A& (vstd!set.Set.remove.? A&. A& s! a!) a!))
    :qid user_vstd__set__axiom_set_remove_same_18
    :skolemid skolem_user_vstd__set__axiom_set_remove_same_18
))))

;; Broadcast vstd::set::axiom_set_remove_insert
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_remove_insert.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (and
       (sized A&.)
       (vstd!set.Set.contains.? A&. A& s! a!)
      )
      (= (vstd!set.Set.insert.? A&. A& (vstd!set.Set.remove.? A&. A& s! a!) a!) s!)
    ))
    :pattern ((vstd!set.Set.remove.? A&. A& s! a!))
    :qid user_vstd__set__axiom_set_remove_insert_19
    :skolemid skolem_user_vstd__set__axiom_set_remove_insert_19
))))

;; Broadcast vstd::set::axiom_set_remove_different
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_remove_different.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a1! Poly) (a2! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a1! A&)
      (has_type a2! A&)
     )
     (=>
      (and
       (sized A&.)
       (not (= a1! a2!))
      )
      (= (vstd!set.Set.contains.? A&. A& (vstd!set.Set.remove.? A&. A& s! a2!) a1!) (vstd!set.Set.contains.?
        A&. A& s! a1!
    ))))
    :pattern ((vstd!set.Set.contains.? A&. A& (vstd!set.Set.remove.? A&. A& s! a2!) a1!))
    :qid user_vstd__set__axiom_set_remove_different_20
    :skolemid skolem_user_vstd__set__axiom_set_remove_different_20
))))

;; Broadcast vstd::set::axiom_set_ext_equal
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_ext_equal.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!set.Set. A&. A&))
      (has_type s2! (TYPE%vstd!set.Set. A&. A&))
     )
     (=>
      (sized A&.)
      (= (ext_eq false (TYPE%vstd!set.Set. A&. A&) s1! s2!) (forall ((a$ Poly)) (!
         (=>
          (has_type a$ A&)
          (= (vstd!set.Set.contains.? A&. A& s1! a$) (vstd!set.Set.contains.? A&. A& s2! a$))
         )
         :pattern ((vstd!set.Set.contains.? A&. A& s1! a$))
         :pattern ((vstd!set.Set.contains.? A&. A& s2! a$))
         :qid user_vstd__set__axiom_set_ext_equal_21
         :skolemid skolem_user_vstd__set__axiom_set_ext_equal_21
    )))))
    :pattern ((ext_eq false (TYPE%vstd!set.Set. A&. A&) s1! s2!))
    :qid user_vstd__set__axiom_set_ext_equal_22
    :skolemid skolem_user_vstd__set__axiom_set_ext_equal_22
))))

;; Broadcast vstd::set::axiom_set_ext_equal_deep
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_ext_equal_deep.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!set.Set. A&. A&))
      (has_type s2! (TYPE%vstd!set.Set. A&. A&))
     )
     (=>
      (sized A&.)
      (= (ext_eq true (TYPE%vstd!set.Set. A&. A&) s1! s2!) (ext_eq false (TYPE%vstd!set.Set.
         A&. A&
        ) s1! s2!
    ))))
    :pattern ((ext_eq true (TYPE%vstd!set.Set. A&. A&) s1! s2!))
    :qid user_vstd__set__axiom_set_ext_equal_deep_23
    :skolemid skolem_user_vstd__set__axiom_set_ext_equal_deep_23
))))

;; Broadcast vstd::set::axiom_set_insert_finite
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_insert_finite.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (and
       (sized A&.)
       (vstd!set.impl&%0.finite.? A&. A& s!)
      )
      (vstd!set.impl&%0.finite.? A&. A& (vstd!set.Set.insert.? A&. A& s! a!))
    ))
    :pattern ((vstd!set.impl&%0.finite.? A&. A& (vstd!set.Set.insert.? A&. A& s! a!)))
    :qid user_vstd__set__axiom_set_insert_finite_24
    :skolemid skolem_user_vstd__set__axiom_set_insert_finite_24
))))

;; Broadcast vstd::set::axiom_set_remove_finite
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_remove_finite.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (and
       (sized A&.)
       (vstd!set.impl&%0.finite.? A&. A& s!)
      )
      (vstd!set.impl&%0.finite.? A&. A& (vstd!set.Set.remove.? A&. A& s! a!))
    ))
    :pattern ((vstd!set.impl&%0.finite.? A&. A& (vstd!set.Set.remove.? A&. A& s! a!)))
    :qid user_vstd__set__axiom_set_remove_finite_25
    :skolemid skolem_user_vstd__set__axiom_set_remove_finite_25
))))

;; Function-Axioms vstd::cell::impl&%2::mem_contents
(assert
 (forall ((V&. Dcr) (V& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!cell.PointsTo. V&. V&))
    (has_type (Poly%vstd!raw_ptr.MemContents. (vstd!cell.impl&%2.mem_contents.? V&. V& self!))
     (TYPE%vstd!raw_ptr.MemContents. V&. V&)
   ))
   :pattern ((vstd!cell.impl&%2.mem_contents.? V&. V& self!))
   :qid internal_vstd!cell.impl&__2.mem_contents.?_pre_post_definition
   :skolemid skolem_internal_vstd!cell.impl&__2.mem_contents.?_pre_post_definition
)))

;; Function-Axioms vstd::raw_ptr::impl&%6::is_init
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%6.is_init.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%6.is_init.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!raw_ptr.impl&%6.is_init.? T&. T& self!) (is-vstd!raw_ptr.MemContents./Init
      (%Poly%vstd!raw_ptr.MemContents. self!)
    ))
    :pattern ((vstd!raw_ptr.impl&%6.is_init.? T&. T& self!))
    :qid internal_vstd!raw_ptr.impl&__6.is_init.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.impl&__6.is_init.?_definition
))))

;; Function-Axioms vstd::cell::impl&%2::is_init
(assert
 (fuel_bool_default fuel%vstd!cell.impl&%2.is_init.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!cell.impl&%2.is_init.)
  (forall ((V&. Dcr) (V& Type) (self! Poly)) (!
    (= (vstd!cell.impl&%2.is_init.? V&. V& self!) (is-vstd!raw_ptr.MemContents./Init (vstd!cell.impl&%2.mem_contents.?
       V&. V& self!
    )))
    :pattern ((vstd!cell.impl&%2.is_init.? V&. V& self!))
    :qid internal_vstd!cell.impl&__2.is_init.?_definition
    :skolemid skolem_internal_vstd!cell.impl&__2.is_init.?_definition
))))

;; Function-Axioms producer_comsumer_example::ProducerState::arrow_Idle_0
(assert
 (fuel_bool_default fuel%producer_comsumer_example!impl&%0.arrow_Idle_0.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!impl&%0.arrow_Idle_0.)
  (forall ((self! Poly)) (!
    (= (producer_comsumer_example!impl&%0.arrow_Idle_0.? self!) (producer_comsumer_example!ProducerState./Idle/0
      (%Poly%producer_comsumer_example!ProducerState. self!)
    ))
    :pattern ((producer_comsumer_example!impl&%0.arrow_Idle_0.? self!))
    :qid internal_producer_comsumer_example!impl&__0.arrow_Idle_0.?_definition
    :skolemid skolem_internal_producer_comsumer_example!impl&__0.arrow_Idle_0.?_definition
))))
(assert
 (forall ((self! Poly)) (!
   (=>
    (has_type self! TYPE%producer_comsumer_example!ProducerState.)
    (<= 0 (producer_comsumer_example!impl&%0.arrow_Idle_0.? self!))
   )
   :pattern ((producer_comsumer_example!impl&%0.arrow_Idle_0.? self!))
   :qid internal_producer_comsumer_example!impl&__0.arrow_Idle_0.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!impl&__0.arrow_Idle_0.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::inc_wrap
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.)
  (forall ((T&. Dcr) (T& Type) (i! Poly) (len! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& i! len!) (ite
      (= (nClip (Add (%I i!) 1)) (%I len!))
      0
      (nClip (Add (%I i!) 1))
    ))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& i! len!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.inc_wrap.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.inc_wrap.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (i! Poly) (len! Poly)) (!
   (=>
    (and
     (has_type i! NAT)
     (has_type len! NAT)
    )
    (<= 0 (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& i! len!))
   )
   :pattern ((producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& i! len!))
   :qid internal_producer_comsumer_example!FifoQueue.impl&__19.inc_wrap.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.inc_wrap.?_pre_post_definition
)))

;; Function-Axioms vstd::raw_ptr::impl&%6::is_uninit
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%6.is_uninit.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%6.is_uninit.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!raw_ptr.impl&%6.is_uninit.? T&. T& self!) (is-vstd!raw_ptr.MemContents./Uninit
      (%Poly%vstd!raw_ptr.MemContents. self!)
    ))
    :pattern ((vstd!raw_ptr.impl&%6.is_uninit.? T&. T& self!))
    :qid internal_vstd!raw_ptr.impl&__6.is_uninit.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.impl&__6.is_uninit.?_definition
))))

;; Function-Axioms vstd::cell::impl&%2::is_uninit
(assert
 (fuel_bool_default fuel%vstd!cell.impl&%2.is_uninit.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!cell.impl&%2.is_uninit.)
  (forall ((V&. Dcr) (V& Type) (self! Poly)) (!
    (= (vstd!cell.impl&%2.is_uninit.? V&. V& self!) (is-vstd!raw_ptr.MemContents./Uninit
      (vstd!cell.impl&%2.mem_contents.? V&. V& self!)
    ))
    :pattern ((vstd!cell.impl&%2.is_uninit.? V&. V& self!))
    :qid internal_vstd!cell.impl&__2.is_uninit.?_definition
    :skolemid skolem_internal_vstd!cell.impl&__2.is_uninit.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::produce_start
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_start.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_start.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly) (post! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.produce_start.? T&. T& pre! post!)
     (let
      ((tmp_assert$ true))
      (let
       ((update_tmp_backing_cells$ (producer_comsumer_example!FifoQueue.State./State/backing_cells
          (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
       )))
       (let
        ((update_tmp_storage$ (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
            pre!
        ))))
        (let
         ((update_tmp_head$ (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
             pre!
         ))))
         (let
          ((update_tmp_tail$ (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
              pre!
          ))))
          (let
           ((update_tmp_consumer$ (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
               pre!
           ))))
           (and
            (is-producer_comsumer_example!ProducerState./Idle (producer_comsumer_example!FifoQueue.State./State/producer
              (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
            ))
            (and
             (let
              ((tail$ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
                  (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!FifoQueue.State./State/producer
                    (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
              ))))))
              (let
               ((head$ (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                   pre!
               ))))
               (let
                ((tmp_assert$1 (and
                   tmp_assert$
                   (and
                    (<= 0 tail$)
                    (< tail$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                       (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                         pre!
                )))))))))
                (let
                 ((next_tail$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$)
                    (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                       (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                         pre!
                 ))))))))
                 (and
                  (=>
                   tmp_assert$1
                   (not (= next_tail$ head$))
                  )
                  (let
                   ((update_tmp_producer$ (producer_comsumer_example!ProducerState./Producing (%I (I tail$)))))
                   (let
                    ((tmp_assert$2 (and
                       tmp_assert$1
                       (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                          T&. T&
                         ) update_tmp_storage$
                        ) (I tail$)
                    ))))
                    (and
                     (let
                      ((perm$ (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) update_tmp_storage$
                         (I tail$)
                      )))
                      (let
                       ((update_tmp_storage$1 (vstd!map.impl&%0.remove.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&.
                           T&
                          ) update_tmp_storage$ (I tail$)
                       )))
                       (let
                        ((tmp_assert$3 (and
                           tmp_assert$2
                           (and
                            (= (vstd!cell.impl&%2.id.? T&. T& perm$) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                               $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                                 (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                                )
                               ) (I tail$)
                            )))
                            (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& perm$))
                        ))))
                        (=>
                         tmp_assert$3
                         (= (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
                            post!
                           )
                          ) update_tmp_storage$1
                     )))))
                     (let
                      ((tmp_assert$4 (let
                         ((perm$ (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) update_tmp_storage$
                            (I tail$)
                         )))
                         (let
                          ((update_tmp_storage$2 (vstd!map.impl&%0.remove.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&.
                              T&
                             ) update_tmp_storage$ (I tail$)
                          )))
                          (let
                           ((tmp_assert$5 (and
                              tmp_assert$2
                              (and
                               (= (vstd!cell.impl&%2.id.? T&. T& perm$) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                                  $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                                    (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                                   )
                                  ) (I tail$)
                               )))
                               (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& perm$))
                           ))))
                           tmp_assert$5
                      )))))
                      (=>
                       tmp_assert$4
                       (= (producer_comsumer_example!FifoQueue.State./State/producer (%Poly%producer_comsumer_example!FifoQueue.State.
                          post!
                         )
                        ) update_tmp_producer$
             )))))))))))
             (let
              ((tmp_assert$6 (let
                 ((tail$ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
                     (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!FifoQueue.State./State/producer
                       (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                 ))))))
                 (let
                  ((tmp_assert$7 (let
                     ((head$ (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                         pre!
                     ))))
                     (let
                      ((tmp_assert$8 (and
                         tmp_assert$
                         (and
                          (<= 0 tail$)
                          (< tail$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                             (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                               pre!
                      )))))))))
                      (let
                       ((tmp_assert$9 (let
                          ((next_tail$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$)
                             (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                                (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                                  pre!
                          ))))))))
                          (let
                           ((update_tmp_producer$ (producer_comsumer_example!ProducerState./Producing (%I (I tail$)))))
                           (let
                            ((tmp_assert$10 (and
                               tmp_assert$8
                               (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                                  T&. T&
                                 ) update_tmp_storage$
                                ) (I tail$)
                            ))))
                            (let
                             ((tmp_assert$11 (let
                                ((perm$ (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) update_tmp_storage$
                                   (I tail$)
                                )))
                                (let
                                 ((update_tmp_storage$3 (vstd!map.impl&%0.remove.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&.
                                     T&
                                    ) update_tmp_storage$ (I tail$)
                                 )))
                                 (let
                                  ((tmp_assert$12 (and
                                     tmp_assert$10
                                     (and
                                      (= (vstd!cell.impl&%2.id.? T&. T& perm$) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                                         $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                                           (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                                          )
                                         ) (I tail$)
                                      )))
                                      (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& perm$))
                                  ))))
                                  tmp_assert$12
                             )))))
                             tmp_assert$11
                       ))))))
                       tmp_assert$9
                  )))))
                  tmp_assert$7
              ))))
              (and
               (=>
                tmp_assert$6
                (= (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
                   post!
                  )
                 ) update_tmp_consumer$
               ))
               (and
                (=>
                 tmp_assert$6
                 (= (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
                    post!
                   )
                  ) update_tmp_tail$
                ))
                (and
                 (=>
                  tmp_assert$6
                  (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                     post!
                    )
                   ) update_tmp_head$
                 ))
                 (=>
                  tmp_assert$6
                  (= (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                     post!
                    )
                   ) update_tmp_backing_cells$
    )))))))))))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.produce_start.? T&. T& pre!
      post!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.produce_start.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.produce_start.?_definition
))))

;; Function-Axioms producer_comsumer_example::ProducerState::arrow_Producing_0
(assert
 (fuel_bool_default fuel%producer_comsumer_example!impl&%0.arrow_Producing_0.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!impl&%0.arrow_Producing_0.)
  (forall ((self! Poly)) (!
    (= (producer_comsumer_example!impl&%0.arrow_Producing_0.? self!) (producer_comsumer_example!ProducerState./Producing/0
      (%Poly%producer_comsumer_example!ProducerState. self!)
    ))
    :pattern ((producer_comsumer_example!impl&%0.arrow_Producing_0.? self!))
    :qid internal_producer_comsumer_example!impl&__0.arrow_Producing_0.?_definition
    :skolemid skolem_internal_producer_comsumer_example!impl&__0.arrow_Producing_0.?_definition
))))
(assert
 (forall ((self! Poly)) (!
   (=>
    (has_type self! TYPE%producer_comsumer_example!ProducerState.)
    (<= 0 (producer_comsumer_example!impl&%0.arrow_Producing_0.? self!))
   )
   :pattern ((producer_comsumer_example!impl&%0.arrow_Producing_0.? self!))
   :qid internal_producer_comsumer_example!impl&__0.arrow_Producing_0.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!impl&__0.arrow_Producing_0.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::produce_end
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_end.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_end.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly) (post! Poly) (perm! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.produce_end.? T&. T& pre! post! perm!)
     (let
      ((tmp_assert$ true))
      (let
       ((update_tmp_backing_cells$ (producer_comsumer_example!FifoQueue.State./State/backing_cells
          (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
       )))
       (let
        ((update_tmp_storage$ (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
            pre!
        ))))
        (let
         ((update_tmp_head$ (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
             pre!
         ))))
         (let
          ((update_tmp_consumer$ (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
              pre!
          ))))
          (and
           (is-producer_comsumer_example!ProducerState./Producing (producer_comsumer_example!FifoQueue.State./State/producer
             (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
           ))
           (and
            (let
             ((tail$ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
                 (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!FifoQueue.State./State/producer
                   (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
             ))))))
             (let
              ((tmp_assert$1 (and
                 tmp_assert$
                 (and
                  (<= 0 tail$)
                  (< tail$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                     (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                       pre!
              )))))))))
              (let
               ((next_tail$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$)
                  (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                     (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                       pre!
               ))))))))
               (and
                (=>
                 tmp_assert$1
                 (and
                  (= (vstd!cell.impl&%2.id.? T&. T& perm!) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                     $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                       (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                      )
                     ) (I tail$)
                  )))
                  (is-vstd!raw_ptr.MemContents./Init (vstd!cell.impl&%2.mem_contents.? T&. T& perm!))
                ))
                (let
                 ((update_tmp_producer$ (producer_comsumer_example!ProducerState./Idle (%I (I next_tail$)))))
                 (let
                  ((update_tmp_tail$ next_tail$))
                  (let
                   ((tmp_assert$2 (and
                      tmp_assert$1
                      (not (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                          T&. T&
                         ) update_tmp_storage$
                        ) (I tail$)
                   )))))
                   (let
                    ((update_tmp_storage$1 (vstd!map.impl&%0.insert.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&.
                        T&
                       ) update_tmp_storage$ (I tail$) perm!
                    )))
                    (and
                     (=>
                      tmp_assert$2
                      (= (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
                         post!
                        )
                       ) update_tmp_storage$1
                     ))
                     (and
                      (=>
                       tmp_assert$2
                       (= (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
                          post!
                         )
                        ) update_tmp_tail$
                      ))
                      (=>
                       tmp_assert$2
                       (= (producer_comsumer_example!FifoQueue.State./State/producer (%Poly%producer_comsumer_example!FifoQueue.State.
                          post!
                         )
                        ) update_tmp_producer$
            ))))))))))))
            (let
             ((tmp_assert$3 (let
                ((tail$ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
                    (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!FifoQueue.State./State/producer
                      (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                ))))))
                (let
                 ((tmp_assert$4 (and
                    tmp_assert$
                    (and
                     (<= 0 tail$)
                     (< tail$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                        (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                          pre!
                 )))))))))
                 (let
                  ((tmp_assert$5 (let
                     ((next_tail$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$)
                        (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                           (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                             pre!
                     ))))))))
                     (let
                      ((update_tmp_producer$ (producer_comsumer_example!ProducerState./Idle (%I (I next_tail$)))))
                      (let
                       ((update_tmp_tail$ next_tail$))
                       (let
                        ((tmp_assert$6 (and
                           tmp_assert$4
                           (not (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                               T&. T&
                              ) update_tmp_storage$
                             ) (I tail$)
                        )))))
                        (let
                         ((update_tmp_storage$2 (vstd!map.impl&%0.insert.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&.
                             T&
                            ) update_tmp_storage$ (I tail$) perm!
                         )))
                         tmp_assert$6
                  )))))))
                  tmp_assert$5
             )))))
             (and
              (=>
               tmp_assert$3
               (= (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
                  post!
                 )
                ) update_tmp_consumer$
              ))
              (and
               (=>
                tmp_assert$3
                (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                   post!
                  )
                 ) update_tmp_head$
               ))
               (=>
                tmp_assert$3
                (= (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                   post!
                  )
                 ) update_tmp_backing_cells$
    )))))))))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.produce_end.? T&. T& pre! post!
      perm!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.produce_end.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.produce_end.?_definition
))))

;; Function-Axioms producer_comsumer_example::ConsumerState::arrow_Idle_0
(assert
 (fuel_bool_default fuel%producer_comsumer_example!impl&%1.arrow_Idle_0.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!impl&%1.arrow_Idle_0.)
  (forall ((self! Poly)) (!
    (= (producer_comsumer_example!impl&%1.arrow_Idle_0.? self!) (producer_comsumer_example!ConsumerState./Idle/0
      (%Poly%producer_comsumer_example!ConsumerState. self!)
    ))
    :pattern ((producer_comsumer_example!impl&%1.arrow_Idle_0.? self!))
    :qid internal_producer_comsumer_example!impl&__1.arrow_Idle_0.?_definition
    :skolemid skolem_internal_producer_comsumer_example!impl&__1.arrow_Idle_0.?_definition
))))
(assert
 (forall ((self! Poly)) (!
   (=>
    (has_type self! TYPE%producer_comsumer_example!ConsumerState.)
    (<= 0 (producer_comsumer_example!impl&%1.arrow_Idle_0.? self!))
   )
   :pattern ((producer_comsumer_example!impl&%1.arrow_Idle_0.? self!))
   :qid internal_producer_comsumer_example!impl&__1.arrow_Idle_0.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!impl&__1.arrow_Idle_0.?_pre_post_definition
)))

;; Function-Axioms vstd::map_lib::impl&%0::contains_pair
(assert
 (fuel_bool_default fuel%vstd!map_lib.impl&%0.contains_pair.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!map_lib.impl&%0.contains_pair.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (k! Poly) (v! Poly))
   (!
    (= (vstd!map_lib.impl&%0.contains_pair.? K&. K& V&. V& self! k! v!) (and
      (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& self!) k!)
      (= (vstd!map.impl&%0.index.? K&. K& V&. V& self! k!) v!)
    ))
    :pattern ((vstd!map_lib.impl&%0.contains_pair.? K&. K& V&. V& self! k! v!))
    :qid internal_vstd!map_lib.impl&__0.contains_pair.?_definition
    :skolemid skolem_internal_vstd!map_lib.impl&__0.contains_pair.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::consume_start
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_start.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_start.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly) (post! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.consume_start.? T&. T& pre! post!)
     (let
      ((tmp_assert$ true))
      (let
       ((update_tmp_backing_cells$ (producer_comsumer_example!FifoQueue.State./State/backing_cells
          (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
       )))
       (let
        ((update_tmp_storage$ (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
            pre!
        ))))
        (let
         ((update_tmp_head$ (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
             pre!
         ))))
         (let
          ((update_tmp_tail$ (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
              pre!
          ))))
          (let
           ((update_tmp_producer$ (producer_comsumer_example!FifoQueue.State./State/producer (%Poly%producer_comsumer_example!FifoQueue.State.
               pre!
           ))))
           (and
            (is-producer_comsumer_example!ConsumerState./Idle (producer_comsumer_example!FifoQueue.State./State/consumer
              (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
            ))
            (and
             (let
              ((head$ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
                  (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!FifoQueue.State./State/consumer
                    (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
              ))))))
              (let
               ((tail$ (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
                   pre!
               ))))
               (let
                ((tmp_assert$1 (and
                   tmp_assert$
                   (and
                    (<= 0 head$)
                    (< head$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                       (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                         pre!
                )))))))))
                (and
                 (=>
                  tmp_assert$1
                  (not (= head$ tail$))
                 )
                 (let
                  ((update_tmp_consumer$ (producer_comsumer_example!ConsumerState./Consuming (%I (I head$)))))
                  (and
                   (let
                    ((perm$ (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) (producer_comsumer_example!FifoQueue.State./State/storage
                        (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                       ) (I head$)
                    )))
                    (let
                     ((tmp_assert$2 (and
                        tmp_assert$1
                        (vstd!map_lib.impl&%0.contains_pair.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) update_tmp_storage$
                         (I head$) perm$
                     ))))
                     (let
                      ((update_tmp_storage$1 (vstd!map.impl&%0.remove.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&.
                          T&
                         ) update_tmp_storage$ (I head$)
                      )))
                      (let
                       ((tmp_assert$3 (and
                          tmp_assert$2
                          (= (vstd!cell.impl&%2.id.? T&. T& perm$) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                             $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                               (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                              )
                             ) (I head$)
                       ))))))
                       (let
                        ((tmp_assert$4 (and
                           tmp_assert$3
                           (is-vstd!raw_ptr.MemContents./Init (vstd!cell.impl&%2.mem_contents.? T&. T& perm$))
                        )))
                        (=>
                         tmp_assert$4
                         (= (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
                            post!
                           )
                          ) update_tmp_storage$1
                   )))))))
                   (let
                    ((tmp_assert$5 (let
                       ((perm$ (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) (producer_comsumer_example!FifoQueue.State./State/storage
                           (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                          ) (I head$)
                       )))
                       (let
                        ((tmp_assert$6 (and
                           tmp_assert$1
                           (vstd!map_lib.impl&%0.contains_pair.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) update_tmp_storage$
                            (I head$) perm$
                        ))))
                        (let
                         ((update_tmp_storage$2 (vstd!map.impl&%0.remove.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&.
                             T&
                            ) update_tmp_storage$ (I head$)
                         )))
                         (let
                          ((tmp_assert$7 (and
                             tmp_assert$6
                             (= (vstd!cell.impl&%2.id.? T&. T& perm$) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                                $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                                  (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                                 )
                                ) (I head$)
                          ))))))
                          (let
                           ((tmp_assert$8 (and
                              tmp_assert$7
                              (is-vstd!raw_ptr.MemContents./Init (vstd!cell.impl&%2.mem_contents.? T&. T& perm$))
                           )))
                           tmp_assert$8
                    )))))))
                    (=>
                     tmp_assert$5
                     (= (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
                        post!
                       )
                      ) update_tmp_consumer$
             )))))))))
             (let
              ((tmp_assert$9 (let
                 ((head$ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
                     (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!FifoQueue.State./State/consumer
                       (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                 ))))))
                 (let
                  ((tmp_assert$10 (let
                     ((tail$ (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
                         pre!
                     ))))
                     (let
                      ((tmp_assert$11 (and
                         tmp_assert$
                         (and
                          (<= 0 head$)
                          (< head$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                             (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                               pre!
                      )))))))))
                      (let
                       ((update_tmp_consumer$ (producer_comsumer_example!ConsumerState./Consuming (%I (I head$)))))
                       (let
                        ((tmp_assert$12 (let
                           ((perm$ (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) (producer_comsumer_example!FifoQueue.State./State/storage
                               (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                              ) (I head$)
                           )))
                           (let
                            ((tmp_assert$13 (and
                               tmp_assert$11
                               (vstd!map_lib.impl&%0.contains_pair.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) update_tmp_storage$
                                (I head$) perm$
                            ))))
                            (let
                             ((update_tmp_storage$3 (vstd!map.impl&%0.remove.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&.
                                 T&
                                ) update_tmp_storage$ (I head$)
                             )))
                             (let
                              ((tmp_assert$14 (and
                                 tmp_assert$13
                                 (= (vstd!cell.impl&%2.id.? T&. T& perm$) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                                    $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                                      (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                                     )
                                    ) (I head$)
                              ))))))
                              (let
                               ((tmp_assert$15 (and
                                  tmp_assert$14
                                  (is-vstd!raw_ptr.MemContents./Init (vstd!cell.impl&%2.mem_contents.? T&. T& perm$))
                               )))
                               tmp_assert$15
                        )))))))
                        tmp_assert$12
                  ))))))
                  tmp_assert$10
              ))))
              (and
               (=>
                tmp_assert$9
                (= (producer_comsumer_example!FifoQueue.State./State/producer (%Poly%producer_comsumer_example!FifoQueue.State.
                   post!
                  )
                 ) update_tmp_producer$
               ))
               (and
                (=>
                 tmp_assert$9
                 (= (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
                    post!
                   )
                  ) update_tmp_tail$
                ))
                (and
                 (=>
                  tmp_assert$9
                  (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                     post!
                    )
                   ) update_tmp_head$
                 ))
                 (=>
                  tmp_assert$9
                  (= (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                     post!
                    )
                   ) update_tmp_backing_cells$
    )))))))))))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.consume_start.? T&. T& pre!
      post!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.consume_start.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.consume_start.?_definition
))))

;; Function-Axioms producer_comsumer_example::ConsumerState::arrow_Consuming_0
(assert
 (fuel_bool_default fuel%producer_comsumer_example!impl&%1.arrow_Consuming_0.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!impl&%1.arrow_Consuming_0.)
  (forall ((self! Poly)) (!
    (= (producer_comsumer_example!impl&%1.arrow_Consuming_0.? self!) (producer_comsumer_example!ConsumerState./Consuming/0
      (%Poly%producer_comsumer_example!ConsumerState. self!)
    ))
    :pattern ((producer_comsumer_example!impl&%1.arrow_Consuming_0.? self!))
    :qid internal_producer_comsumer_example!impl&__1.arrow_Consuming_0.?_definition
    :skolemid skolem_internal_producer_comsumer_example!impl&__1.arrow_Consuming_0.?_definition
))))
(assert
 (forall ((self! Poly)) (!
   (=>
    (has_type self! TYPE%producer_comsumer_example!ConsumerState.)
    (<= 0 (producer_comsumer_example!impl&%1.arrow_Consuming_0.? self!))
   )
   :pattern ((producer_comsumer_example!impl&%1.arrow_Consuming_0.? self!))
   :qid internal_producer_comsumer_example!impl&__1.arrow_Consuming_0.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!impl&__1.arrow_Consuming_0.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::consume_end
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_end.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_end.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly) (post! Poly) (perm! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.consume_end.? T&. T& pre! post! perm!)
     (let
      ((tmp_assert$ true))
      (let
       ((update_tmp_backing_cells$ (producer_comsumer_example!FifoQueue.State./State/backing_cells
          (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
       )))
       (let
        ((update_tmp_storage$ (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
            pre!
        ))))
        (let
         ((update_tmp_tail$ (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
             pre!
         ))))
         (let
          ((update_tmp_producer$ (producer_comsumer_example!FifoQueue.State./State/producer (%Poly%producer_comsumer_example!FifoQueue.State.
              pre!
          ))))
          (and
           (is-producer_comsumer_example!ConsumerState./Consuming (producer_comsumer_example!FifoQueue.State./State/consumer
             (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
           ))
           (and
            (let
             ((head$ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
                 (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!FifoQueue.State./State/consumer
                   (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
             ))))))
             (let
              ((tmp_assert$1 (and
                 tmp_assert$
                 (and
                  (<= 0 head$)
                  (< head$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                     (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                       pre!
              )))))))))
              (let
               ((next_head$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I head$)
                  (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                     (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                       pre!
               ))))))))
               (let
                ((update_tmp_consumer$ (producer_comsumer_example!ConsumerState./Idle (%I (I next_head$)))))
                (let
                 ((update_tmp_head$ next_head$))
                 (and
                  (=>
                   tmp_assert$1
                   (and
                    (= (vstd!cell.impl&%2.id.? T&. T& perm!) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                       $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                         (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                        )
                       ) (I head$)
                    )))
                    (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& perm!))
                  ))
                  (let
                   ((tmp_assert$2 (and
                      tmp_assert$1
                      (not (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                          T&. T&
                         ) update_tmp_storage$
                        ) (I head$)
                   )))))
                   (let
                    ((update_tmp_storage$1 (vstd!map.impl&%0.insert.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&.
                        T&
                       ) update_tmp_storage$ (I head$) perm!
                    )))
                    (and
                     (=>
                      tmp_assert$2
                      (= (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
                         post!
                        )
                       ) update_tmp_storage$1
                     ))
                     (and
                      (=>
                       tmp_assert$2
                       (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                          post!
                         )
                        ) update_tmp_head$
                      ))
                      (=>
                       tmp_assert$2
                       (= (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
                          post!
                         )
                        ) update_tmp_consumer$
            ))))))))))))
            (let
             ((tmp_assert$3 (let
                ((head$ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
                    (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!FifoQueue.State./State/consumer
                      (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                ))))))
                (let
                 ((tmp_assert$4 (and
                    tmp_assert$
                    (and
                     (<= 0 head$)
                     (< head$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                        (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                          pre!
                 )))))))))
                 (let
                  ((tmp_assert$5 (let
                     ((next_head$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I head$)
                        (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                           (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                             pre!
                     ))))))))
                     (let
                      ((update_tmp_consumer$ (producer_comsumer_example!ConsumerState./Idle (%I (I next_head$)))))
                      (let
                       ((update_tmp_head$ next_head$))
                       (let
                        ((tmp_assert$6 (and
                           tmp_assert$4
                           (not (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                               T&. T&
                              ) update_tmp_storage$
                             ) (I head$)
                        )))))
                        (let
                         ((update_tmp_storage$2 (vstd!map.impl&%0.insert.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&.
                             T&
                            ) update_tmp_storage$ (I head$) perm!
                         )))
                         tmp_assert$6
                  )))))))
                  tmp_assert$5
             )))))
             (and
              (=>
               tmp_assert$3
               (= (producer_comsumer_example!FifoQueue.State./State/producer (%Poly%producer_comsumer_example!FifoQueue.State.
                  post!
                 )
                ) update_tmp_producer$
              ))
              (and
               (=>
                tmp_assert$3
                (= (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
                   post!
                  )
                 ) update_tmp_tail$
               ))
               (=>
                tmp_assert$3
                (= (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                   post!
                  )
                 ) update_tmp_backing_cells$
    )))))))))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.consume_end.? T&. T& pre! post!
      perm!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.consume_end.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.consume_end.?_definition
))))

;; Function-Specs producer_comsumer_example::FifoQueue::show::produce_start
(declare-fun req%producer_comsumer_example!FifoQueue.show.produce_start. (Dcr Type
  producer_comsumer_example!FifoQueue.State. producer_comsumer_example!FifoQueue.State.
 ) Bool
)
(declare-const %%global_location_label%%4 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   )
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.show.produce_start. T&. T& pre! post!)
    (=>
     %%global_location_label%%4
     (producer_comsumer_example!FifoQueue.impl&%19.produce_start.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
       pre!
      ) (Poly%producer_comsumer_example!FifoQueue.State. post!)
   )))
   :pattern ((req%producer_comsumer_example!FifoQueue.show.produce_start. T&. T& pre!
     post!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.show.produce_start._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.show.produce_start._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.show.produce_start. (Dcr Type
  producer_comsumer_example!FifoQueue.State. producer_comsumer_example!FifoQueue.State.
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   )
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.show.produce_start. T&. T& pre! post!)
    (producer_comsumer_example!FifoQueue.impl&%19.next.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      pre!
     ) (Poly%producer_comsumer_example!FifoQueue.State. post!)
   ))
   :pattern ((ens%producer_comsumer_example!FifoQueue.show.produce_start. T&. T& pre!
     post!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.show.produce_start._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.show.produce_start._definition
)))

;; Function-Specs producer_comsumer_example::FifoQueue::show::produce_end
(declare-fun req%producer_comsumer_example!FifoQueue.show.produce_end. (Dcr Type producer_comsumer_example!FifoQueue.State.
  producer_comsumer_example!FifoQueue.State. Poly
 ) Bool
)
(declare-const %%global_location_label%%5 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   ) (perm! Poly)
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.show.produce_end. T&. T& pre! post! perm!)
    (=>
     %%global_location_label%%5
     (producer_comsumer_example!FifoQueue.impl&%19.produce_end.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
       pre!
      ) (Poly%producer_comsumer_example!FifoQueue.State. post!) perm!
   )))
   :pattern ((req%producer_comsumer_example!FifoQueue.show.produce_end. T&. T& pre! post!
     perm!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.show.produce_end._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.show.produce_end._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.show.produce_end. (Dcr Type producer_comsumer_example!FifoQueue.State.
  producer_comsumer_example!FifoQueue.State. Poly
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   ) (perm! Poly)
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.show.produce_end. T&. T& pre! post! perm!)
    (producer_comsumer_example!FifoQueue.impl&%19.next.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      pre!
     ) (Poly%producer_comsumer_example!FifoQueue.State. post!)
   ))
   :pattern ((ens%producer_comsumer_example!FifoQueue.show.produce_end. T&. T& pre! post!
     perm!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.show.produce_end._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.show.produce_end._definition
)))

;; Function-Specs producer_comsumer_example::FifoQueue::show::consume_start
(declare-fun req%producer_comsumer_example!FifoQueue.show.consume_start. (Dcr Type
  producer_comsumer_example!FifoQueue.State. producer_comsumer_example!FifoQueue.State.
 ) Bool
)
(declare-const %%global_location_label%%6 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   )
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.show.consume_start. T&. T& pre! post!)
    (=>
     %%global_location_label%%6
     (producer_comsumer_example!FifoQueue.impl&%19.consume_start.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
       pre!
      ) (Poly%producer_comsumer_example!FifoQueue.State. post!)
   )))
   :pattern ((req%producer_comsumer_example!FifoQueue.show.consume_start. T&. T& pre!
     post!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.show.consume_start._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.show.consume_start._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.show.consume_start. (Dcr Type
  producer_comsumer_example!FifoQueue.State. producer_comsumer_example!FifoQueue.State.
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   )
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.show.consume_start. T&. T& pre! post!)
    (producer_comsumer_example!FifoQueue.impl&%19.next.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      pre!
     ) (Poly%producer_comsumer_example!FifoQueue.State. post!)
   ))
   :pattern ((ens%producer_comsumer_example!FifoQueue.show.consume_start. T&. T& pre!
     post!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.show.consume_start._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.show.consume_start._definition
)))

;; Function-Specs producer_comsumer_example::FifoQueue::show::consume_end
(declare-fun req%producer_comsumer_example!FifoQueue.show.consume_end. (Dcr Type producer_comsumer_example!FifoQueue.State.
  producer_comsumer_example!FifoQueue.State. Poly
 ) Bool
)
(declare-const %%global_location_label%%7 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   ) (perm! Poly)
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.show.consume_end. T&. T& pre! post! perm!)
    (=>
     %%global_location_label%%7
     (producer_comsumer_example!FifoQueue.impl&%19.consume_end.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
       pre!
      ) (Poly%producer_comsumer_example!FifoQueue.State. post!) perm!
   )))
   :pattern ((req%producer_comsumer_example!FifoQueue.show.consume_end. T&. T& pre! post!
     perm!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.show.consume_end._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.show.consume_end._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.show.consume_end. (Dcr Type producer_comsumer_example!FifoQueue.State.
  producer_comsumer_example!FifoQueue.State. Poly
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   ) (perm! Poly)
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.show.consume_end. T&. T& pre! post! perm!)
    (producer_comsumer_example!FifoQueue.impl&%19.next.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      pre!
     ) (Poly%producer_comsumer_example!FifoQueue.State. post!)
   ))
   :pattern ((ens%producer_comsumer_example!FifoQueue.show.consume_end. T&. T& pre! post!
     perm!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.show.consume_end._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.show.consume_end._definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::initialize
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.initialize.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.initialize.)
  (forall ((T&. Dcr) (T& Type) (post! Poly) (backing_cells! Poly) (storage! Poly)) (
    !
    (= (producer_comsumer_example!FifoQueue.impl&%19.initialize.? T&. T& post! backing_cells!
      storage!
     ) (and
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ NAT)
         (=>
          (and
           (<= 0 (%I i$))
           (< (%I i$) (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. backing_cells!))
          )
          (and
           (and
            (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
               T&. T&
              ) storage!
             ) i$
            )
            (= (vstd!cell.impl&%2.id.? T&. T& (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                T&. T&
               ) storage! i$
              )
             ) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.? $ TYPE%vstd!cell.CellId. backing_cells!
               i$
           ))))
           (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& (vstd!map.impl&%0.index.?
              $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) storage! i$
        ))))))
        :pattern ((vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
            T&. T&
           ) storage!
          ) i$
        ))
        :qid user_producer_comsumer_example__FifoQueue__State__initialize_26
        :skolemid skolem_user_producer_comsumer_example__FifoQueue__State__initialize_26
      ))
      (and
       (> (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. backing_cells!) 0)
       (let
        ((update_tmp_backing_cells$ (%Poly%vstd!seq.Seq<vstd!cell.CellId.>. backing_cells!)))
        (let
         ((update_tmp_storage$ storage!))
         (let
          ((update_tmp_head$ 0))
          (let
           ((update_tmp_tail$ 0))
           (let
            ((update_tmp_producer$ (producer_comsumer_example!ProducerState./Idle (%I (I 0)))))
            (let
             ((update_tmp_consumer$ (producer_comsumer_example!ConsumerState./Idle (%I (I 0)))))
             (and
              (= (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
                 post!
                )
               ) update_tmp_consumer$
              )
              (and
               (= (producer_comsumer_example!FifoQueue.State./State/producer (%Poly%producer_comsumer_example!FifoQueue.State.
                  post!
                 )
                ) update_tmp_producer$
               )
               (and
                (= (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
                   post!
                  )
                 ) update_tmp_tail$
                )
                (and
                 (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                    post!
                   )
                  ) update_tmp_head$
                 )
                 (and
                  (= (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
                     post!
                    )
                   ) update_tmp_storage$
                  )
                  (= (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                     post!
                    )
                   ) update_tmp_backing_cells$
    )))))))))))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.initialize.? T&. T& post! backing_cells!
      storage!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.initialize.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.initialize.?_definition
))))

;; Function-Specs producer_comsumer_example::FifoQueue::show::initialize
(declare-fun req%producer_comsumer_example!FifoQueue.show.initialize. (Dcr Type producer_comsumer_example!FifoQueue.State.
  vstd!seq.Seq<vstd!cell.CellId.>. Poly
 ) Bool
)
(declare-const %%global_location_label%%8 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (post! producer_comsumer_example!FifoQueue.State.) (backing_cells!
    vstd!seq.Seq<vstd!cell.CellId.>.
   ) (storage! Poly)
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.show.initialize. T&. T& post! backing_cells!
     storage!
    ) (=>
     %%global_location_label%%8
     (producer_comsumer_example!FifoQueue.impl&%19.initialize.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
       post!
      ) (Poly%vstd!seq.Seq<vstd!cell.CellId.>. backing_cells!) storage!
   )))
   :pattern ((req%producer_comsumer_example!FifoQueue.show.initialize. T&. T& post! backing_cells!
     storage!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.show.initialize._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.show.initialize._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.show.initialize. (Dcr Type producer_comsumer_example!FifoQueue.State.
  vstd!seq.Seq<vstd!cell.CellId.>. Poly
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (post! producer_comsumer_example!FifoQueue.State.) (backing_cells!
    vstd!seq.Seq<vstd!cell.CellId.>.
   ) (storage! Poly)
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.show.initialize. T&. T& post! backing_cells!
     storage!
    ) (producer_comsumer_example!FifoQueue.impl&%19.init.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      post!
   )))
   :pattern ((ens%producer_comsumer_example!FifoQueue.show.initialize. T&. T& post! backing_cells!
     storage!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.show.initialize._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.show.initialize._definition
)))
