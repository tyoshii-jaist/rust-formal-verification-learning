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

;; MODULE 'module FifoQueue'

;; Fuel
(declare-const fuel%vstd!std_specs.option.impl&%2.arrow_0. FuelId)
(declare-const fuel%vstd!std_specs.option.is_some. FuelId)
(declare-const fuel%vstd!std_specs.option.is_none. FuelId)
(declare-const fuel%vstd!std_specs.option.spec_unwrap. FuelId)
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
(declare-const fuel%vstd!pervasive.strictly_cloned. FuelId)
(declare-const fuel%vstd!pervasive.cloned. FuelId)
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
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%0.arrow_produce_end_0.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%0.arrow_consume_end_0.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%0.arrow_dummy_to_use_type_params_0.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%1.is_produce_start.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%1.is_produce_end. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%1.get_produce_end_0.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%1.is_consume_start.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%1.is_consume_end. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%1.get_consume_end_0.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%1.is_dummy_to_use_type_params.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%1.get_dummy_to_use_type_params_0.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_1. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_0.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_1.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_dummy_to_use_type_params_0.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%3.is_initialize. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%3.get_initialize_0.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%3.get_initialize_1.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%3.is_dummy_to_use_type_params.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%3.get_dummy_to_use_type_params_0.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.initialize. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.initialize_enabled.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_start. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_start_strong.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_start_enabled.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_end. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_end_strong.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_end_enabled.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_start. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_start_strong.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_start_enabled.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_end. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_end_strong.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_end_enabled.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.next_by. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.next. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.next_strong_by. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.next_strong. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.init_by. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.init. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.invariant. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.not_overlapping.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.in_bounds. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.valid_storage_all.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.len. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.inc_wrap. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.in_active_range.
 FuelId
)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.is_checked_out. FuelId)
(declare-const fuel%producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.
 FuelId
)
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
 (distinct fuel%vstd!std_specs.option.impl&%2.arrow_0. fuel%vstd!std_specs.option.is_some.
  fuel%vstd!std_specs.option.is_none. fuel%vstd!std_specs.option.spec_unwrap. fuel%vstd!cell.impl&%2.is_init.
  fuel%vstd!cell.impl&%2.is_uninit. fuel%vstd!map.impl&%0.spec_index. fuel%vstd!map.axiom_map_index_decreases_finite.
  fuel%vstd!map.axiom_map_index_decreases_infinite. fuel%vstd!map.axiom_map_insert_domain.
  fuel%vstd!map.axiom_map_insert_same. fuel%vstd!map.axiom_map_insert_different. fuel%vstd!map.axiom_map_remove_domain.
  fuel%vstd!map.axiom_map_remove_different. fuel%vstd!map.axiom_map_ext_equal. fuel%vstd!map.axiom_map_ext_equal_deep.
  fuel%vstd!map_lib.impl&%0.contains_pair. fuel%vstd!pervasive.strictly_cloned. fuel%vstd!pervasive.cloned.
  fuel%vstd!raw_ptr.impl&%6.is_init. fuel%vstd!raw_ptr.impl&%6.is_uninit. fuel%vstd!seq.impl&%0.spec_index.
  fuel%vstd!seq.axiom_seq_index_decreases. fuel%vstd!seq.axiom_seq_ext_equal. fuel%vstd!seq.axiom_seq_ext_equal_deep.
  fuel%vstd!set.axiom_set_insert_same. fuel%vstd!set.axiom_set_insert_different. fuel%vstd!set.axiom_set_remove_same.
  fuel%vstd!set.axiom_set_remove_insert. fuel%vstd!set.axiom_set_remove_different.
  fuel%vstd!set.axiom_set_ext_equal. fuel%vstd!set.axiom_set_ext_equal_deep. fuel%vstd!set.axiom_set_insert_finite.
  fuel%vstd!set.axiom_set_remove_finite. fuel%producer_comsumer_example!FifoQueue.impl&%0.arrow_produce_end_0.
  fuel%producer_comsumer_example!FifoQueue.impl&%0.arrow_consume_end_0. fuel%producer_comsumer_example!FifoQueue.impl&%0.arrow_dummy_to_use_type_params_0.
  fuel%producer_comsumer_example!FifoQueue.impl&%1.is_produce_start. fuel%producer_comsumer_example!FifoQueue.impl&%1.is_produce_end.
  fuel%producer_comsumer_example!FifoQueue.impl&%1.get_produce_end_0. fuel%producer_comsumer_example!FifoQueue.impl&%1.is_consume_start.
  fuel%producer_comsumer_example!FifoQueue.impl&%1.is_consume_end. fuel%producer_comsumer_example!FifoQueue.impl&%1.get_consume_end_0.
  fuel%producer_comsumer_example!FifoQueue.impl&%1.is_dummy_to_use_type_params. fuel%producer_comsumer_example!FifoQueue.impl&%1.get_dummy_to_use_type_params_0.
  fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_1. fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_0.
  fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_1. fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_dummy_to_use_type_params_0.
  fuel%producer_comsumer_example!FifoQueue.impl&%3.is_initialize. fuel%producer_comsumer_example!FifoQueue.impl&%3.get_initialize_0.
  fuel%producer_comsumer_example!FifoQueue.impl&%3.get_initialize_1. fuel%producer_comsumer_example!FifoQueue.impl&%3.is_dummy_to_use_type_params.
  fuel%producer_comsumer_example!FifoQueue.impl&%3.get_dummy_to_use_type_params_0.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.initialize. fuel%producer_comsumer_example!FifoQueue.impl&%19.initialize_enabled.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_start. fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_start_strong.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_start_enabled. fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_end.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_end_strong. fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_end_enabled.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_start. fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_start_strong.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_start_enabled. fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_end.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_end_strong. fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_end_enabled.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.next_by. fuel%producer_comsumer_example!FifoQueue.impl&%19.next.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.next_strong_by. fuel%producer_comsumer_example!FifoQueue.impl&%19.next_strong.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.init_by. fuel%producer_comsumer_example!FifoQueue.impl&%19.init.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.invariant. fuel%producer_comsumer_example!FifoQueue.impl&%19.not_overlapping.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.in_bounds. fuel%producer_comsumer_example!FifoQueue.impl&%19.valid_storage_all.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.len. fuel%producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.in_active_range. fuel%producer_comsumer_example!FifoQueue.impl&%19.is_checked_out.
  fuel%producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx. fuel%producer_comsumer_example!impl&%0.arrow_Idle_0.
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
(declare-sort vstd!state_machine_internal.NoCopy. 0)
(declare-datatypes ((core!option.Option. 0) (vstd!raw_ptr.MemContents. 0) (vstd!tokens.InstanceId.
   0
  ) (producer_comsumer_example!FifoQueue.State. 0) (producer_comsumer_example!FifoQueue.Step.
   0
  ) (producer_comsumer_example!FifoQueue.Config. 0) (producer_comsumer_example!FifoQueue.Instance.
   0
  ) (producer_comsumer_example!FifoQueue.head. 0) (producer_comsumer_example!FifoQueue.tail.
   0
  ) (producer_comsumer_example!FifoQueue.producer. 0) (producer_comsumer_example!FifoQueue.consumer.
   0
  ) (producer_comsumer_example!ProducerState. 0) (producer_comsumer_example!ConsumerState.
   0
  ) (tuple%0. 0) (tuple%1. 0) (tuple%2. 0) (tuple%5. 0)
 ) (((core!option.Option./None) (core!option.Option./Some (core!option.Option./Some/?0
     Poly
   ))
  ) ((vstd!raw_ptr.MemContents./Uninit) (vstd!raw_ptr.MemContents./Init (vstd!raw_ptr.MemContents./Init/?0
     Poly
   ))
  ) ((vstd!tokens.InstanceId./InstanceId (vstd!tokens.InstanceId./InstanceId/?0 Int)))
  ((producer_comsumer_example!FifoQueue.State./State (producer_comsumer_example!FifoQueue.State./State/?backing_cells
     vstd!seq.Seq<vstd!cell.CellId.>.
    ) (producer_comsumer_example!FifoQueue.State./State/?storage Poly) (producer_comsumer_example!FifoQueue.State./State/?head
     Int
    ) (producer_comsumer_example!FifoQueue.State./State/?tail Int) (producer_comsumer_example!FifoQueue.State./State/?producer
     producer_comsumer_example!ProducerState.
    ) (producer_comsumer_example!FifoQueue.State./State/?consumer producer_comsumer_example!ConsumerState.)
   )
  ) ((producer_comsumer_example!FifoQueue.Step./produce_start) (producer_comsumer_example!FifoQueue.Step./produce_end
    (producer_comsumer_example!FifoQueue.Step./produce_end/?0 Poly)
   ) (producer_comsumer_example!FifoQueue.Step./consume_start) (producer_comsumer_example!FifoQueue.Step./consume_end
    (producer_comsumer_example!FifoQueue.Step./consume_end/?0 Poly)
   ) (producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params (producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/?0
     producer_comsumer_example!FifoQueue.State.
   ))
  ) ((producer_comsumer_example!FifoQueue.Config./initialize (producer_comsumer_example!FifoQueue.Config./initialize/?0
     vstd!seq.Seq<vstd!cell.CellId.>.
    ) (producer_comsumer_example!FifoQueue.Config./initialize/?1 Poly)
   ) (producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params (producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/?0
     producer_comsumer_example!FifoQueue.State.
   ))
  ) ((producer_comsumer_example!FifoQueue.Instance./Instance (producer_comsumer_example!FifoQueue.Instance./Instance/?send_sync
     Poly
    ) (producer_comsumer_example!FifoQueue.Instance./Instance/?state core!option.Option.)
    (producer_comsumer_example!FifoQueue.Instance./Instance/?location Int)
   )
  ) ((producer_comsumer_example!FifoQueue.head./head (producer_comsumer_example!FifoQueue.head./head/?dummy_instance
     producer_comsumer_example!FifoQueue.Instance.
    ) (producer_comsumer_example!FifoQueue.head./head/?no_copy vstd!state_machine_internal.NoCopy.)
   )
  ) ((producer_comsumer_example!FifoQueue.tail./tail (producer_comsumer_example!FifoQueue.tail./tail/?dummy_instance
     producer_comsumer_example!FifoQueue.Instance.
    ) (producer_comsumer_example!FifoQueue.tail./tail/?no_copy vstd!state_machine_internal.NoCopy.)
   )
  ) ((producer_comsumer_example!FifoQueue.producer./producer (producer_comsumer_example!FifoQueue.producer./producer/?dummy_instance
     producer_comsumer_example!FifoQueue.Instance.
    ) (producer_comsumer_example!FifoQueue.producer./producer/?no_copy vstd!state_machine_internal.NoCopy.)
   )
  ) ((producer_comsumer_example!FifoQueue.consumer./consumer (producer_comsumer_example!FifoQueue.consumer./consumer/?dummy_instance
     producer_comsumer_example!FifoQueue.Instance.
    ) (producer_comsumer_example!FifoQueue.consumer./consumer/?no_copy vstd!state_machine_internal.NoCopy.)
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
  ) ((tuple%0./tuple%0)) ((tuple%1./tuple%1 (tuple%1./tuple%1/?0 Poly))) ((tuple%2./tuple%2
    (tuple%2./tuple%2/?0 Poly) (tuple%2./tuple%2/?1 Poly)
   )
  ) ((tuple%5./tuple%5 (tuple%5./tuple%5/?0 Poly) (tuple%5./tuple%5/?1 Poly) (tuple%5./tuple%5/?2
     Poly
    ) (tuple%5./tuple%5/?3 Poly) (tuple%5./tuple%5/?4 Poly)
))))
(declare-fun core!option.Option./Some/0 (Dcr Type core!option.Option.) Poly)
(declare-fun vstd!raw_ptr.MemContents./Init/0 (Dcr Type vstd!raw_ptr.MemContents.)
 Poly
)
(declare-fun vstd!tokens.InstanceId./InstanceId/0 (vstd!tokens.InstanceId.) Int)
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
(declare-fun producer_comsumer_example!FifoQueue.Step./produce_end/0 (Dcr Type producer_comsumer_example!FifoQueue.Step.)
 Poly
)
(declare-fun producer_comsumer_example!FifoQueue.Step./consume_end/0 (Dcr Type producer_comsumer_example!FifoQueue.Step.)
 Poly
)
(declare-fun producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0
 (Dcr Type producer_comsumer_example!FifoQueue.Step.) producer_comsumer_example!FifoQueue.State.
)
(declare-fun producer_comsumer_example!FifoQueue.Config./initialize/0 (Dcr Type producer_comsumer_example!FifoQueue.Config.)
 vstd!seq.Seq<vstd!cell.CellId.>.
)
(declare-fun producer_comsumer_example!FifoQueue.Config./initialize/1 (Dcr Type producer_comsumer_example!FifoQueue.Config.)
 Poly
)
(declare-fun producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0
 (Dcr Type producer_comsumer_example!FifoQueue.Config.) producer_comsumer_example!FifoQueue.State.
)
(declare-fun producer_comsumer_example!FifoQueue.Instance./Instance/send_sync (producer_comsumer_example!FifoQueue.Instance.)
 Poly
)
(declare-fun producer_comsumer_example!FifoQueue.Instance./Instance/state (producer_comsumer_example!FifoQueue.Instance.)
 core!option.Option.
)
(declare-fun producer_comsumer_example!FifoQueue.Instance./Instance/location (producer_comsumer_example!FifoQueue.Instance.)
 Int
)
(declare-fun producer_comsumer_example!FifoQueue.head./head/dummy_instance (producer_comsumer_example!FifoQueue.head.)
 producer_comsumer_example!FifoQueue.Instance.
)
(declare-fun producer_comsumer_example!FifoQueue.head./head/no_copy (producer_comsumer_example!FifoQueue.head.)
 vstd!state_machine_internal.NoCopy.
)
(declare-fun producer_comsumer_example!FifoQueue.tail./tail/dummy_instance (producer_comsumer_example!FifoQueue.tail.)
 producer_comsumer_example!FifoQueue.Instance.
)
(declare-fun producer_comsumer_example!FifoQueue.tail./tail/no_copy (producer_comsumer_example!FifoQueue.tail.)
 vstd!state_machine_internal.NoCopy.
)
(declare-fun producer_comsumer_example!FifoQueue.producer./producer/dummy_instance
 (producer_comsumer_example!FifoQueue.producer.) producer_comsumer_example!FifoQueue.Instance.
)
(declare-fun producer_comsumer_example!FifoQueue.producer./producer/no_copy (producer_comsumer_example!FifoQueue.producer.)
 vstd!state_machine_internal.NoCopy.
)
(declare-fun producer_comsumer_example!FifoQueue.consumer./consumer/dummy_instance
 (producer_comsumer_example!FifoQueue.consumer.) producer_comsumer_example!FifoQueue.Instance.
)
(declare-fun producer_comsumer_example!FifoQueue.consumer./consumer/no_copy (producer_comsumer_example!FifoQueue.consumer.)
 vstd!state_machine_internal.NoCopy.
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
(declare-fun tuple%1./tuple%1/0 (tuple%1.) Poly)
(declare-fun tuple%2./tuple%2/0 (tuple%2.) Poly)
(declare-fun tuple%2./tuple%2/1 (tuple%2.) Poly)
(declare-fun tuple%5./tuple%5/0 (tuple%5.) Poly)
(declare-fun tuple%5./tuple%5/1 (tuple%5.) Poly)
(declare-fun tuple%5./tuple%5/2 (tuple%5.) Poly)
(declare-fun tuple%5./tuple%5/3 (tuple%5.) Poly)
(declare-fun tuple%5./tuple%5/4 (tuple%5.) Poly)
(declare-fun TYPE%core!option.Option. (Dcr Type) Type)
(declare-fun TYPE%vstd!cell.PointsTo. (Dcr Type) Type)
(declare-const TYPE%vstd!cell.CellId. Type)
(declare-fun TYPE%vstd!map.Map. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%vstd!raw_ptr.MemContents. (Dcr Type) Type)
(declare-fun TYPE%vstd!seq.Seq. (Dcr Type) Type)
(declare-fun TYPE%vstd!set.Set. (Dcr Type) Type)
(declare-fun TYPE%vstd!state_machine_internal.SyncSendIfSyncSend. (Dcr Type) Type)
(declare-const TYPE%vstd!state_machine_internal.NoCopy. Type)
(declare-const TYPE%vstd!tokens.InstanceId. Type)
(declare-fun TYPE%producer_comsumer_example!FifoQueue.State. (Dcr Type) Type)
(declare-fun TYPE%producer_comsumer_example!FifoQueue.Step. (Dcr Type) Type)
(declare-fun TYPE%producer_comsumer_example!FifoQueue.Config. (Dcr Type) Type)
(declare-fun TYPE%producer_comsumer_example!FifoQueue.Instance. (Dcr Type) Type)
(declare-fun TYPE%producer_comsumer_example!FifoQueue.head. (Dcr Type) Type)
(declare-fun TYPE%producer_comsumer_example!FifoQueue.tail. (Dcr Type) Type)
(declare-fun TYPE%producer_comsumer_example!FifoQueue.producer. (Dcr Type) Type)
(declare-fun TYPE%producer_comsumer_example!FifoQueue.consumer. (Dcr Type) Type)
(declare-const TYPE%producer_comsumer_example!ProducerState. Type)
(declare-const TYPE%producer_comsumer_example!ConsumerState. Type)
(declare-fun TYPE%tuple%1. (Dcr Type) Type)
(declare-fun TYPE%tuple%2. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%tuple%5. (Dcr Type Dcr Type Dcr Type Dcr Type Dcr Type) Type)
(declare-fun FNDEF%core!clone.Clone.clone. (Dcr Type) Type)
(declare-fun Poly%vstd!cell.CellId. (vstd!cell.CellId.) Poly)
(declare-fun %Poly%vstd!cell.CellId. (Poly) vstd!cell.CellId.)
(declare-fun Poly%vstd!seq.Seq<vstd!cell.CellId.>. (vstd!seq.Seq<vstd!cell.CellId.>.)
 Poly
)
(declare-fun %Poly%vstd!seq.Seq<vstd!cell.CellId.>. (Poly) vstd!seq.Seq<vstd!cell.CellId.>.)
(declare-fun Poly%vstd!set.Set<nat.>. (vstd!set.Set<nat.>.) Poly)
(declare-fun %Poly%vstd!set.Set<nat.>. (Poly) vstd!set.Set<nat.>.)
(declare-fun Poly%vstd!state_machine_internal.NoCopy. (vstd!state_machine_internal.NoCopy.)
 Poly
)
(declare-fun %Poly%vstd!state_machine_internal.NoCopy. (Poly) vstd!state_machine_internal.NoCopy.)
(declare-fun Poly%core!option.Option. (core!option.Option.) Poly)
(declare-fun %Poly%core!option.Option. (Poly) core!option.Option.)
(declare-fun Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.MemContents.) Poly)
(declare-fun %Poly%vstd!raw_ptr.MemContents. (Poly) vstd!raw_ptr.MemContents.)
(declare-fun Poly%vstd!tokens.InstanceId. (vstd!tokens.InstanceId.) Poly)
(declare-fun %Poly%vstd!tokens.InstanceId. (Poly) vstd!tokens.InstanceId.)
(declare-fun Poly%producer_comsumer_example!FifoQueue.State. (producer_comsumer_example!FifoQueue.State.)
 Poly
)
(declare-fun %Poly%producer_comsumer_example!FifoQueue.State. (Poly) producer_comsumer_example!FifoQueue.State.)
(declare-fun Poly%producer_comsumer_example!FifoQueue.Step. (producer_comsumer_example!FifoQueue.Step.)
 Poly
)
(declare-fun %Poly%producer_comsumer_example!FifoQueue.Step. (Poly) producer_comsumer_example!FifoQueue.Step.)
(declare-fun Poly%producer_comsumer_example!FifoQueue.Config. (producer_comsumer_example!FifoQueue.Config.)
 Poly
)
(declare-fun %Poly%producer_comsumer_example!FifoQueue.Config. (Poly) producer_comsumer_example!FifoQueue.Config.)
(declare-fun Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.Instance.)
 Poly
)
(declare-fun %Poly%producer_comsumer_example!FifoQueue.Instance. (Poly) producer_comsumer_example!FifoQueue.Instance.)
(declare-fun Poly%producer_comsumer_example!FifoQueue.head. (producer_comsumer_example!FifoQueue.head.)
 Poly
)
(declare-fun %Poly%producer_comsumer_example!FifoQueue.head. (Poly) producer_comsumer_example!FifoQueue.head.)
(declare-fun Poly%producer_comsumer_example!FifoQueue.tail. (producer_comsumer_example!FifoQueue.tail.)
 Poly
)
(declare-fun %Poly%producer_comsumer_example!FifoQueue.tail. (Poly) producer_comsumer_example!FifoQueue.tail.)
(declare-fun Poly%producer_comsumer_example!FifoQueue.producer. (producer_comsumer_example!FifoQueue.producer.)
 Poly
)
(declare-fun %Poly%producer_comsumer_example!FifoQueue.producer. (Poly) producer_comsumer_example!FifoQueue.producer.)
(declare-fun Poly%producer_comsumer_example!FifoQueue.consumer. (producer_comsumer_example!FifoQueue.consumer.)
 Poly
)
(declare-fun %Poly%producer_comsumer_example!FifoQueue.consumer. (Poly) producer_comsumer_example!FifoQueue.consumer.)
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
(declare-fun Poly%tuple%1. (tuple%1.) Poly)
(declare-fun %Poly%tuple%1. (Poly) tuple%1.)
(declare-fun Poly%tuple%2. (tuple%2.) Poly)
(declare-fun %Poly%tuple%2. (Poly) tuple%2.)
(declare-fun Poly%tuple%5. (tuple%5.) Poly)
(declare-fun %Poly%tuple%5. (Poly) tuple%5.)
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
 (forall ((x vstd!state_machine_internal.NoCopy.)) (!
   (= x (%Poly%vstd!state_machine_internal.NoCopy. (Poly%vstd!state_machine_internal.NoCopy.
      x
   )))
   :pattern ((Poly%vstd!state_machine_internal.NoCopy. x))
   :qid internal_vstd__state_machine_internal__NoCopy_box_axiom_definition
   :skolemid skolem_internal_vstd__state_machine_internal__NoCopy_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%vstd!state_machine_internal.NoCopy.)
    (= x (Poly%vstd!state_machine_internal.NoCopy. (%Poly%vstd!state_machine_internal.NoCopy.
       x
   ))))
   :pattern ((has_type x TYPE%vstd!state_machine_internal.NoCopy.))
   :qid internal_vstd__state_machine_internal__NoCopy_unbox_axiom_definition
   :skolemid skolem_internal_vstd__state_machine_internal__NoCopy_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!state_machine_internal.NoCopy.)) (!
   (has_type (Poly%vstd!state_machine_internal.NoCopy. x) TYPE%vstd!state_machine_internal.NoCopy.)
   :pattern ((has_type (Poly%vstd!state_machine_internal.NoCopy. x) TYPE%vstd!state_machine_internal.NoCopy.))
   :qid internal_vstd__state_machine_internal__NoCopy_has_type_always_definition
   :skolemid skolem_internal_vstd__state_machine_internal__NoCopy_has_type_always_definition
)))
(assert
 (forall ((x core!option.Option.)) (!
   (= x (%Poly%core!option.Option. (Poly%core!option.Option. x)))
   :pattern ((Poly%core!option.Option. x))
   :qid internal_core__option__Option_box_axiom_definition
   :skolemid skolem_internal_core__option__Option_box_axiom_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!option.Option. V&. V&))
    (= x (Poly%core!option.Option. (%Poly%core!option.Option. x)))
   )
   :pattern ((has_type x (TYPE%core!option.Option. V&. V&)))
   :qid internal_core__option__Option_unbox_axiom_definition
   :skolemid skolem_internal_core__option__Option_unbox_axiom_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type)) (!
   (has_type (Poly%core!option.Option. core!option.Option./None) (TYPE%core!option.Option.
     V&. V&
   ))
   :pattern ((has_type (Poly%core!option.Option. core!option.Option./None) (TYPE%core!option.Option.
      V&. V&
   )))
   :qid internal_core!option.Option./None_constructor_definition
   :skolemid skolem_internal_core!option.Option./None_constructor_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (_0! Poly)) (!
   (=>
    (has_type _0! V&)
    (has_type (Poly%core!option.Option. (core!option.Option./Some _0!)) (TYPE%core!option.Option.
      V&. V&
   )))
   :pattern ((has_type (Poly%core!option.Option. (core!option.Option./Some _0!)) (TYPE%core!option.Option.
      V&. V&
   )))
   :qid internal_core!option.Option./Some_constructor_definition
   :skolemid skolem_internal_core!option.Option./Some_constructor_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (x core!option.Option.)) (!
   (=>
    (is-core!option.Option./Some x)
    (= (core!option.Option./Some/0 V&. V& x) (core!option.Option./Some/?0 x))
   )
   :pattern ((core!option.Option./Some/0 V&. V& x))
   :qid internal_core!option.Option./Some/0_accessor_definition
   :skolemid skolem_internal_core!option.Option./Some/0_accessor_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!option.Option. V&. V&))
    (has_type (core!option.Option./Some/0 V&. V& (%Poly%core!option.Option. x)) V&)
   )
   :pattern ((core!option.Option./Some/0 V&. V& (%Poly%core!option.Option. x)) (has_type
     x (TYPE%core!option.Option. V&. V&)
   ))
   :qid internal_core!option.Option./Some/0_invariant_definition
   :skolemid skolem_internal_core!option.Option./Some/0_invariant_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (x core!option.Option.)) (!
   (=>
    (is-core!option.Option./Some x)
    (height_lt (height (core!option.Option./Some/0 V&. V& x)) (height (Poly%core!option.Option.
       x
   ))))
   :pattern ((height (core!option.Option./Some/0 V&. V& x)))
   :qid prelude_datatype_height_core!option.Option./Some/0
   :skolemid skolem_prelude_datatype_height_core!option.Option./Some/0
)))
(assert
 (forall ((V&. Dcr) (V& Type) (deep Bool) (x Poly) (y Poly)) (!
   (=>
    (and
     (has_type x (TYPE%core!option.Option. V&. V&))
     (has_type y (TYPE%core!option.Option. V&. V&))
     (is-core!option.Option./None (%Poly%core!option.Option. x))
     (is-core!option.Option./None (%Poly%core!option.Option. y))
    )
    (ext_eq deep (TYPE%core!option.Option. V&. V&) x y)
   )
   :pattern ((ext_eq deep (TYPE%core!option.Option. V&. V&) x y))
   :qid internal_core!option.Option./None_ext_equal_definition
   :skolemid skolem_internal_core!option.Option./None_ext_equal_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (deep Bool) (x Poly) (y Poly)) (!
   (=>
    (and
     (has_type x (TYPE%core!option.Option. V&. V&))
     (has_type y (TYPE%core!option.Option. V&. V&))
     (is-core!option.Option./Some (%Poly%core!option.Option. x))
     (is-core!option.Option./Some (%Poly%core!option.Option. y))
     (ext_eq deep V& (core!option.Option./Some/0 V&. V& (%Poly%core!option.Option. x))
      (core!option.Option./Some/0 V&. V& (%Poly%core!option.Option. y))
    ))
    (ext_eq deep (TYPE%core!option.Option. V&. V&) x y)
   )
   :pattern ((ext_eq deep (TYPE%core!option.Option. V&. V&) x y))
   :qid internal_core!option.Option./Some_ext_equal_definition
   :skolemid skolem_internal_core!option.Option./Some_ext_equal_definition
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
 (forall ((x vstd!tokens.InstanceId.)) (!
   (= x (%Poly%vstd!tokens.InstanceId. (Poly%vstd!tokens.InstanceId. x)))
   :pattern ((Poly%vstd!tokens.InstanceId. x))
   :qid internal_vstd__tokens__InstanceId_box_axiom_definition
   :skolemid skolem_internal_vstd__tokens__InstanceId_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%vstd!tokens.InstanceId.)
    (= x (Poly%vstd!tokens.InstanceId. (%Poly%vstd!tokens.InstanceId. x)))
   )
   :pattern ((has_type x TYPE%vstd!tokens.InstanceId.))
   :qid internal_vstd__tokens__InstanceId_unbox_axiom_definition
   :skolemid skolem_internal_vstd__tokens__InstanceId_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!tokens.InstanceId.)) (!
   (= (vstd!tokens.InstanceId./InstanceId/0 x) (vstd!tokens.InstanceId./InstanceId/?0
     x
   ))
   :pattern ((vstd!tokens.InstanceId./InstanceId/0 x))
   :qid internal_vstd!tokens.InstanceId./InstanceId/0_accessor_definition
   :skolemid skolem_internal_vstd!tokens.InstanceId./InstanceId/0_accessor_definition
)))
(assert
 (forall ((x vstd!tokens.InstanceId.)) (!
   (has_type (Poly%vstd!tokens.InstanceId. x) TYPE%vstd!tokens.InstanceId.)
   :pattern ((has_type (Poly%vstd!tokens.InstanceId. x) TYPE%vstd!tokens.InstanceId.))
   :qid internal_vstd__tokens__InstanceId_has_type_always_definition
   :skolemid skolem_internal_vstd__tokens__InstanceId_has_type_always_definition
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
 (forall ((x producer_comsumer_example!FifoQueue.Step.)) (!
   (= x (%Poly%producer_comsumer_example!FifoQueue.Step. (Poly%producer_comsumer_example!FifoQueue.Step.
      x
   )))
   :pattern ((Poly%producer_comsumer_example!FifoQueue.Step. x))
   :qid internal_producer_comsumer_example__FifoQueue__Step_box_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__Step_box_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
    (= x (Poly%producer_comsumer_example!FifoQueue.Step. (%Poly%producer_comsumer_example!FifoQueue.Step.
       x
   ))))
   :pattern ((has_type x (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&)))
   :qid internal_producer_comsumer_example__FifoQueue__Step_unbox_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__Step_unbox_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (has_type (Poly%producer_comsumer_example!FifoQueue.Step. producer_comsumer_example!FifoQueue.Step./produce_start)
    (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&)
   )
   :pattern ((has_type (Poly%producer_comsumer_example!FifoQueue.Step. producer_comsumer_example!FifoQueue.Step./produce_start)
     (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&)
   ))
   :qid internal_producer_comsumer_example!FifoQueue.Step./produce_start_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Step./produce_start_constructor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_0! Poly)) (!
   (=>
    (has_type _0! (TYPE%vstd!cell.PointsTo. T&. T&))
    (has_type (Poly%producer_comsumer_example!FifoQueue.Step. (producer_comsumer_example!FifoQueue.Step./produce_end
       _0!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&)
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!FifoQueue.Step. (producer_comsumer_example!FifoQueue.Step./produce_end
       _0!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&)
   ))
   :qid internal_producer_comsumer_example!FifoQueue.Step./produce_end_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Step./produce_end_constructor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x producer_comsumer_example!FifoQueue.Step.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.Step./produce_end x)
    (= (producer_comsumer_example!FifoQueue.Step./produce_end/0 T&. T& x) (producer_comsumer_example!FifoQueue.Step./produce_end/?0
      x
   )))
   :pattern ((producer_comsumer_example!FifoQueue.Step./produce_end/0 T&. T& x))
   :qid internal_producer_comsumer_example!FifoQueue.Step./produce_end/0_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Step./produce_end/0_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
    (has_type (producer_comsumer_example!FifoQueue.Step./produce_end/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step.
       x
      )
     ) (TYPE%vstd!cell.PointsTo. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.Step./produce_end/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step.
      x
     )
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.Step./produce_end/0_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Step./produce_end/0_invariant_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (has_type (Poly%producer_comsumer_example!FifoQueue.Step. producer_comsumer_example!FifoQueue.Step./consume_start)
    (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&)
   )
   :pattern ((has_type (Poly%producer_comsumer_example!FifoQueue.Step. producer_comsumer_example!FifoQueue.Step./consume_start)
     (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&)
   ))
   :qid internal_producer_comsumer_example!FifoQueue.Step./consume_start_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Step./consume_start_constructor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_0! Poly)) (!
   (=>
    (has_type _0! (TYPE%vstd!cell.PointsTo. T&. T&))
    (has_type (Poly%producer_comsumer_example!FifoQueue.Step. (producer_comsumer_example!FifoQueue.Step./consume_end
       _0!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&)
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!FifoQueue.Step. (producer_comsumer_example!FifoQueue.Step./consume_end
       _0!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&)
   ))
   :qid internal_producer_comsumer_example!FifoQueue.Step./consume_end_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Step./consume_end_constructor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x producer_comsumer_example!FifoQueue.Step.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.Step./consume_end x)
    (= (producer_comsumer_example!FifoQueue.Step./consume_end/0 T&. T& x) (producer_comsumer_example!FifoQueue.Step./consume_end/?0
      x
   )))
   :pattern ((producer_comsumer_example!FifoQueue.Step./consume_end/0 T&. T& x))
   :qid internal_producer_comsumer_example!FifoQueue.Step./consume_end/0_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Step./consume_end/0_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
    (has_type (producer_comsumer_example!FifoQueue.Step./consume_end/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step.
       x
      )
     ) (TYPE%vstd!cell.PointsTo. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.Step./consume_end/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step.
      x
     )
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.Step./consume_end/0_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Step./consume_end/0_invariant_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_0! producer_comsumer_example!FifoQueue.State.)) (!
   (=>
    (has_type (Poly%producer_comsumer_example!FifoQueue.State. _0!) (TYPE%producer_comsumer_example!FifoQueue.State.
      T&. T&
    ))
    (has_type (Poly%producer_comsumer_example!FifoQueue.Step. (producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params
       _0!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&)
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!FifoQueue.Step. (producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params
       _0!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&)
   ))
   :qid internal_producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params_constructor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x producer_comsumer_example!FifoQueue.Step.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params x)
    (= (producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0 T&. T& x)
     (producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/?0 x)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0 T&.
     T& x
   ))
   :qid internal_producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
    (has_type (Poly%producer_comsumer_example!FifoQueue.State. (producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0
       T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step. x)
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0 T&.
     T& (%Poly%producer_comsumer_example!FifoQueue.Step. x)
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0_invariant_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x producer_comsumer_example!FifoQueue.Step.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.Step./produce_end x)
    (height_lt (height (producer_comsumer_example!FifoQueue.Step./produce_end/0 T&. T& x))
     (height (Poly%producer_comsumer_example!FifoQueue.Step. x))
   ))
   :pattern ((height (producer_comsumer_example!FifoQueue.Step./produce_end/0 T&. T& x)))
   :qid prelude_datatype_height_producer_comsumer_example!FifoQueue.Step./produce_end/0
   :skolemid skolem_prelude_datatype_height_producer_comsumer_example!FifoQueue.Step./produce_end/0
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x producer_comsumer_example!FifoQueue.Step.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.Step./consume_end x)
    (height_lt (height (producer_comsumer_example!FifoQueue.Step./consume_end/0 T&. T& x))
     (height (Poly%producer_comsumer_example!FifoQueue.Step. x))
   ))
   :pattern ((height (producer_comsumer_example!FifoQueue.Step./consume_end/0 T&. T& x)))
   :qid prelude_datatype_height_producer_comsumer_example!FifoQueue.Step./consume_end/0
   :skolemid skolem_prelude_datatype_height_producer_comsumer_example!FifoQueue.Step./consume_end/0
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x producer_comsumer_example!FifoQueue.Step.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params x)
    (height_lt (height (Poly%producer_comsumer_example!FifoQueue.State. (producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0
        T&. T& x
      ))
     ) (height (Poly%producer_comsumer_example!FifoQueue.Step. x))
   ))
   :pattern ((height (Poly%producer_comsumer_example!FifoQueue.State. (producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0
       T&. T& x
   ))))
   :qid prelude_datatype_height_producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0
   :skolemid skolem_prelude_datatype_height_producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.Config.)) (!
   (= x (%Poly%producer_comsumer_example!FifoQueue.Config. (Poly%producer_comsumer_example!FifoQueue.Config.
      x
   )))
   :pattern ((Poly%producer_comsumer_example!FifoQueue.Config. x))
   :qid internal_producer_comsumer_example__FifoQueue__Config_box_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__Config_box_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&))
    (= x (Poly%producer_comsumer_example!FifoQueue.Config. (%Poly%producer_comsumer_example!FifoQueue.Config.
       x
   ))))
   :pattern ((has_type x (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&)))
   :qid internal_producer_comsumer_example__FifoQueue__Config_unbox_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__Config_unbox_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_0! vstd!seq.Seq<vstd!cell.CellId.>.) (_1! Poly)) (!
   (=>
    (has_type _1! (TYPE%vstd!map.Map. $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&)))
    (has_type (Poly%producer_comsumer_example!FifoQueue.Config. (producer_comsumer_example!FifoQueue.Config./initialize
       _0! _1!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&)
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!FifoQueue.Config. (producer_comsumer_example!FifoQueue.Config./initialize
       _0! _1!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&)
   ))
   :qid internal_producer_comsumer_example!FifoQueue.Config./initialize_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Config./initialize_constructor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x producer_comsumer_example!FifoQueue.Config.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.Config./initialize x)
    (= (producer_comsumer_example!FifoQueue.Config./initialize/0 T&. T& x) (producer_comsumer_example!FifoQueue.Config./initialize/?0
      x
   )))
   :pattern ((producer_comsumer_example!FifoQueue.Config./initialize/0 T&. T& x))
   :qid internal_producer_comsumer_example!FifoQueue.Config./initialize/0_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Config./initialize/0_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x producer_comsumer_example!FifoQueue.Config.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.Config./initialize x)
    (= (producer_comsumer_example!FifoQueue.Config./initialize/1 T&. T& x) (producer_comsumer_example!FifoQueue.Config./initialize/?1
      x
   )))
   :pattern ((producer_comsumer_example!FifoQueue.Config./initialize/1 T&. T& x))
   :qid internal_producer_comsumer_example!FifoQueue.Config./initialize/1_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Config./initialize/1_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&))
    (has_type (producer_comsumer_example!FifoQueue.Config./initialize/1 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Config.
       x
      )
     ) (TYPE%vstd!map.Map. $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&))
   ))
   :pattern ((producer_comsumer_example!FifoQueue.Config./initialize/1 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Config.
      x
     )
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.Config./initialize/1_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Config./initialize/1_invariant_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_0! producer_comsumer_example!FifoQueue.State.)) (!
   (=>
    (has_type (Poly%producer_comsumer_example!FifoQueue.State. _0!) (TYPE%producer_comsumer_example!FifoQueue.State.
      T&. T&
    ))
    (has_type (Poly%producer_comsumer_example!FifoQueue.Config. (producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params
       _0!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&)
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!FifoQueue.Config. (producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params
       _0!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&)
   ))
   :qid internal_producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params_constructor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x producer_comsumer_example!FifoQueue.Config.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params x)
    (= (producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0 T&. T& x)
     (producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/?0 x)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0 T&.
     T& x
   ))
   :qid internal_producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&))
    (has_type (Poly%producer_comsumer_example!FifoQueue.State. (producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0
       T&. T& (%Poly%producer_comsumer_example!FifoQueue.Config. x)
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0 T&.
     T& (%Poly%producer_comsumer_example!FifoQueue.Config. x)
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0_invariant_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x producer_comsumer_example!FifoQueue.Config.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.Config./initialize x)
    (height_lt (height (producer_comsumer_example!FifoQueue.Config./initialize/1 T&. T&
       x
      )
     ) (height (Poly%producer_comsumer_example!FifoQueue.Config. x))
   ))
   :pattern ((height (producer_comsumer_example!FifoQueue.Config./initialize/1 T&. T& x)))
   :qid prelude_datatype_height_producer_comsumer_example!FifoQueue.Config./initialize/1
   :skolemid skolem_prelude_datatype_height_producer_comsumer_example!FifoQueue.Config./initialize/1
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x producer_comsumer_example!FifoQueue.Config.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params x)
    (height_lt (height (Poly%producer_comsumer_example!FifoQueue.State. (producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0
        T&. T& x
      ))
     ) (height (Poly%producer_comsumer_example!FifoQueue.Config. x))
   ))
   :pattern ((height (Poly%producer_comsumer_example!FifoQueue.State. (producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0
       T&. T& x
   ))))
   :qid prelude_datatype_height_producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0
   :skolemid skolem_prelude_datatype_height_producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.Instance.)) (!
   (= x (%Poly%producer_comsumer_example!FifoQueue.Instance. (Poly%producer_comsumer_example!FifoQueue.Instance.
      x
   )))
   :pattern ((Poly%producer_comsumer_example!FifoQueue.Instance. x))
   :qid internal_producer_comsumer_example__FifoQueue__Instance_box_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__Instance_box_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.Instance. T&. T&))
    (= x (Poly%producer_comsumer_example!FifoQueue.Instance. (%Poly%producer_comsumer_example!FifoQueue.Instance.
       x
   ))))
   :pattern ((has_type x (TYPE%producer_comsumer_example!FifoQueue.Instance. T&. T&)))
   :qid internal_producer_comsumer_example__FifoQueue__Instance_unbox_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__Instance_unbox_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_send_sync! Poly) (_state! core!option.Option.) (_location!
    Int
   )
  ) (!
   (=>
    (and
     (has_type _send_sync! (TYPE%vstd!state_machine_internal.SyncSendIfSyncSend. $ (TYPE%vstd!cell.PointsTo.
        T&. T&
     )))
     (has_type (Poly%core!option.Option. _state!) (TYPE%core!option.Option. (GHOST $) (TYPE%producer_comsumer_example!FifoQueue.State.
        T&. T&
    ))))
    (has_type (Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.Instance./Instance
       _send_sync! _state! _location!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Instance. T&. T&)
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.Instance./Instance
       _send_sync! _state! _location!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Instance. T&. T&)
   ))
   :qid internal_producer_comsumer_example!FifoQueue.Instance./Instance_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Instance./Instance_constructor_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.Instance.)) (!
   (= (producer_comsumer_example!FifoQueue.Instance./Instance/send_sync x) (producer_comsumer_example!FifoQueue.Instance./Instance/?send_sync
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.Instance./Instance/send_sync x))
   :qid internal_producer_comsumer_example!FifoQueue.Instance./Instance/send_sync_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Instance./Instance/send_sync_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.Instance. T&. T&))
    (has_type (producer_comsumer_example!FifoQueue.Instance./Instance/send_sync (%Poly%producer_comsumer_example!FifoQueue.Instance.
       x
      )
     ) (TYPE%vstd!state_machine_internal.SyncSendIfSyncSend. $ (TYPE%vstd!cell.PointsTo.
       T&. T&
   ))))
   :pattern ((producer_comsumer_example!FifoQueue.Instance./Instance/send_sync (%Poly%producer_comsumer_example!FifoQueue.Instance.
      x
     )
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.Instance. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.Instance./Instance/send_sync_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Instance./Instance/send_sync_invariant_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.Instance.)) (!
   (= (producer_comsumer_example!FifoQueue.Instance./Instance/state x) (producer_comsumer_example!FifoQueue.Instance./Instance/?state
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.Instance./Instance/state x))
   :qid internal_producer_comsumer_example!FifoQueue.Instance./Instance/state_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Instance./Instance/state_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.Instance. T&. T&))
    (has_type (Poly%core!option.Option. (producer_comsumer_example!FifoQueue.Instance./Instance/state
       (%Poly%producer_comsumer_example!FifoQueue.Instance. x)
      )
     ) (TYPE%core!option.Option. (GHOST $) (TYPE%producer_comsumer_example!FifoQueue.State.
       T&. T&
   ))))
   :pattern ((producer_comsumer_example!FifoQueue.Instance./Instance/state (%Poly%producer_comsumer_example!FifoQueue.Instance.
      x
     )
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.Instance. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.Instance./Instance/state_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Instance./Instance/state_invariant_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.Instance.)) (!
   (= (producer_comsumer_example!FifoQueue.Instance./Instance/location x) (producer_comsumer_example!FifoQueue.Instance./Instance/?location
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.Instance./Instance/location x))
   :qid internal_producer_comsumer_example!FifoQueue.Instance./Instance/location_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.Instance./Instance/location_accessor_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.Instance.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.Instance./Instance x)
    (height_lt (height (producer_comsumer_example!FifoQueue.Instance./Instance/send_sync
       x
      )
     ) (height (Poly%producer_comsumer_example!FifoQueue.Instance. x))
   ))
   :pattern ((height (producer_comsumer_example!FifoQueue.Instance./Instance/send_sync
      x
   )))
   :qid prelude_datatype_height_producer_comsumer_example!FifoQueue.Instance./Instance/send_sync
   :skolemid skolem_prelude_datatype_height_producer_comsumer_example!FifoQueue.Instance./Instance/send_sync
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.Instance.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.Instance./Instance x)
    (height_lt (height (Poly%core!option.Option. (producer_comsumer_example!FifoQueue.Instance./Instance/state
        x
      ))
     ) (height (Poly%producer_comsumer_example!FifoQueue.Instance. x))
   ))
   :pattern ((height (Poly%core!option.Option. (producer_comsumer_example!FifoQueue.Instance./Instance/state
       x
   ))))
   :qid prelude_datatype_height_producer_comsumer_example!FifoQueue.Instance./Instance/state
   :skolemid skolem_prelude_datatype_height_producer_comsumer_example!FifoQueue.Instance./Instance/state
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.head.)) (!
   (= x (%Poly%producer_comsumer_example!FifoQueue.head. (Poly%producer_comsumer_example!FifoQueue.head.
      x
   )))
   :pattern ((Poly%producer_comsumer_example!FifoQueue.head. x))
   :qid internal_producer_comsumer_example__FifoQueue__head_box_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__head_box_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.head. T&. T&))
    (= x (Poly%producer_comsumer_example!FifoQueue.head. (%Poly%producer_comsumer_example!FifoQueue.head.
       x
   ))))
   :pattern ((has_type x (TYPE%producer_comsumer_example!FifoQueue.head. T&. T&)))
   :qid internal_producer_comsumer_example__FifoQueue__head_unbox_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__head_unbox_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_dummy_instance! producer_comsumer_example!FifoQueue.Instance.)
   (_no_copy! vstd!state_machine_internal.NoCopy.)
  ) (!
   (=>
    (has_type (Poly%producer_comsumer_example!FifoQueue.Instance. _dummy_instance!) (TYPE%producer_comsumer_example!FifoQueue.Instance.
      T&. T&
    ))
    (has_type (Poly%producer_comsumer_example!FifoQueue.head. (producer_comsumer_example!FifoQueue.head./head
       _dummy_instance! _no_copy!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.head. T&. T&)
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!FifoQueue.head. (producer_comsumer_example!FifoQueue.head./head
       _dummy_instance! _no_copy!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.head. T&. T&)
   ))
   :qid internal_producer_comsumer_example!FifoQueue.head./head_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.head./head_constructor_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.head.)) (!
   (= (producer_comsumer_example!FifoQueue.head./head/dummy_instance x) (producer_comsumer_example!FifoQueue.head./head/?dummy_instance
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.head./head/dummy_instance x))
   :qid internal_producer_comsumer_example!FifoQueue.head./head/dummy_instance_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.head./head/dummy_instance_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.head. T&. T&))
    (has_type (Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.head./head/dummy_instance
       (%Poly%producer_comsumer_example!FifoQueue.head. x)
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Instance. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.head./head/dummy_instance (%Poly%producer_comsumer_example!FifoQueue.head.
      x
     )
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.head. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.head./head/dummy_instance_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.head./head/dummy_instance_invariant_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.head.)) (!
   (= (producer_comsumer_example!FifoQueue.head./head/no_copy x) (producer_comsumer_example!FifoQueue.head./head/?no_copy
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.head./head/no_copy x))
   :qid internal_producer_comsumer_example!FifoQueue.head./head/no_copy_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.head./head/no_copy_accessor_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.head.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.head./head x)
    (height_lt (height (Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.head./head/dummy_instance
        x
      ))
     ) (height (Poly%producer_comsumer_example!FifoQueue.head. x))
   ))
   :pattern ((height (Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.head./head/dummy_instance
       x
   ))))
   :qid prelude_datatype_height_producer_comsumer_example!FifoQueue.head./head/dummy_instance
   :skolemid skolem_prelude_datatype_height_producer_comsumer_example!FifoQueue.head./head/dummy_instance
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.tail.)) (!
   (= x (%Poly%producer_comsumer_example!FifoQueue.tail. (Poly%producer_comsumer_example!FifoQueue.tail.
      x
   )))
   :pattern ((Poly%producer_comsumer_example!FifoQueue.tail. x))
   :qid internal_producer_comsumer_example__FifoQueue__tail_box_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__tail_box_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.tail. T&. T&))
    (= x (Poly%producer_comsumer_example!FifoQueue.tail. (%Poly%producer_comsumer_example!FifoQueue.tail.
       x
   ))))
   :pattern ((has_type x (TYPE%producer_comsumer_example!FifoQueue.tail. T&. T&)))
   :qid internal_producer_comsumer_example__FifoQueue__tail_unbox_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__tail_unbox_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_dummy_instance! producer_comsumer_example!FifoQueue.Instance.)
   (_no_copy! vstd!state_machine_internal.NoCopy.)
  ) (!
   (=>
    (has_type (Poly%producer_comsumer_example!FifoQueue.Instance. _dummy_instance!) (TYPE%producer_comsumer_example!FifoQueue.Instance.
      T&. T&
    ))
    (has_type (Poly%producer_comsumer_example!FifoQueue.tail. (producer_comsumer_example!FifoQueue.tail./tail
       _dummy_instance! _no_copy!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.tail. T&. T&)
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!FifoQueue.tail. (producer_comsumer_example!FifoQueue.tail./tail
       _dummy_instance! _no_copy!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.tail. T&. T&)
   ))
   :qid internal_producer_comsumer_example!FifoQueue.tail./tail_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.tail./tail_constructor_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.tail.)) (!
   (= (producer_comsumer_example!FifoQueue.tail./tail/dummy_instance x) (producer_comsumer_example!FifoQueue.tail./tail/?dummy_instance
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.tail./tail/dummy_instance x))
   :qid internal_producer_comsumer_example!FifoQueue.tail./tail/dummy_instance_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.tail./tail/dummy_instance_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.tail. T&. T&))
    (has_type (Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.tail./tail/dummy_instance
       (%Poly%producer_comsumer_example!FifoQueue.tail. x)
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Instance. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.tail./tail/dummy_instance (%Poly%producer_comsumer_example!FifoQueue.tail.
      x
     )
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.tail. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.tail./tail/dummy_instance_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.tail./tail/dummy_instance_invariant_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.tail.)) (!
   (= (producer_comsumer_example!FifoQueue.tail./tail/no_copy x) (producer_comsumer_example!FifoQueue.tail./tail/?no_copy
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.tail./tail/no_copy x))
   :qid internal_producer_comsumer_example!FifoQueue.tail./tail/no_copy_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.tail./tail/no_copy_accessor_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.tail.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.tail./tail x)
    (height_lt (height (Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.tail./tail/dummy_instance
        x
      ))
     ) (height (Poly%producer_comsumer_example!FifoQueue.tail. x))
   ))
   :pattern ((height (Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.tail./tail/dummy_instance
       x
   ))))
   :qid prelude_datatype_height_producer_comsumer_example!FifoQueue.tail./tail/dummy_instance
   :skolemid skolem_prelude_datatype_height_producer_comsumer_example!FifoQueue.tail./tail/dummy_instance
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.producer.)) (!
   (= x (%Poly%producer_comsumer_example!FifoQueue.producer. (Poly%producer_comsumer_example!FifoQueue.producer.
      x
   )))
   :pattern ((Poly%producer_comsumer_example!FifoQueue.producer. x))
   :qid internal_producer_comsumer_example__FifoQueue__producer_box_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__producer_box_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.producer. T&. T&))
    (= x (Poly%producer_comsumer_example!FifoQueue.producer. (%Poly%producer_comsumer_example!FifoQueue.producer.
       x
   ))))
   :pattern ((has_type x (TYPE%producer_comsumer_example!FifoQueue.producer. T&. T&)))
   :qid internal_producer_comsumer_example__FifoQueue__producer_unbox_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__producer_unbox_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_dummy_instance! producer_comsumer_example!FifoQueue.Instance.)
   (_no_copy! vstd!state_machine_internal.NoCopy.)
  ) (!
   (=>
    (has_type (Poly%producer_comsumer_example!FifoQueue.Instance. _dummy_instance!) (TYPE%producer_comsumer_example!FifoQueue.Instance.
      T&. T&
    ))
    (has_type (Poly%producer_comsumer_example!FifoQueue.producer. (producer_comsumer_example!FifoQueue.producer./producer
       _dummy_instance! _no_copy!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.producer. T&. T&)
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!FifoQueue.producer. (producer_comsumer_example!FifoQueue.producer./producer
       _dummy_instance! _no_copy!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.producer. T&. T&)
   ))
   :qid internal_producer_comsumer_example!FifoQueue.producer./producer_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.producer./producer_constructor_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.producer.)) (!
   (= (producer_comsumer_example!FifoQueue.producer./producer/dummy_instance x) (producer_comsumer_example!FifoQueue.producer./producer/?dummy_instance
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.producer./producer/dummy_instance x))
   :qid internal_producer_comsumer_example!FifoQueue.producer./producer/dummy_instance_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.producer./producer/dummy_instance_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.producer. T&. T&))
    (has_type (Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.producer./producer/dummy_instance
       (%Poly%producer_comsumer_example!FifoQueue.producer. x)
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Instance. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.producer./producer/dummy_instance (%Poly%producer_comsumer_example!FifoQueue.producer.
      x
     )
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.producer. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.producer./producer/dummy_instance_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.producer./producer/dummy_instance_invariant_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.producer.)) (!
   (= (producer_comsumer_example!FifoQueue.producer./producer/no_copy x) (producer_comsumer_example!FifoQueue.producer./producer/?no_copy
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.producer./producer/no_copy x))
   :qid internal_producer_comsumer_example!FifoQueue.producer./producer/no_copy_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.producer./producer/no_copy_accessor_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.producer.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.producer./producer x)
    (height_lt (height (Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.producer./producer/dummy_instance
        x
      ))
     ) (height (Poly%producer_comsumer_example!FifoQueue.producer. x))
   ))
   :pattern ((height (Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.producer./producer/dummy_instance
       x
   ))))
   :qid prelude_datatype_height_producer_comsumer_example!FifoQueue.producer./producer/dummy_instance
   :skolemid skolem_prelude_datatype_height_producer_comsumer_example!FifoQueue.producer./producer/dummy_instance
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.consumer.)) (!
   (= x (%Poly%producer_comsumer_example!FifoQueue.consumer. (Poly%producer_comsumer_example!FifoQueue.consumer.
      x
   )))
   :pattern ((Poly%producer_comsumer_example!FifoQueue.consumer. x))
   :qid internal_producer_comsumer_example__FifoQueue__consumer_box_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__consumer_box_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.consumer. T&. T&))
    (= x (Poly%producer_comsumer_example!FifoQueue.consumer. (%Poly%producer_comsumer_example!FifoQueue.consumer.
       x
   ))))
   :pattern ((has_type x (TYPE%producer_comsumer_example!FifoQueue.consumer. T&. T&)))
   :qid internal_producer_comsumer_example__FifoQueue__consumer_unbox_axiom_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__consumer_unbox_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_dummy_instance! producer_comsumer_example!FifoQueue.Instance.)
   (_no_copy! vstd!state_machine_internal.NoCopy.)
  ) (!
   (=>
    (has_type (Poly%producer_comsumer_example!FifoQueue.Instance. _dummy_instance!) (TYPE%producer_comsumer_example!FifoQueue.Instance.
      T&. T&
    ))
    (has_type (Poly%producer_comsumer_example!FifoQueue.consumer. (producer_comsumer_example!FifoQueue.consumer./consumer
       _dummy_instance! _no_copy!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.consumer. T&. T&)
   ))
   :pattern ((has_type (Poly%producer_comsumer_example!FifoQueue.consumer. (producer_comsumer_example!FifoQueue.consumer./consumer
       _dummy_instance! _no_copy!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.consumer. T&. T&)
   ))
   :qid internal_producer_comsumer_example!FifoQueue.consumer./consumer_constructor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.consumer./consumer_constructor_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.consumer.)) (!
   (= (producer_comsumer_example!FifoQueue.consumer./consumer/dummy_instance x) (producer_comsumer_example!FifoQueue.consumer./consumer/?dummy_instance
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.consumer./consumer/dummy_instance x))
   :qid internal_producer_comsumer_example!FifoQueue.consumer./consumer/dummy_instance_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.consumer./consumer/dummy_instance_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%producer_comsumer_example!FifoQueue.consumer. T&. T&))
    (has_type (Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.consumer./consumer/dummy_instance
       (%Poly%producer_comsumer_example!FifoQueue.consumer. x)
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.Instance. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.consumer./consumer/dummy_instance (%Poly%producer_comsumer_example!FifoQueue.consumer.
      x
     )
    ) (has_type x (TYPE%producer_comsumer_example!FifoQueue.consumer. T&. T&))
   )
   :qid internal_producer_comsumer_example!FifoQueue.consumer./consumer/dummy_instance_invariant_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.consumer./consumer/dummy_instance_invariant_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.consumer.)) (!
   (= (producer_comsumer_example!FifoQueue.consumer./consumer/no_copy x) (producer_comsumer_example!FifoQueue.consumer./consumer/?no_copy
     x
   ))
   :pattern ((producer_comsumer_example!FifoQueue.consumer./consumer/no_copy x))
   :qid internal_producer_comsumer_example!FifoQueue.consumer./consumer/no_copy_accessor_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.consumer./consumer/no_copy_accessor_definition
)))
(assert
 (forall ((x producer_comsumer_example!FifoQueue.consumer.)) (!
   (=>
    (is-producer_comsumer_example!FifoQueue.consumer./consumer x)
    (height_lt (height (Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.consumer./consumer/dummy_instance
        x
      ))
     ) (height (Poly%producer_comsumer_example!FifoQueue.consumer. x))
   ))
   :pattern ((height (Poly%producer_comsumer_example!FifoQueue.Instance. (producer_comsumer_example!FifoQueue.consumer./consumer/dummy_instance
       x
   ))))
   :qid prelude_datatype_height_producer_comsumer_example!FifoQueue.consumer./consumer/dummy_instance
   :skolemid skolem_prelude_datatype_height_producer_comsumer_example!FifoQueue.consumer./consumer/dummy_instance
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
(assert
 (forall ((x tuple%1.)) (!
   (= x (%Poly%tuple%1. (Poly%tuple%1. x)))
   :pattern ((Poly%tuple%1. x))
   :qid internal_crate__tuple__1_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__1_box_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%tuple%1. T%0&. T%0&))
    (= x (Poly%tuple%1. (%Poly%tuple%1. x)))
   )
   :pattern ((has_type x (TYPE%tuple%1. T%0&. T%0&)))
   :qid internal_crate__tuple__1_unbox_axiom_definition
   :skolemid skolem_internal_crate__tuple__1_unbox_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (_0! Poly)) (!
   (=>
    (has_type _0! T%0&)
    (has_type (Poly%tuple%1. (tuple%1./tuple%1 _0!)) (TYPE%tuple%1. T%0&. T%0&))
   )
   :pattern ((has_type (Poly%tuple%1. (tuple%1./tuple%1 _0!)) (TYPE%tuple%1. T%0&. T%0&)))
   :qid internal_tuple__1./tuple__1_constructor_definition
   :skolemid skolem_internal_tuple__1./tuple__1_constructor_definition
)))
(assert
 (forall ((x tuple%1.)) (!
   (= (tuple%1./tuple%1/0 x) (tuple%1./tuple%1/?0 x))
   :pattern ((tuple%1./tuple%1/0 x))
   :qid internal_tuple__1./tuple__1/0_accessor_definition
   :skolemid skolem_internal_tuple__1./tuple__1/0_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%tuple%1. T%0&. T%0&))
    (has_type (tuple%1./tuple%1/0 (%Poly%tuple%1. x)) T%0&)
   )
   :pattern ((tuple%1./tuple%1/0 (%Poly%tuple%1. x)) (has_type x (TYPE%tuple%1. T%0&. T%0&)))
   :qid internal_tuple__1./tuple__1/0_invariant_definition
   :skolemid skolem_internal_tuple__1./tuple__1/0_invariant_definition
)))
(assert
 (forall ((x tuple%1.)) (!
   (=>
    (is-tuple%1./tuple%1 x)
    (height_lt (height (tuple%1./tuple%1/0 x)) (height (Poly%tuple%1. x)))
   )
   :pattern ((height (tuple%1./tuple%1/0 x)))
   :qid prelude_datatype_height_tuple%1./tuple%1/0
   :skolemid skolem_prelude_datatype_height_tuple%1./tuple%1/0
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (deep Bool) (x Poly) (y Poly)) (!
   (=>
    (and
     (has_type x (TYPE%tuple%1. T%0&. T%0&))
     (has_type y (TYPE%tuple%1. T%0&. T%0&))
     (ext_eq deep T%0& (tuple%1./tuple%1/0 (%Poly%tuple%1. x)) (tuple%1./tuple%1/0 (%Poly%tuple%1.
        y
    ))))
    (ext_eq deep (TYPE%tuple%1. T%0&. T%0&) x y)
   )
   :pattern ((ext_eq deep (TYPE%tuple%1. T%0&. T%0&) x y))
   :qid internal_tuple__1./tuple__1_ext_equal_definition
   :skolemid skolem_internal_tuple__1./tuple__1_ext_equal_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (= x (%Poly%tuple%2. (Poly%tuple%2. x)))
   :pattern ((Poly%tuple%2. x))
   :qid internal_crate__tuple__2_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__2_box_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
    (= x (Poly%tuple%2. (%Poly%tuple%2. x)))
   )
   :pattern ((has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&)))
   :qid internal_crate__tuple__2_unbox_axiom_definition
   :skolemid skolem_internal_crate__tuple__2_unbox_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (_0! Poly) (_1! Poly)) (!
   (=>
    (and
     (has_type _0! T%0&)
     (has_type _1! T%1&)
    )
    (has_type (Poly%tuple%2. (tuple%2./tuple%2 _0! _1!)) (TYPE%tuple%2. T%0&. T%0& T%1&.
      T%1&
   )))
   :pattern ((has_type (Poly%tuple%2. (tuple%2./tuple%2 _0! _1!)) (TYPE%tuple%2. T%0&.
      T%0& T%1&. T%1&
   )))
   :qid internal_tuple__2./tuple__2_constructor_definition
   :skolemid skolem_internal_tuple__2./tuple__2_constructor_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (= (tuple%2./tuple%2/0 x) (tuple%2./tuple%2/?0 x))
   :pattern ((tuple%2./tuple%2/0 x))
   :qid internal_tuple__2./tuple__2/0_accessor_definition
   :skolemid skolem_internal_tuple__2./tuple__2/0_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
    (has_type (tuple%2./tuple%2/0 (%Poly%tuple%2. x)) T%0&)
   )
   :pattern ((tuple%2./tuple%2/0 (%Poly%tuple%2. x)) (has_type x (TYPE%tuple%2. T%0&. T%0&
      T%1&. T%1&
   )))
   :qid internal_tuple__2./tuple__2/0_invariant_definition
   :skolemid skolem_internal_tuple__2./tuple__2/0_invariant_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (= (tuple%2./tuple%2/1 x) (tuple%2./tuple%2/?1 x))
   :pattern ((tuple%2./tuple%2/1 x))
   :qid internal_tuple__2./tuple__2/1_accessor_definition
   :skolemid skolem_internal_tuple__2./tuple__2/1_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
    (has_type (tuple%2./tuple%2/1 (%Poly%tuple%2. x)) T%1&)
   )
   :pattern ((tuple%2./tuple%2/1 (%Poly%tuple%2. x)) (has_type x (TYPE%tuple%2. T%0&. T%0&
      T%1&. T%1&
   )))
   :qid internal_tuple__2./tuple__2/1_invariant_definition
   :skolemid skolem_internal_tuple__2./tuple__2/1_invariant_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (=>
    (is-tuple%2./tuple%2 x)
    (height_lt (height (tuple%2./tuple%2/0 x)) (height (Poly%tuple%2. x)))
   )
   :pattern ((height (tuple%2./tuple%2/0 x)))
   :qid prelude_datatype_height_tuple%2./tuple%2/0
   :skolemid skolem_prelude_datatype_height_tuple%2./tuple%2/0
)))
(assert
 (forall ((x tuple%2.)) (!
   (=>
    (is-tuple%2./tuple%2 x)
    (height_lt (height (tuple%2./tuple%2/1 x)) (height (Poly%tuple%2. x)))
   )
   :pattern ((height (tuple%2./tuple%2/1 x)))
   :qid prelude_datatype_height_tuple%2./tuple%2/1
   :skolemid skolem_prelude_datatype_height_tuple%2./tuple%2/1
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (deep Bool) (x Poly) (y Poly))
  (!
   (=>
    (and
     (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
     (has_type y (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
     (ext_eq deep T%0& (tuple%2./tuple%2/0 (%Poly%tuple%2. x)) (tuple%2./tuple%2/0 (%Poly%tuple%2.
        y
     )))
     (ext_eq deep T%1& (tuple%2./tuple%2/1 (%Poly%tuple%2. x)) (tuple%2./tuple%2/1 (%Poly%tuple%2.
        y
    ))))
    (ext_eq deep (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&) x y)
   )
   :pattern ((ext_eq deep (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&) x y))
   :qid internal_tuple__2./tuple__2_ext_equal_definition
   :skolemid skolem_internal_tuple__2./tuple__2_ext_equal_definition
)))
(assert
 (forall ((x tuple%5.)) (!
   (= x (%Poly%tuple%5. (Poly%tuple%5. x)))
   :pattern ((Poly%tuple%5. x))
   :qid internal_crate__tuple__5_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__5_box_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (T%3&.
    Dcr
   ) (T%3& Type) (T%4&. Dcr) (T%4& Type) (x Poly)
  ) (!
   (=>
    (has_type x (TYPE%tuple%5. T%0&. T%0& T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&))
    (= x (Poly%tuple%5. (%Poly%tuple%5. x)))
   )
   :pattern ((has_type x (TYPE%tuple%5. T%0&. T%0& T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&.
      T%4&
   )))
   :qid internal_crate__tuple__5_unbox_axiom_definition
   :skolemid skolem_internal_crate__tuple__5_unbox_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (T%3&.
    Dcr
   ) (T%3& Type) (T%4&. Dcr) (T%4& Type) (_0! Poly) (_1! Poly) (_2! Poly) (_3! Poly)
   (_4! Poly)
  ) (!
   (=>
    (and
     (has_type _0! T%0&)
     (has_type _1! T%1&)
     (has_type _2! T%2&)
     (has_type _3! T%3&)
     (has_type _4! T%4&)
    )
    (has_type (Poly%tuple%5. (tuple%5./tuple%5 _0! _1! _2! _3! _4!)) (TYPE%tuple%5. T%0&.
      T%0& T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&
   )))
   :pattern ((has_type (Poly%tuple%5. (tuple%5./tuple%5 _0! _1! _2! _3! _4!)) (TYPE%tuple%5.
      T%0&. T%0& T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&
   )))
   :qid internal_tuple__5./tuple__5_constructor_definition
   :skolemid skolem_internal_tuple__5./tuple__5_constructor_definition
)))
(assert
 (forall ((x tuple%5.)) (!
   (= (tuple%5./tuple%5/0 x) (tuple%5./tuple%5/?0 x))
   :pattern ((tuple%5./tuple%5/0 x))
   :qid internal_tuple__5./tuple__5/0_accessor_definition
   :skolemid skolem_internal_tuple__5./tuple__5/0_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (T%3&.
    Dcr
   ) (T%3& Type) (T%4&. Dcr) (T%4& Type) (x Poly)
  ) (!
   (=>
    (has_type x (TYPE%tuple%5. T%0&. T%0& T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&))
    (has_type (tuple%5./tuple%5/0 (%Poly%tuple%5. x)) T%0&)
   )
   :pattern ((tuple%5./tuple%5/0 (%Poly%tuple%5. x)) (has_type x (TYPE%tuple%5. T%0&. T%0&
      T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&
   )))
   :qid internal_tuple__5./tuple__5/0_invariant_definition
   :skolemid skolem_internal_tuple__5./tuple__5/0_invariant_definition
)))
(assert
 (forall ((x tuple%5.)) (!
   (= (tuple%5./tuple%5/1 x) (tuple%5./tuple%5/?1 x))
   :pattern ((tuple%5./tuple%5/1 x))
   :qid internal_tuple__5./tuple__5/1_accessor_definition
   :skolemid skolem_internal_tuple__5./tuple__5/1_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (T%3&.
    Dcr
   ) (T%3& Type) (T%4&. Dcr) (T%4& Type) (x Poly)
  ) (!
   (=>
    (has_type x (TYPE%tuple%5. T%0&. T%0& T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&))
    (has_type (tuple%5./tuple%5/1 (%Poly%tuple%5. x)) T%1&)
   )
   :pattern ((tuple%5./tuple%5/1 (%Poly%tuple%5. x)) (has_type x (TYPE%tuple%5. T%0&. T%0&
      T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&
   )))
   :qid internal_tuple__5./tuple__5/1_invariant_definition
   :skolemid skolem_internal_tuple__5./tuple__5/1_invariant_definition
)))
(assert
 (forall ((x tuple%5.)) (!
   (= (tuple%5./tuple%5/2 x) (tuple%5./tuple%5/?2 x))
   :pattern ((tuple%5./tuple%5/2 x))
   :qid internal_tuple__5./tuple__5/2_accessor_definition
   :skolemid skolem_internal_tuple__5./tuple__5/2_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (T%3&.
    Dcr
   ) (T%3& Type) (T%4&. Dcr) (T%4& Type) (x Poly)
  ) (!
   (=>
    (has_type x (TYPE%tuple%5. T%0&. T%0& T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&))
    (has_type (tuple%5./tuple%5/2 (%Poly%tuple%5. x)) T%2&)
   )
   :pattern ((tuple%5./tuple%5/2 (%Poly%tuple%5. x)) (has_type x (TYPE%tuple%5. T%0&. T%0&
      T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&
   )))
   :qid internal_tuple__5./tuple__5/2_invariant_definition
   :skolemid skolem_internal_tuple__5./tuple__5/2_invariant_definition
)))
(assert
 (forall ((x tuple%5.)) (!
   (= (tuple%5./tuple%5/3 x) (tuple%5./tuple%5/?3 x))
   :pattern ((tuple%5./tuple%5/3 x))
   :qid internal_tuple__5./tuple__5/3_accessor_definition
   :skolemid skolem_internal_tuple__5./tuple__5/3_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (T%3&.
    Dcr
   ) (T%3& Type) (T%4&. Dcr) (T%4& Type) (x Poly)
  ) (!
   (=>
    (has_type x (TYPE%tuple%5. T%0&. T%0& T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&))
    (has_type (tuple%5./tuple%5/3 (%Poly%tuple%5. x)) T%3&)
   )
   :pattern ((tuple%5./tuple%5/3 (%Poly%tuple%5. x)) (has_type x (TYPE%tuple%5. T%0&. T%0&
      T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&
   )))
   :qid internal_tuple__5./tuple__5/3_invariant_definition
   :skolemid skolem_internal_tuple__5./tuple__5/3_invariant_definition
)))
(assert
 (forall ((x tuple%5.)) (!
   (= (tuple%5./tuple%5/4 x) (tuple%5./tuple%5/?4 x))
   :pattern ((tuple%5./tuple%5/4 x))
   :qid internal_tuple__5./tuple__5/4_accessor_definition
   :skolemid skolem_internal_tuple__5./tuple__5/4_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (T%3&.
    Dcr
   ) (T%3& Type) (T%4&. Dcr) (T%4& Type) (x Poly)
  ) (!
   (=>
    (has_type x (TYPE%tuple%5. T%0&. T%0& T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&))
    (has_type (tuple%5./tuple%5/4 (%Poly%tuple%5. x)) T%4&)
   )
   :pattern ((tuple%5./tuple%5/4 (%Poly%tuple%5. x)) (has_type x (TYPE%tuple%5. T%0&. T%0&
      T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&
   )))
   :qid internal_tuple__5./tuple__5/4_invariant_definition
   :skolemid skolem_internal_tuple__5./tuple__5/4_invariant_definition
)))
(assert
 (forall ((x tuple%5.)) (!
   (=>
    (is-tuple%5./tuple%5 x)
    (height_lt (height (tuple%5./tuple%5/0 x)) (height (Poly%tuple%5. x)))
   )
   :pattern ((height (tuple%5./tuple%5/0 x)))
   :qid prelude_datatype_height_tuple%5./tuple%5/0
   :skolemid skolem_prelude_datatype_height_tuple%5./tuple%5/0
)))
(assert
 (forall ((x tuple%5.)) (!
   (=>
    (is-tuple%5./tuple%5 x)
    (height_lt (height (tuple%5./tuple%5/1 x)) (height (Poly%tuple%5. x)))
   )
   :pattern ((height (tuple%5./tuple%5/1 x)))
   :qid prelude_datatype_height_tuple%5./tuple%5/1
   :skolemid skolem_prelude_datatype_height_tuple%5./tuple%5/1
)))
(assert
 (forall ((x tuple%5.)) (!
   (=>
    (is-tuple%5./tuple%5 x)
    (height_lt (height (tuple%5./tuple%5/2 x)) (height (Poly%tuple%5. x)))
   )
   :pattern ((height (tuple%5./tuple%5/2 x)))
   :qid prelude_datatype_height_tuple%5./tuple%5/2
   :skolemid skolem_prelude_datatype_height_tuple%5./tuple%5/2
)))
(assert
 (forall ((x tuple%5.)) (!
   (=>
    (is-tuple%5./tuple%5 x)
    (height_lt (height (tuple%5./tuple%5/3 x)) (height (Poly%tuple%5. x)))
   )
   :pattern ((height (tuple%5./tuple%5/3 x)))
   :qid prelude_datatype_height_tuple%5./tuple%5/3
   :skolemid skolem_prelude_datatype_height_tuple%5./tuple%5/3
)))
(assert
 (forall ((x tuple%5.)) (!
   (=>
    (is-tuple%5./tuple%5 x)
    (height_lt (height (tuple%5./tuple%5/4 x)) (height (Poly%tuple%5. x)))
   )
   :pattern ((height (tuple%5./tuple%5/4 x)))
   :qid prelude_datatype_height_tuple%5./tuple%5/4
   :skolemid skolem_prelude_datatype_height_tuple%5./tuple%5/4
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (T%3&.
    Dcr
   ) (T%3& Type) (T%4&. Dcr) (T%4& Type) (deep Bool) (x Poly) (y Poly)
  ) (!
   (=>
    (and
     (has_type x (TYPE%tuple%5. T%0&. T%0& T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&))
     (has_type y (TYPE%tuple%5. T%0&. T%0& T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&))
     (ext_eq deep T%0& (tuple%5./tuple%5/0 (%Poly%tuple%5. x)) (tuple%5./tuple%5/0 (%Poly%tuple%5.
        y
     )))
     (ext_eq deep T%1& (tuple%5./tuple%5/1 (%Poly%tuple%5. x)) (tuple%5./tuple%5/1 (%Poly%tuple%5.
        y
     )))
     (ext_eq deep T%2& (tuple%5./tuple%5/2 (%Poly%tuple%5. x)) (tuple%5./tuple%5/2 (%Poly%tuple%5.
        y
     )))
     (ext_eq deep T%3& (tuple%5./tuple%5/3 (%Poly%tuple%5. x)) (tuple%5./tuple%5/3 (%Poly%tuple%5.
        y
     )))
     (ext_eq deep T%4& (tuple%5./tuple%5/4 (%Poly%tuple%5. x)) (tuple%5./tuple%5/4 (%Poly%tuple%5.
        y
    ))))
    (ext_eq deep (TYPE%tuple%5. T%0&. T%0& T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&. T%4&)
     x y
   ))
   :pattern ((ext_eq deep (TYPE%tuple%5. T%0&. T%0& T%1&. T%1& T%2&. T%2& T%3&. T%3& T%4&.
      T%4&
     ) x y
   ))
   :qid internal_tuple__5./tuple__5_ext_equal_definition
   :skolemid skolem_internal_tuple__5./tuple__5_ext_equal_definition
)))

;; Traits
(declare-fun tr_bound%vstd!tokens.ValueToken. (Dcr Type Dcr Type) Bool)
(declare-fun tr_bound%vstd!tokens.UniqueValueToken. (Dcr Type Dcr Type) Bool)
(declare-fun tr_bound%core!clone.Clone. (Dcr Type) Bool)
(declare-fun tr_bound%core!alloc.Allocator. (Dcr Type) Bool)
(declare-fun tr_bound%vstd!std_specs.option.OptionAdditionalFns. (Dcr Type Dcr Type)
 Bool
)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (Value&. Dcr) (Value& Type)) (!
   (=>
    (tr_bound%vstd!tokens.ValueToken. Self%&. Self%& Value&. Value&)
    (and
     (sized Self%&.)
     (sized Value&.)
   ))
   :pattern ((tr_bound%vstd!tokens.ValueToken. Self%&. Self%& Value&. Value&))
   :qid internal_vstd__tokens__ValueToken_trait_type_bounds_definition
   :skolemid skolem_internal_vstd__tokens__ValueToken_trait_type_bounds_definition
)))
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (Value&. Dcr) (Value& Type)) (!
   (=>
    (tr_bound%vstd!tokens.UniqueValueToken. Self%&. Self%& Value&. Value&)
    (and
     (tr_bound%vstd!tokens.ValueToken. Self%&. Self%& Value&. Value&)
     (sized Value&.)
   ))
   :pattern ((tr_bound%vstd!tokens.UniqueValueToken. Self%&. Self%& Value&. Value&))
   :qid internal_vstd__tokens__UniqueValueToken_trait_type_bounds_definition
   :skolemid skolem_internal_vstd__tokens__UniqueValueToken_trait_type_bounds_definition
)))
(assert
 (forall ((Self%&. Dcr) (Self%& Type)) (!
   (=>
    (tr_bound%core!clone.Clone. Self%&. Self%&)
    (sized Self%&.)
   )
   :pattern ((tr_bound%core!clone.Clone. Self%&. Self%&))
   :qid internal_core__clone__Clone_trait_type_bounds_definition
   :skolemid skolem_internal_core__clone__Clone_trait_type_bounds_definition
)))
(assert
 (forall ((Self%&. Dcr) (Self%& Type)) (!
   true
   :pattern ((tr_bound%core!alloc.Allocator. Self%&. Self%&))
   :qid internal_core__alloc__Allocator_trait_type_bounds_definition
   :skolemid skolem_internal_core__alloc__Allocator_trait_type_bounds_definition
)))
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type)) (!
   (=>
    (tr_bound%vstd!std_specs.option.OptionAdditionalFns. Self%&. Self%& T&. T&)
    (and
     (sized Self%&.)
     (sized T&.)
   ))
   :pattern ((tr_bound%vstd!std_specs.option.OptionAdditionalFns. Self%&. Self%& T&. T&))
   :qid internal_vstd__std_specs__option__OptionAdditionalFns_trait_type_bounds_definition
   :skolemid skolem_internal_vstd__std_specs__option__OptionAdditionalFns_trait_type_bounds_definition
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

;; Function-Decl vstd::tokens::ValueToken::instance_id
(declare-fun vstd!tokens.ValueToken.instance_id.? (Dcr Type Dcr Type Poly) Poly)
(declare-fun vstd!tokens.ValueToken.instance_id%default%.? (Dcr Type Dcr Type Poly)
 Poly
)

;; Function-Decl vstd::tokens::ValueToken::value
(declare-fun vstd!tokens.ValueToken.value.? (Dcr Type Dcr Type Poly) Poly)
(declare-fun vstd!tokens.ValueToken.value%default%.? (Dcr Type Dcr Type Poly) Poly)

;; Function-Decl vstd::std_specs::option::OptionAdditionalFns::arrow_0
(declare-fun vstd!std_specs.option.OptionAdditionalFns.arrow_0.? (Dcr Type Dcr Type
  Poly
 ) Poly
)
(declare-fun vstd!std_specs.option.OptionAdditionalFns.arrow_0%default%.? (Dcr Type
  Dcr Type Poly
 ) Poly
)

;; Function-Decl vstd::std_specs::option::is_some
(declare-fun vstd!std_specs.option.is_some.? (Dcr Type Poly) Bool)

;; Function-Decl vstd::std_specs::option::is_none
(declare-fun vstd!std_specs.option.is_none.? (Dcr Type Poly) Bool)

;; Function-Decl vstd::std_specs::option::spec_unwrap
(declare-fun vstd!std_specs.option.spec_unwrap.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::pervasive::strictly_cloned
(declare-fun vstd!pervasive.strictly_cloned.? (Dcr Type Poly Poly) Bool)

;; Function-Decl vstd::pervasive::cloned
(declare-fun vstd!pervasive.cloned.? (Dcr Type Poly Poly) Bool)

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

;; Function-Decl producer_comsumer_example::FifoQueue::State::next_by
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.next_by.? (Dcr Type Poly
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

;; Function-Decl producer_comsumer_example::FifoQueue::State::init_by
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.init_by.? (Dcr Type Poly
  Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::init
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.init.? (Dcr Type Poly) Bool)

;; Function-Decl producer_comsumer_example::FifoQueue::Instance::id
(declare-fun producer_comsumer_example!FifoQueue.impl&%16.id.? (Dcr Type Poly) vstd!tokens.InstanceId.)

;; Function-Decl producer_comsumer_example::FifoQueue::Instance::backing_cells
(declare-fun producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? (Dcr Type
  Poly
 ) vstd!seq.Seq<vstd!cell.CellId.>.
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::len
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.len.? (Dcr Type Poly) Int)

;; Function-Decl producer_comsumer_example::FifoQueue::State::not_overlapping
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.not_overlapping.? (Dcr Type
  Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::in_bounds
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.in_bounds.? (Dcr Type Poly)
 Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::is_checked_out
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.is_checked_out.? (Dcr Type
  Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::in_active_range
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.in_active_range.? (Dcr Type
  Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::valid_storage_at_idx
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? (
  Dcr Type Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::valid_storage_all
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.valid_storage_all.? (Dcr
  Type Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::Step::arrow_produce_end_0
(declare-fun producer_comsumer_example!FifoQueue.impl&%0.arrow_produce_end_0.? (Dcr
  Type Poly
 ) Poly
)

;; Function-Decl producer_comsumer_example::FifoQueue::Step::arrow_consume_end_0
(declare-fun producer_comsumer_example!FifoQueue.impl&%0.arrow_consume_end_0.? (Dcr
  Type Poly
 ) Poly
)

;; Function-Decl producer_comsumer_example::FifoQueue::Step::arrow_dummy_to_use_type_params_0
(declare-fun producer_comsumer_example!FifoQueue.impl&%0.arrow_dummy_to_use_type_params_0.?
 (Dcr Type Poly) producer_comsumer_example!FifoQueue.State.
)

;; Function-Decl producer_comsumer_example::FifoQueue::Step::is_produce_start
(declare-fun producer_comsumer_example!FifoQueue.impl&%1.is_produce_start.? (Dcr Type
  Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::Step::is_produce_end
(declare-fun producer_comsumer_example!FifoQueue.impl&%1.is_produce_end.? (Dcr Type
  Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::Step::get_produce_end_0
(declare-fun producer_comsumer_example!FifoQueue.impl&%1.get_produce_end_0.? (Dcr Type
  Poly
 ) Poly
)

;; Function-Decl producer_comsumer_example::FifoQueue::Step::is_consume_start
(declare-fun producer_comsumer_example!FifoQueue.impl&%1.is_consume_start.? (Dcr Type
  Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::Step::is_consume_end
(declare-fun producer_comsumer_example!FifoQueue.impl&%1.is_consume_end.? (Dcr Type
  Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::Step::get_consume_end_0
(declare-fun producer_comsumer_example!FifoQueue.impl&%1.get_consume_end_0.? (Dcr Type
  Poly
 ) Poly
)

;; Function-Decl producer_comsumer_example::FifoQueue::Step::is_dummy_to_use_type_params
(declare-fun producer_comsumer_example!FifoQueue.impl&%1.is_dummy_to_use_type_params.?
 (Dcr Type Poly) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::Step::get_dummy_to_use_type_params_0
(declare-fun producer_comsumer_example!FifoQueue.impl&%1.get_dummy_to_use_type_params_0.?
 (Dcr Type Poly) producer_comsumer_example!FifoQueue.State.
)

;; Function-Decl producer_comsumer_example::FifoQueue::Config::arrow_1
(declare-fun producer_comsumer_example!FifoQueue.impl&%2.arrow_1.? (Dcr Type Poly)
 Poly
)

;; Function-Decl producer_comsumer_example::FifoQueue::Config::arrow_initialize_0
(declare-fun producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_0.? (Dcr
  Type Poly
 ) vstd!seq.Seq<vstd!cell.CellId.>.
)

;; Function-Decl producer_comsumer_example::FifoQueue::Config::arrow_initialize_1
(declare-fun producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_1.? (Dcr
  Type Poly
 ) Poly
)

;; Function-Decl producer_comsumer_example::FifoQueue::Config::arrow_dummy_to_use_type_params_0
(declare-fun producer_comsumer_example!FifoQueue.impl&%2.arrow_dummy_to_use_type_params_0.?
 (Dcr Type Poly) producer_comsumer_example!FifoQueue.State.
)

;; Function-Decl producer_comsumer_example::FifoQueue::Config::is_initialize
(declare-fun producer_comsumer_example!FifoQueue.impl&%3.is_initialize.? (Dcr Type
  Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::Config::get_initialize_0
(declare-fun producer_comsumer_example!FifoQueue.impl&%3.get_initialize_0.? (Dcr Type
  Poly
 ) vstd!seq.Seq<vstd!cell.CellId.>.
)

;; Function-Decl producer_comsumer_example::FifoQueue::Config::get_initialize_1
(declare-fun producer_comsumer_example!FifoQueue.impl&%3.get_initialize_1.? (Dcr Type
  Poly
 ) Poly
)

;; Function-Decl producer_comsumer_example::FifoQueue::Config::is_dummy_to_use_type_params
(declare-fun producer_comsumer_example!FifoQueue.impl&%3.is_dummy_to_use_type_params.?
 (Dcr Type Poly) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::Config::get_dummy_to_use_type_params_0
(declare-fun producer_comsumer_example!FifoQueue.impl&%3.get_dummy_to_use_type_params_0.?
 (Dcr Type Poly) producer_comsumer_example!FifoQueue.State.
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::initialize_enabled
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.initialize_enabled.? (Dcr
  Type Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::produce_start_strong
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.produce_start_strong.? (
  Dcr Type Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::produce_start_enabled
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.produce_start_enabled.?
 (Dcr Type Poly) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::produce_end_strong
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.produce_end_strong.? (Dcr
  Type Poly Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::produce_end_enabled
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.produce_end_enabled.? (Dcr
  Type Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::consume_start_strong
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.consume_start_strong.? (
  Dcr Type Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::consume_start_enabled
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.consume_start_enabled.?
 (Dcr Type Poly) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::consume_end_strong
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.consume_end_strong.? (Dcr
  Type Poly Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::consume_end_enabled
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.consume_end_enabled.? (Dcr
  Type Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::next_strong_by
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.next_strong_by.? (Dcr Type
  Poly Poly Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::next_strong
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.next_strong.? (Dcr Type Poly
  Poly
 ) Bool
)

;; Function-Decl producer_comsumer_example::FifoQueue::State::invariant
(declare-fun producer_comsumer_example!FifoQueue.impl&%19.invariant.? (Dcr Type Poly)
 Bool
)

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

;; Function-Axioms vstd::tokens::ValueToken::instance_id
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (Value&. Dcr) (Value& Type) (self! Poly)) (!
   (=>
    (has_type self! Self%&)
    (has_type (vstd!tokens.ValueToken.instance_id.? Self%&. Self%& Value&. Value& self!)
     TYPE%vstd!tokens.InstanceId.
   ))
   :pattern ((vstd!tokens.ValueToken.instance_id.? Self%&. Self%& Value&. Value& self!))
   :qid internal_vstd!tokens.ValueToken.instance_id.?_pre_post_definition
   :skolemid skolem_internal_vstd!tokens.ValueToken.instance_id.?_pre_post_definition
)))

;; Function-Axioms vstd::tokens::ValueToken::value
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (Value&. Dcr) (Value& Type) (self! Poly)) (!
   (=>
    (has_type self! Self%&)
    (has_type (vstd!tokens.ValueToken.value.? Self%&. Self%& Value&. Value& self!) Value&)
   )
   :pattern ((vstd!tokens.ValueToken.value.? Self%&. Self%& Value&. Value& self!))
   :qid internal_vstd!tokens.ValueToken.value.?_pre_post_definition
   :skolemid skolem_internal_vstd!tokens.ValueToken.value.?_pre_post_definition
)))

;; Function-Specs vstd::tokens::ValueToken::agree
(declare-fun req%vstd!tokens.ValueToken.agree. (Dcr Type Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%4 Bool)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (Value&. Dcr) (Value& Type) (self! Poly) (other!
    Poly
   )
  ) (!
   (= (req%vstd!tokens.ValueToken.agree. Self%&. Self%& Value&. Value& self! other!)
    (=>
     %%global_location_label%%4
     (= (vstd!tokens.ValueToken.instance_id.? Self%&. Self%& Value&. Value& self!) (vstd!tokens.ValueToken.instance_id.?
       Self%&. Self%& Value&. Value& other!
   ))))
   :pattern ((req%vstd!tokens.ValueToken.agree. Self%&. Self%& Value&. Value& self! other!))
   :qid internal_req__vstd!tokens.ValueToken.agree._definition
   :skolemid skolem_internal_req__vstd!tokens.ValueToken.agree._definition
)))
(declare-fun ens%vstd!tokens.ValueToken.agree. (Dcr Type Dcr Type Poly Poly) Bool)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (Value&. Dcr) (Value& Type) (self! Poly) (other!
    Poly
   )
  ) (!
   (= (ens%vstd!tokens.ValueToken.agree. Self%&. Self%& Value&. Value& self! other!)
    (= (vstd!tokens.ValueToken.value.? Self%&. Self%& Value&. Value& self!) (vstd!tokens.ValueToken.value.?
      Self%&. Self%& Value&. Value& other!
   )))
   :pattern ((ens%vstd!tokens.ValueToken.agree. Self%&. Self%& Value&. Value& self! other!))
   :qid internal_ens__vstd!tokens.ValueToken.agree._definition
   :skolemid skolem_internal_ens__vstd!tokens.ValueToken.agree._definition
)))

;; Function-Specs vstd::tokens::ValueToken::arbitrary
(declare-fun ens%vstd!tokens.ValueToken.arbitrary. (Dcr Type Dcr Type Poly) Bool)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (Value&. Dcr) (Value& Type) (%return! Poly))
  (!
   (= (ens%vstd!tokens.ValueToken.arbitrary. Self%&. Self%& Value&. Value& %return!)
    (has_type %return! Self%&)
   )
   :pattern ((ens%vstd!tokens.ValueToken.arbitrary. Self%&. Self%& Value&. Value& %return!))
   :qid internal_ens__vstd!tokens.ValueToken.arbitrary._definition
   :skolemid skolem_internal_ens__vstd!tokens.ValueToken.arbitrary._definition
)))

;; Function-Specs vstd::tokens::UniqueValueToken::unique
(declare-fun ens%vstd!tokens.UniqueValueToken.unique. (Dcr Type Dcr Type Poly Poly
  Poly
 ) Bool
)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (Value&. Dcr) (Value& Type) (pre%self! Poly) (
    self! Poly
   ) (other! Poly)
  ) (!
   (= (ens%vstd!tokens.UniqueValueToken.unique. Self%&. Self%& Value&. Value& pre%self!
     self! other!
    ) (and
     (has_type self! Self%&)
     (not (= (vstd!tokens.ValueToken.instance_id.? Self%&. Self%& Value&. Value& self!)
       (vstd!tokens.ValueToken.instance_id.? Self%&. Self%& Value&. Value& other!)
     ))
     (= self! pre%self!)
   ))
   :pattern ((ens%vstd!tokens.UniqueValueToken.unique. Self%&. Self%& Value&. Value& pre%self!
     self! other!
   ))
   :qid internal_ens__vstd!tokens.UniqueValueToken.unique._definition
   :skolemid skolem_internal_ens__vstd!tokens.UniqueValueToken.unique._definition
)))

;; Function-Specs core::clone::Clone::clone
(declare-fun ens%core!clone.Clone.clone. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (self! Poly) (%return! Poly)) (!
   (= (ens%core!clone.Clone.clone. Self%&. Self%& self! %return!) (has_type %return! Self%&))
   :pattern ((ens%core!clone.Clone.clone. Self%&. Self%& self! %return!))
   :qid internal_ens__core!clone.Clone.clone._definition
   :skolemid skolem_internal_ens__core!clone.Clone.clone._definition
)))
(assert
 (forall ((closure%$ Poly) (Self%&. Dcr) (Self%& Type)) (!
   (=>
    (has_type closure%$ (TYPE%tuple%1. (REF Self%&.) Self%&))
    (=>
     (let
      ((self$ (tuple%1./tuple%1/0 (%Poly%tuple%1. closure%$))))
      true
     )
     (closure_req (FNDEF%core!clone.Clone.clone. Self%&. Self%&) (DST (REF Self%&.)) (TYPE%tuple%1.
       (REF Self%&.) Self%&
      ) (F fndef_singleton) closure%$
   )))
   :pattern ((closure_req (FNDEF%core!clone.Clone.clone. Self%&. Self%&) (DST (REF Self%&.))
     (TYPE%tuple%1. (REF Self%&.) Self%&) (F fndef_singleton) closure%$
   ))
   :qid user_core__clone__Clone__clone_26
   :skolemid skolem_user_core__clone__Clone__clone_26
)))

;; Function-Specs core::clone::impls::impl&%21::clone
(declare-fun ens%core!clone.impls.impl&%21.clone. (Poly Poly) Bool)
(assert
 (forall ((b! Poly) (%return! Poly)) (!
   (= (ens%core!clone.impls.impl&%21.clone. b! %return!) (and
     (ens%core!clone.Clone.clone. $ BOOL b! %return!)
     (= %return! b!)
   ))
   :pattern ((ens%core!clone.impls.impl&%21.clone. b! %return!))
   :qid internal_ens__core!clone.impls.impl&__21.clone._definition
   :skolemid skolem_internal_ens__core!clone.impls.impl&__21.clone._definition
)))
(assert
 (forall ((closure%$ Poly) (%return$ Poly)) (!
   (=>
    (and
     (has_type closure%$ (TYPE%tuple%1. (REF $) BOOL))
     (has_type %return$ BOOL)
    )
    (=>
     (closure_ens (FNDEF%core!clone.Clone.clone. $ BOOL) (DST (REF $)) (TYPE%tuple%1. (REF
        $
       ) BOOL
      ) (F fndef_singleton) closure%$ %return$
     )
     (let
      ((b$ (%B (tuple%1./tuple%1/0 (%Poly%tuple%1. closure%$)))))
      (= (%B %return$) b$)
   )))
   :pattern ((closure_ens (FNDEF%core!clone.Clone.clone. $ BOOL) (DST (REF $)) (TYPE%tuple%1.
      (REF $) BOOL
     ) (F fndef_singleton) closure%$ %return$
   ))
   :qid user_core__clone__impls__impl&%21__clone_27
   :skolemid skolem_user_core__clone__impls__impl&%21__clone_27
)))

;; Function-Specs core::clone::impls::impl&%3::clone
(declare-fun ens%core!clone.impls.impl&%3.clone. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (b! Poly) (res! Poly)) (!
   (= (ens%core!clone.impls.impl&%3.clone. T&. T& b! res!) (and
     (ens%core!clone.Clone.clone. (REF T&.) T& b! res!)
     (= res! b!)
   ))
   :pattern ((ens%core!clone.impls.impl&%3.clone. T&. T& b! res!))
   :qid internal_ens__core!clone.impls.impl&__3.clone._definition
   :skolemid skolem_internal_ens__core!clone.impls.impl&__3.clone._definition
)))
(assert
 (forall ((closure%$ Poly) (res$ Poly) (T&. Dcr) (T& Type)) (!
   (=>
    (and
     (has_type closure%$ (TYPE%tuple%1. (REF (REF T&.)) T&))
     (has_type res$ T&)
    )
    (=>
     (closure_ens (FNDEF%core!clone.Clone.clone. (REF T&.) T&) (DST (REF (REF T&.))) (TYPE%tuple%1.
       (REF (REF T&.)) T&
      ) (F fndef_singleton) closure%$ res$
     )
     (let
      ((b$ (tuple%1./tuple%1/0 (%Poly%tuple%1. closure%$))))
      (= res$ b$)
   )))
   :pattern ((closure_ens (FNDEF%core!clone.Clone.clone. (REF T&.) T&) (DST (REF (REF T&.)))
     (TYPE%tuple%1. (REF (REF T&.)) T&) (F fndef_singleton) closure%$ res$
   ))
   :qid user_core__clone__impls__impl&%3__clone_28
   :skolemid skolem_user_core__clone__impls__impl&%3__clone_28
)))

;; Function-Specs builtin::impl&%5::clone
(declare-fun ens%builtin!impl&%5.clone. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (b! Poly) (res! Poly)) (!
   (= (ens%builtin!impl&%5.clone. T&. T& b! res!) (and
     (ens%core!clone.Clone.clone. (TRACKED T&.) T& b! res!)
     (= res! b!)
   ))
   :pattern ((ens%builtin!impl&%5.clone. T&. T& b! res!))
   :qid internal_ens__builtin!impl&__5.clone._definition
   :skolemid skolem_internal_ens__builtin!impl&__5.clone._definition
)))
(assert
 (forall ((closure%$ Poly) (res$ Poly) (T&. Dcr) (T& Type)) (!
   (=>
    (and
     (has_type closure%$ (TYPE%tuple%1. (REF (TRACKED T&.)) T&))
     (has_type res$ T&)
    )
    (=>
     (closure_ens (FNDEF%core!clone.Clone.clone. (TRACKED T&.) T&) (DST (REF (TRACKED T&.)))
      (TYPE%tuple%1. (REF (TRACKED T&.)) T&) (F fndef_singleton) closure%$ res$
     )
     (let
      ((b$ (tuple%1./tuple%1/0 (%Poly%tuple%1. closure%$))))
      (= res$ b$)
   )))
   :pattern ((closure_ens (FNDEF%core!clone.Clone.clone. (TRACKED T&.) T&) (DST (REF (TRACKED
        T&.
      ))
     ) (TYPE%tuple%1. (REF (TRACKED T&.)) T&) (F fndef_singleton) closure%$ res$
   ))
   :qid user_builtin__impl&%5__clone_29
   :skolemid skolem_user_builtin__impl&%5__clone_29
)))

;; Function-Specs builtin::impl&%3::clone
(declare-fun ens%builtin!impl&%3.clone. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (b! Poly) (res! Poly)) (!
   (= (ens%builtin!impl&%3.clone. T&. T& b! res!) (and
     (ens%core!clone.Clone.clone. (GHOST T&.) T& b! res!)
     (= res! b!)
   ))
   :pattern ((ens%builtin!impl&%3.clone. T&. T& b! res!))
   :qid internal_ens__builtin!impl&__3.clone._definition
   :skolemid skolem_internal_ens__builtin!impl&__3.clone._definition
)))
(assert
 (forall ((closure%$ Poly) (res$ Poly) (T&. Dcr) (T& Type)) (!
   (=>
    (and
     (has_type closure%$ (TYPE%tuple%1. (REF (GHOST T&.)) T&))
     (has_type res$ T&)
    )
    (=>
     (closure_ens (FNDEF%core!clone.Clone.clone. (GHOST T&.) T&) (DST (REF (GHOST T&.)))
      (TYPE%tuple%1. (REF (GHOST T&.)) T&) (F fndef_singleton) closure%$ res$
     )
     (let
      ((b$ (tuple%1./tuple%1/0 (%Poly%tuple%1. closure%$))))
      (= res$ b$)
   )))
   :pattern ((closure_ens (FNDEF%core!clone.Clone.clone. (GHOST T&.) T&) (DST (REF (GHOST
        T&.
      ))
     ) (TYPE%tuple%1. (REF (GHOST T&.)) T&) (F fndef_singleton) closure%$ res$
   ))
   :qid user_builtin__impl&%3__clone_30
   :skolemid skolem_user_builtin__impl&%3__clone_30
)))

;; Function-Axioms vstd::std_specs::option::OptionAdditionalFns::arrow_0
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! Self%&)
    (has_type (vstd!std_specs.option.OptionAdditionalFns.arrow_0.? Self%&. Self%& T&. T&
      self!
     ) T&
   ))
   :pattern ((vstd!std_specs.option.OptionAdditionalFns.arrow_0.? Self%&. Self%& T&. T&
     self!
   ))
   :qid internal_vstd!std_specs.option.OptionAdditionalFns.arrow_0.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.option.OptionAdditionalFns.arrow_0.?_pre_post_definition
)))

;; Function-Axioms vstd::std_specs::option::is_some
(assert
 (fuel_bool_default fuel%vstd!std_specs.option.is_some.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.option.is_some.)
  (forall ((T&. Dcr) (T& Type) (option! Poly)) (!
    (= (vstd!std_specs.option.is_some.? T&. T& option!) (is-core!option.Option./Some (%Poly%core!option.Option.
       option!
    )))
    :pattern ((vstd!std_specs.option.is_some.? T&. T& option!))
    :qid internal_vstd!std_specs.option.is_some.?_definition
    :skolemid skolem_internal_vstd!std_specs.option.is_some.?_definition
))))

;; Function-Axioms vstd::std_specs::option::is_none
(assert
 (fuel_bool_default fuel%vstd!std_specs.option.is_none.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.option.is_none.)
  (forall ((T&. Dcr) (T& Type) (option! Poly)) (!
    (= (vstd!std_specs.option.is_none.? T&. T& option!) (is-core!option.Option./None (%Poly%core!option.Option.
       option!
    )))
    :pattern ((vstd!std_specs.option.is_none.? T&. T& option!))
    :qid internal_vstd!std_specs.option.is_none.?_definition
    :skolemid skolem_internal_vstd!std_specs.option.is_none.?_definition
))))

;; Function-Axioms vstd::std_specs::option::impl&%2::arrow_0
(assert
 (fuel_bool_default fuel%vstd!std_specs.option.impl&%2.arrow_0.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.option.impl&%2.arrow_0.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (=>
     (sized T&.)
     (= (vstd!std_specs.option.OptionAdditionalFns.arrow_0.? $ (TYPE%core!option.Option.
        T&. T&
       ) T&. T& self!
      ) (core!option.Option./Some/0 T&. T& (%Poly%core!option.Option. self!))
    ))
    :pattern ((vstd!std_specs.option.OptionAdditionalFns.arrow_0.? $ (TYPE%core!option.Option.
       T&. T&
      ) T&. T& self!
    ))
    :qid internal_vstd!std_specs.option.OptionAdditionalFns.arrow_0.?_definition
    :skolemid skolem_internal_vstd!std_specs.option.OptionAdditionalFns.arrow_0.?_definition
))))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%vstd!std_specs.option.OptionAdditionalFns. $ (TYPE%core!option.Option. T&.
      T&
     ) T&. T&
   ))
   :pattern ((tr_bound%vstd!std_specs.option.OptionAdditionalFns. $ (TYPE%core!option.Option.
      T&. T&
     ) T&. T&
   ))
   :qid internal_vstd__std_specs__option__impl&__2_trait_impl_definition
   :skolemid skolem_internal_vstd__std_specs__option__impl&__2_trait_impl_definition
)))

;; Function-Specs vstd::std_specs::option::spec_unwrap
(declare-fun req%vstd!std_specs.option.spec_unwrap. (Dcr Type Poly) Bool)
(declare-const %%global_location_label%%5 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (option! Poly)) (!
   (= (req%vstd!std_specs.option.spec_unwrap. T&. T& option!) (=>
     %%global_location_label%%5
     (is-core!option.Option./Some (%Poly%core!option.Option. option!))
   ))
   :pattern ((req%vstd!std_specs.option.spec_unwrap. T&. T& option!))
   :qid internal_req__vstd!std_specs.option.spec_unwrap._definition
   :skolemid skolem_internal_req__vstd!std_specs.option.spec_unwrap._definition
)))

;; Function-Axioms vstd::std_specs::option::spec_unwrap
(assert
 (fuel_bool_default fuel%vstd!std_specs.option.spec_unwrap.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.option.spec_unwrap.)
  (forall ((T&. Dcr) (T& Type) (option! Poly)) (!
    (= (vstd!std_specs.option.spec_unwrap.? T&. T& option!) (core!option.Option./Some/0
      T&. T& (%Poly%core!option.Option. option!)
    ))
    :pattern ((vstd!std_specs.option.spec_unwrap.? T&. T& option!))
    :qid internal_vstd!std_specs.option.spec_unwrap.?_definition
    :skolemid skolem_internal_vstd!std_specs.option.spec_unwrap.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (option! Poly)) (!
   (=>
    (has_type option! (TYPE%core!option.Option. T&. T&))
    (has_type (vstd!std_specs.option.spec_unwrap.? T&. T& option!) T&)
   )
   :pattern ((vstd!std_specs.option.spec_unwrap.? T&. T& option!))
   :qid internal_vstd!std_specs.option.spec_unwrap.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.option.spec_unwrap.?_pre_post_definition
)))

;; Function-Axioms vstd::pervasive::strictly_cloned
(assert
 (fuel_bool_default fuel%vstd!pervasive.strictly_cloned.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!pervasive.strictly_cloned.)
  (forall ((T&. Dcr) (T& Type) (a! Poly) (b! Poly)) (!
    (= (vstd!pervasive.strictly_cloned.? T&. T& a! b!) (closure_ens (FNDEF%core!clone.Clone.clone.
       T&. T&
      ) (DST (REF T&.)) (TYPE%tuple%1. (REF T&.) T&) (F fndef_singleton) (Poly%tuple%1.
       (tuple%1./tuple%1 a!)
      ) b!
    ))
    :pattern ((vstd!pervasive.strictly_cloned.? T&. T& a! b!))
    :qid internal_vstd!pervasive.strictly_cloned.?_definition
    :skolemid skolem_internal_vstd!pervasive.strictly_cloned.?_definition
))))

;; Function-Axioms vstd::pervasive::cloned
(assert
 (fuel_bool_default fuel%vstd!pervasive.cloned.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!pervasive.cloned.)
  (forall ((T&. Dcr) (T& Type) (a! Poly) (b! Poly)) (!
    (= (vstd!pervasive.cloned.? T&. T& a! b!) (or
      (vstd!pervasive.strictly_cloned.? T&. T& a! b!)
      (= a! b!)
    ))
    :pattern ((vstd!pervasive.cloned.? T&. T& a! b!))
    :qid internal_vstd!pervasive.cloned.?_definition
    :skolemid skolem_internal_vstd!pervasive.cloned.?_definition
))))

;; Function-Specs core::option::impl&%5::clone
(declare-fun ens%core!option.impl&%5.clone. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (opt! Poly) (res! Poly)) (!
   (= (ens%core!option.impl&%5.clone. T&. T& opt! res!) (and
     (ens%core!clone.Clone.clone. $ (TYPE%core!option.Option. T&. T&) opt! res!)
     (=>
      (is-core!option.Option./None (%Poly%core!option.Option. opt!))
      (is-core!option.Option./None (%Poly%core!option.Option. res!))
     )
     (=>
      (is-core!option.Option./Some (%Poly%core!option.Option. opt!))
      (and
       (is-core!option.Option./Some (%Poly%core!option.Option. res!))
       (vstd!pervasive.cloned.? T&. T& (core!option.Option./Some/0 T&. T& (%Poly%core!option.Option.
          opt!
         )
        ) (core!option.Option./Some/0 T&. T& (%Poly%core!option.Option. res!))
   )))))
   :pattern ((ens%core!option.impl&%5.clone. T&. T& opt! res!))
   :qid internal_ens__core!option.impl&__5.clone._definition
   :skolemid skolem_internal_ens__core!option.impl&__5.clone._definition
)))
(assert
 (forall ((closure%$ Poly) (res$ Poly) (T&. Dcr) (T& Type)) (!
   (=>
    (and
     (has_type closure%$ (TYPE%tuple%1. (REF $) (TYPE%core!option.Option. T&. T&)))
     (has_type res$ (TYPE%core!option.Option. T&. T&))
    )
    (=>
     (closure_ens (FNDEF%core!clone.Clone.clone. $ (TYPE%core!option.Option. T&. T&)) (
       DST (REF $)
      ) (TYPE%tuple%1. (REF $) (TYPE%core!option.Option. T&. T&)) (F fndef_singleton) closure%$
      res$
     )
     (let
      ((opt$ (%Poly%core!option.Option. (tuple%1./tuple%1/0 (%Poly%tuple%1. closure%$)))))
      (and
       (=>
        (is-core!option.Option./None opt$)
        (is-core!option.Option./None (%Poly%core!option.Option. res$))
       )
       (=>
        (is-core!option.Option./Some opt$)
        (and
         (is-core!option.Option./Some (%Poly%core!option.Option. res$))
         (vstd!pervasive.cloned.? T&. T& (core!option.Option./Some/0 T&. T& (%Poly%core!option.Option.
            (Poly%core!option.Option. opt$)
           )
          ) (core!option.Option./Some/0 T&. T& (%Poly%core!option.Option. res$))
   )))))))
   :pattern ((closure_ens (FNDEF%core!clone.Clone.clone. $ (TYPE%core!option.Option. T&.
       T&
      )
     ) (DST (REF $)) (TYPE%tuple%1. (REF $) (TYPE%core!option.Option. T&. T&)) (F fndef_singleton)
     closure%$ res$
   ))
   :qid user_core__option__impl&%5__clone_31
   :skolemid skolem_user_core__option__impl&%5__clone_31
)))

;; Function-Specs alloc::boxed::impl&%12::clone
(declare-fun ens%alloc!boxed.impl&%12.clone. (Dcr Type Dcr Type Poly Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type) (b! Poly) (res! Poly)) (!
   (= (ens%alloc!boxed.impl&%12.clone. T&. T& A&. A& b! res!) (and
     (ens%core!clone.Clone.clone. (BOX A&. A& T&.) T& b! res!)
     (vstd!pervasive.cloned.? T&. T& b! res!)
   ))
   :pattern ((ens%alloc!boxed.impl&%12.clone. T&. T& A&. A& b! res!))
   :qid internal_ens__alloc!boxed.impl&__12.clone._definition
   :skolemid skolem_internal_ens__alloc!boxed.impl&__12.clone._definition
)))
(assert
 (forall ((closure%$ Poly) (res$ Poly) (T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (=>
    (and
     (has_type closure%$ (TYPE%tuple%1. (REF (BOX A&. A& T&.)) T&))
     (has_type res$ T&)
    )
    (=>
     (closure_ens (FNDEF%core!clone.Clone.clone. (BOX A&. A& T&.) T&) (DST (REF (BOX A&. A&
         T&.
       ))
      ) (TYPE%tuple%1. (REF (BOX A&. A& T&.)) T&) (F fndef_singleton) closure%$ res$
     )
     (let
      ((b$ (tuple%1./tuple%1/0 (%Poly%tuple%1. closure%$))))
      (vstd!pervasive.cloned.? T&. T& b$ res$)
   )))
   :pattern ((closure_ens (FNDEF%core!clone.Clone.clone. (BOX A&. A& T&.) T&) (DST (REF
       (BOX A&. A& T&.)
      )
     ) (TYPE%tuple%1. (REF (BOX A&. A& T&.)) T&) (F fndef_singleton) closure%$ res$
   ))
   :qid user_alloc__boxed__impl&%12__clone_32
   :skolemid skolem_user_alloc__boxed__impl&%12__clone_32
)))

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

;; Function-Specs vstd::state_machine_internal::assert_safety
(declare-fun req%vstd!state_machine_internal.assert_safety. (Bool) Bool)
(assert
 (forall ((b! Bool)) (!
   (= (req%vstd!state_machine_internal.assert_safety. b!) b!)
   :pattern ((req%vstd!state_machine_internal.assert_safety. b!))
   :qid internal_req__vstd!state_machine_internal.assert_safety._definition
   :skolemid skolem_internal_req__vstd!state_machine_internal.assert_safety._definition
)))
(declare-fun ens%vstd!state_machine_internal.assert_safety. (Bool) Bool)
(assert
 (forall ((b! Bool)) (!
   (= (ens%vstd!state_machine_internal.assert_safety. b!) b!)
   :pattern ((ens%vstd!state_machine_internal.assert_safety. b!))
   :qid internal_ens__vstd!state_machine_internal.assert_safety._definition
   :skolemid skolem_internal_ens__vstd!state_machine_internal.assert_safety._definition
)))

;; Function-Specs vstd::state_machine_internal::assert_withdraw_map
(declare-fun req%vstd!state_machine_internal.assert_withdraw_map. (Bool) Bool)
(assert
 (forall ((b! Bool)) (!
   (= (req%vstd!state_machine_internal.assert_withdraw_map. b!) b!)
   :pattern ((req%vstd!state_machine_internal.assert_withdraw_map. b!))
   :qid internal_req__vstd!state_machine_internal.assert_withdraw_map._definition
   :skolemid skolem_internal_req__vstd!state_machine_internal.assert_withdraw_map._definition
)))
(declare-fun ens%vstd!state_machine_internal.assert_withdraw_map. (Bool) Bool)
(assert
 (forall ((b! Bool)) (!
   (= (ens%vstd!state_machine_internal.assert_withdraw_map. b!) b!)
   :pattern ((ens%vstd!state_machine_internal.assert_withdraw_map. b!))
   :qid internal_ens__vstd!state_machine_internal.assert_withdraw_map._definition
   :skolemid skolem_internal_ens__vstd!state_machine_internal.assert_withdraw_map._definition
)))

;; Function-Specs vstd::state_machine_internal::assert_deposit_map
(declare-fun req%vstd!state_machine_internal.assert_deposit_map. (Bool) Bool)
(assert
 (forall ((b! Bool)) (!
   (= (req%vstd!state_machine_internal.assert_deposit_map. b!) b!)
   :pattern ((req%vstd!state_machine_internal.assert_deposit_map. b!))
   :qid internal_req__vstd!state_machine_internal.assert_deposit_map._definition
   :skolemid skolem_internal_req__vstd!state_machine_internal.assert_deposit_map._definition
)))
(declare-fun ens%vstd!state_machine_internal.assert_deposit_map. (Bool) Bool)
(assert
 (forall ((b! Bool)) (!
   (= (ens%vstd!state_machine_internal.assert_deposit_map. b!) b!)
   :pattern ((ens%vstd!state_machine_internal.assert_deposit_map. b!))
   :qid internal_ens__vstd!state_machine_internal.assert_deposit_map._definition
   :skolemid skolem_internal_ens__vstd!state_machine_internal.assert_deposit_map._definition
)))

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

;; Function-Axioms producer_comsumer_example::FifoQueue::State::next_by
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.next_by.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly) (post! Poly) (step! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.next_by.? T&. T& pre! post! step!)
     (ite
      (is-producer_comsumer_example!FifoQueue.Step./produce_start (%Poly%producer_comsumer_example!FifoQueue.Step.
        step!
      ))
      (producer_comsumer_example!FifoQueue.impl&%19.produce_start.? T&. T& pre! post!)
      (ite
       (is-producer_comsumer_example!FifoQueue.Step./produce_end (%Poly%producer_comsumer_example!FifoQueue.Step.
         step!
       ))
       (let
        ((perm$ (producer_comsumer_example!FifoQueue.Step./produce_end/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step.
            step!
        ))))
        (producer_comsumer_example!FifoQueue.impl&%19.produce_end.? T&. T& pre! post! perm$)
       )
       (ite
        (is-producer_comsumer_example!FifoQueue.Step./consume_start (%Poly%producer_comsumer_example!FifoQueue.Step.
          step!
        ))
        (producer_comsumer_example!FifoQueue.impl&%19.consume_start.? T&. T& pre! post!)
        (and
         (is-producer_comsumer_example!FifoQueue.Step./consume_end (%Poly%producer_comsumer_example!FifoQueue.Step.
           step!
         ))
         (let
          ((perm$ (producer_comsumer_example!FifoQueue.Step./consume_end/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step.
              step!
          ))))
          (producer_comsumer_example!FifoQueue.impl&%19.consume_end.? T&. T& pre! post! perm$)
    ))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.next_by.? T&. T& pre! post!
      step!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.next_by.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.next_by.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::next
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.next.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly) (post! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.next.? T&. T& pre! post!) (exists
      ((step$ Poly)) (!
       (and
        (has_type step$ (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
        (producer_comsumer_example!FifoQueue.impl&%19.next_by.? T&. T& pre! post! step$)
       )
       :pattern ((producer_comsumer_example!FifoQueue.impl&%19.next_by.? T&. T& pre! post!
         step$
       ))
       :qid user_producer_comsumer_example__FifoQueue__State__next_33
       :skolemid skolem_user_producer_comsumer_example__FifoQueue__State__next_33
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.next.? T&. T& pre! post!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.next.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.next.?_definition
))))

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
        :qid user_producer_comsumer_example__FifoQueue__State__initialize_34
        :skolemid skolem_user_producer_comsumer_example__FifoQueue__State__initialize_34
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

;; Function-Axioms producer_comsumer_example::FifoQueue::State::init_by
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.init_by.)
  (forall ((T&. Dcr) (T& Type) (post! Poly) (step! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.init_by.? T&. T& post! step!) (and
      (is-producer_comsumer_example!FifoQueue.Config./initialize (%Poly%producer_comsumer_example!FifoQueue.Config.
        step!
      ))
      (let
       ((backing_cells$ (producer_comsumer_example!FifoQueue.Config./initialize/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Config.
           step!
       ))))
       (let
        ((storage$ (producer_comsumer_example!FifoQueue.Config./initialize/1 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Config.
            step!
        ))))
        (producer_comsumer_example!FifoQueue.impl&%19.initialize.? T&. T& post! (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
          backing_cells$
         ) storage$
    )))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.init_by.? T&. T& post! step!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.init_by.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.init_by.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::init
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.init.)
  (forall ((T&. Dcr) (T& Type) (post! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.init.? T&. T& post!) (exists ((step$
        Poly
       )
      ) (!
       (and
        (has_type step$ (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&))
        (producer_comsumer_example!FifoQueue.impl&%19.init_by.? T&. T& post! step$)
       )
       :pattern ((producer_comsumer_example!FifoQueue.impl&%19.init_by.? T&. T& post! step$))
       :qid user_producer_comsumer_example__FifoQueue__State__init_35
       :skolemid skolem_user_producer_comsumer_example__FifoQueue__State__init_35
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.init.? T&. T& post!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.init.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.init.?_definition
))))

;; Function-Specs producer_comsumer_example::FifoQueue::Instance::clone
(declare-fun ens%producer_comsumer_example!FifoQueue.impl&%16.clone. (Dcr Type producer_comsumer_example!FifoQueue.Instance.
  producer_comsumer_example!FifoQueue.Instance.
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (self! producer_comsumer_example!FifoQueue.Instance.)
   (s! producer_comsumer_example!FifoQueue.Instance.)
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.impl&%16.clone. T&. T& self! s!) (and
     (has_type (Poly%producer_comsumer_example!FifoQueue.Instance. s!) (TYPE%producer_comsumer_example!FifoQueue.Instance.
       T&. T&
     ))
     (= self! s!)
   ))
   :pattern ((ens%producer_comsumer_example!FifoQueue.impl&%16.clone. T&. T& self! s!))
   :qid internal_ens__producer_comsumer_example!FifoQueue.impl&__16.clone._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.impl&__16.clone._definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::len
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.len.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.len.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.len.? T&. T& self!) (vstd!seq.Seq.len.?
      $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
        (%Poly%producer_comsumer_example!FifoQueue.State. self!)
    ))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.len.? T&. T& self!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.len.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.len.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&))
    (<= 0 (producer_comsumer_example!FifoQueue.impl&%19.len.? T&. T& self!))
   )
   :pattern ((producer_comsumer_example!FifoQueue.impl&%19.len.? T&. T& self!))
   :qid internal_producer_comsumer_example!FifoQueue.impl&__19.len.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.len.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::not_overlapping
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.not_overlapping.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.not_overlapping.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.not_overlapping.? T&. T& self!) (
      let
      ((tmp%%$ (tuple%2./tuple%2 (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!FifoQueue.State./State/producer
           (%Poly%producer_comsumer_example!FifoQueue.State. self!)
          )
         ) (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!FifoQueue.State./State/consumer
           (%Poly%producer_comsumer_example!FifoQueue.State. self!)
      )))))
      (ite
       (and
        (and
         (is-tuple%2./tuple%2 tmp%%$)
         (is-producer_comsumer_example!ProducerState./Producing (%Poly%producer_comsumer_example!ProducerState.
           (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
        )))
        (is-producer_comsumer_example!ConsumerState./Idle (%Poly%producer_comsumer_example!ConsumerState.
          (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
       )))
       (let
        ((tail$ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
            (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
        ))))
        (let
         ((head$ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
             (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
         ))))
         (not (= (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$) (I
             (producer_comsumer_example!FifoQueue.impl&%19.len.? T&. T& self!)
            )
           ) head$
       ))))
       (ite
        (and
         (and
          (is-tuple%2./tuple%2 tmp%%$)
          (is-producer_comsumer_example!ProducerState./Producing (%Poly%producer_comsumer_example!ProducerState.
            (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
         )))
         (is-producer_comsumer_example!ConsumerState./Consuming (%Poly%producer_comsumer_example!ConsumerState.
           (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
        )))
        (let
         ((tail$ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
             (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
         ))))
         (let
          ((head$ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
              (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
          ))))
          (and
           (not (= head$ tail$))
           (not (= (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$) (I
               (producer_comsumer_example!FifoQueue.impl&%19.len.? T&. T& self!)
              )
             ) head$
        )))))
        (ite
         (and
          (and
           (is-tuple%2./tuple%2 tmp%%$)
           (is-producer_comsumer_example!ProducerState./Idle (%Poly%producer_comsumer_example!ProducerState.
             (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
          )))
          (is-producer_comsumer_example!ConsumerState./Idle (%Poly%producer_comsumer_example!ConsumerState.
            (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
         )))
         (let
          ((tail$ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
              (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
          ))))
          (let
           ((head$ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
               (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
           ))))
           true
         ))
         (let
          ((tail$ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
              (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
          ))))
          (let
           ((head$ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
               (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
           ))))
           (not (= head$ tail$))
    )))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.not_overlapping.? T&. T& self!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.not_overlapping.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.not_overlapping.?_definition
))))

;; Function-Specs producer_comsumer_example::FifoQueue::State::lemma_msg_not_overlapping
(declare-fun req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping.
 (Dcr Type producer_comsumer_example!FifoQueue.State.) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (s! producer_comsumer_example!FifoQueue.State.)) (!
   (= (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping. T&.
     T& s!
    ) (producer_comsumer_example!FifoQueue.impl&%19.not_overlapping.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      s!
   )))
   :pattern ((req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping.
     T&. T& s!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.impl&__19.lemma_msg_not_overlapping._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.impl&__19.lemma_msg_not_overlapping._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping.
 (Dcr Type producer_comsumer_example!FifoQueue.State.) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (s! producer_comsumer_example!FifoQueue.State.)) (!
   (= (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping. T&.
     T& s!
    ) (producer_comsumer_example!FifoQueue.impl&%19.not_overlapping.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      s!
   )))
   :pattern ((ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping.
     T&. T& s!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.impl&__19.lemma_msg_not_overlapping._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.impl&__19.lemma_msg_not_overlapping._definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::in_bounds
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.in_bounds.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.in_bounds.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.in_bounds.? T&. T& self!) (and
      (and
       (and
        (and
         (and
          (<= 0 (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
             self!
          )))
          (< (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
             self!
            )
           ) (producer_comsumer_example!FifoQueue.impl&%19.len.? T&. T& self!)
         ))
         (<= 0 (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
            self!
        ))))
        (< (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
           self!
          )
         ) (producer_comsumer_example!FifoQueue.impl&%19.len.? T&. T& self!)
       ))
       (let
        ((tmp%%$ (producer_comsumer_example!FifoQueue.State./State/producer (%Poly%producer_comsumer_example!FifoQueue.State.
            self!
        ))))
        (ite
         (is-producer_comsumer_example!ProducerState./Producing tmp%%$)
         (let
          ((tail$ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
              (Poly%producer_comsumer_example!ProducerState. tmp%%$)
          ))))
          (= (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
             self!
            )
           ) tail$
         ))
         (let
          ((tail$ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
              (Poly%producer_comsumer_example!ProducerState. tmp%%$)
          ))))
          (= (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
             self!
            )
           ) tail$
      )))))
      (let
       ((tmp%%$ (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
           self!
       ))))
       (ite
        (is-producer_comsumer_example!ConsumerState./Consuming tmp%%$)
        (let
         ((head$ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
             (Poly%producer_comsumer_example!ConsumerState. tmp%%$)
         ))))
         (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
            self!
           )
          ) head$
        ))
        (let
         ((head$ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
             (Poly%producer_comsumer_example!ConsumerState. tmp%%$)
         ))))
         (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
            self!
           )
          ) head$
    ))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.in_bounds.? T&. T& self!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.in_bounds.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.in_bounds.?_definition
))))

;; Function-Specs producer_comsumer_example::FifoQueue::State::lemma_msg_in_bounds
(declare-fun req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds.
 (Dcr Type producer_comsumer_example!FifoQueue.State.) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (s! producer_comsumer_example!FifoQueue.State.)) (!
   (= (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds. T&. T& s!)
    (producer_comsumer_example!FifoQueue.impl&%19.in_bounds.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      s!
   )))
   :pattern ((req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds. T&.
     T& s!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.impl&__19.lemma_msg_in_bounds._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.impl&__19.lemma_msg_in_bounds._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds.
 (Dcr Type producer_comsumer_example!FifoQueue.State.) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (s! producer_comsumer_example!FifoQueue.State.)) (!
   (= (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds. T&. T& s!)
    (producer_comsumer_example!FifoQueue.impl&%19.in_bounds.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      s!
   )))
   :pattern ((ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds. T&.
     T& s!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.impl&__19.lemma_msg_in_bounds._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.impl&__19.lemma_msg_in_bounds._definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::is_checked_out
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.is_checked_out.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.is_checked_out.)
  (forall ((T&. Dcr) (T& Type) (self! Poly) (i! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.is_checked_out.? T&. T& self! i!)
     (or
      (= (producer_comsumer_example!FifoQueue.State./State/producer (%Poly%producer_comsumer_example!FifoQueue.State.
         self!
        )
       ) (producer_comsumer_example!ProducerState./Producing (%I i!))
      )
      (= (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
         self!
        )
       ) (producer_comsumer_example!ConsumerState./Consuming (%I i!))
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.is_checked_out.? T&. T& self!
      i!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.is_checked_out.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.is_checked_out.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::in_active_range
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.in_active_range.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.in_active_range.)
  (forall ((T&. Dcr) (T& Type) (self! Poly) (i! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.in_active_range.? T&. T& self! i!)
     (and
      (and
       (<= 0 (%I i!))
       (< (%I i!) (producer_comsumer_example!FifoQueue.impl&%19.len.? T&. T& self!))
      )
      (ite
       (<= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
          self!
         )
        ) (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
          self!
       )))
       (and
        (<= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
           self!
          )
         ) (%I i!)
        )
        (< (%I i!) (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
           self!
       ))))
       (or
        (>= (%I i!) (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
           self!
        )))
        (< (%I i!) (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
           self!
    )))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.in_active_range.? T&. T& self!
      i!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.in_active_range.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.in_active_range.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::valid_storage_at_idx
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.)
  (forall ((T&. Dcr) (T& Type) (self! Poly) (i! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& self!
      i!
     ) (ite
      (producer_comsumer_example!FifoQueue.impl&%19.is_checked_out.? T&. T& self! i!)
      (not (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
          T&. T&
         ) (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
           self!
         ))
        ) i!
      ))
      (and
       (and
        (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
           T&. T&
          ) (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
            self!
          ))
         ) i!
        )
        (= (vstd!cell.impl&%2.id.? T&. T& (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo.
            T&. T&
           ) (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
             self!
            )
           ) i!
          )
         ) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
            (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
              self!
            ))
           ) i!
       ))))
       (ite
        (producer_comsumer_example!FifoQueue.impl&%19.in_active_range.? T&. T& self! i!)
        (is-vstd!raw_ptr.MemContents./Init (vstd!cell.impl&%2.mem_contents.? T&. T& (vstd!map.impl&%0.index.?
           $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) (producer_comsumer_example!FifoQueue.State./State/storage
            (%Poly%producer_comsumer_example!FifoQueue.State. self!)
           ) i!
        )))
        (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& (vstd!map.impl&%0.index.?
           $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) (producer_comsumer_example!FifoQueue.State./State/storage
            (%Poly%producer_comsumer_example!FifoQueue.State. self!)
           ) i!
    )))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&.
      T& self! i!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.valid_storage_at_idx.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.valid_storage_at_idx.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::valid_storage_all
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.valid_storage_all.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.valid_storage_all.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_all.? T&. T& self!)
     (forall ((i$ Poly)) (!
       (=>
        (has_type i$ NAT)
        (=>
         (and
          (<= 0 (%I i$))
          (< (%I i$) (producer_comsumer_example!FifoQueue.impl&%19.len.? T&. T& self!))
         )
         (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& self!
          i$
       )))
       :pattern ((producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&.
         T& self! i$
       ))
       :qid user_producer_comsumer_example__FifoQueue__State__valid_storage_all_36
       :skolemid skolem_user_producer_comsumer_example__FifoQueue__State__valid_storage_all_36
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.valid_storage_all.? T&. T&
      self!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.valid_storage_all.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.valid_storage_all.?_definition
))))

;; Function-Specs producer_comsumer_example::FifoQueue::State::lemma_msg_valid_storage_all
(declare-fun req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all.
 (Dcr Type producer_comsumer_example!FifoQueue.State.) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (s! producer_comsumer_example!FifoQueue.State.)) (!
   (= (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all. T&.
     T& s!
    ) (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_all.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      s!
   )))
   :pattern ((req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all.
     T&. T& s!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.impl&__19.lemma_msg_valid_storage_all._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.impl&__19.lemma_msg_valid_storage_all._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all.
 (Dcr Type producer_comsumer_example!FifoQueue.State.) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (s! producer_comsumer_example!FifoQueue.State.)) (!
   (= (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all. T&.
     T& s!
    ) (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_all.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      s!
   )))
   :pattern ((ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all.
     T&. T& s!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.impl&__19.lemma_msg_valid_storage_all._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.impl&__19.lemma_msg_valid_storage_all._definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::Step::arrow_produce_end_0
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%0.arrow_produce_end_0.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%0.arrow_produce_end_0.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%0.arrow_produce_end_0.? T&. T& self!)
     (producer_comsumer_example!FifoQueue.Step./produce_end/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step.
       self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%0.arrow_produce_end_0.? T&. T&
      self!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__0.arrow_produce_end_0.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__0.arrow_produce_end_0.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
    (has_type (producer_comsumer_example!FifoQueue.impl&%0.arrow_produce_end_0.? T&. T&
      self!
     ) (TYPE%vstd!cell.PointsTo. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.impl&%0.arrow_produce_end_0.? T&. T&
     self!
   ))
   :qid internal_producer_comsumer_example!FifoQueue.impl&__0.arrow_produce_end_0.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__0.arrow_produce_end_0.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::Step::arrow_consume_end_0
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%0.arrow_consume_end_0.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%0.arrow_consume_end_0.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%0.arrow_consume_end_0.? T&. T& self!)
     (producer_comsumer_example!FifoQueue.Step./consume_end/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step.
       self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%0.arrow_consume_end_0.? T&. T&
      self!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__0.arrow_consume_end_0.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__0.arrow_consume_end_0.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
    (has_type (producer_comsumer_example!FifoQueue.impl&%0.arrow_consume_end_0.? T&. T&
      self!
     ) (TYPE%vstd!cell.PointsTo. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.impl&%0.arrow_consume_end_0.? T&. T&
     self!
   ))
   :qid internal_producer_comsumer_example!FifoQueue.impl&__0.arrow_consume_end_0.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__0.arrow_consume_end_0.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::Step::arrow_dummy_to_use_type_params_0
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%0.arrow_dummy_to_use_type_params_0.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%0.arrow_dummy_to_use_type_params_0.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%0.arrow_dummy_to_use_type_params_0.?
      T&. T& self!
     ) (producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step.
       self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%0.arrow_dummy_to_use_type_params_0.?
      T&. T& self!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__0.arrow_dummy_to_use_type_params_0.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__0.arrow_dummy_to_use_type_params_0.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
    (has_type (Poly%producer_comsumer_example!FifoQueue.State. (producer_comsumer_example!FifoQueue.impl&%0.arrow_dummy_to_use_type_params_0.?
       T&. T& self!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.impl&%0.arrow_dummy_to_use_type_params_0.?
     T&. T& self!
   ))
   :qid internal_producer_comsumer_example!FifoQueue.impl&__0.arrow_dummy_to_use_type_params_0.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__0.arrow_dummy_to_use_type_params_0.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::Step::is_produce_start
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%1.is_produce_start.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%1.is_produce_start.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%1.is_produce_start.? T&. T& self!) (
      is-producer_comsumer_example!FifoQueue.Step./produce_start (%Poly%producer_comsumer_example!FifoQueue.Step.
       self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%1.is_produce_start.? T&. T& self!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__1.is_produce_start.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__1.is_produce_start.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::Step::is_produce_end
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%1.is_produce_end.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%1.is_produce_end.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%1.is_produce_end.? T&. T& self!) (is-producer_comsumer_example!FifoQueue.Step./produce_end
      (%Poly%producer_comsumer_example!FifoQueue.Step. self!)
    ))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%1.is_produce_end.? T&. T& self!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__1.is_produce_end.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__1.is_produce_end.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::Step::get_produce_end_0
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%1.get_produce_end_0.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%1.get_produce_end_0.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%1.get_produce_end_0.? T&. T& self!)
     (producer_comsumer_example!FifoQueue.Step./produce_end/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step.
       self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%1.get_produce_end_0.? T&. T& self!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__1.get_produce_end_0.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__1.get_produce_end_0.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
    (has_type (producer_comsumer_example!FifoQueue.impl&%1.get_produce_end_0.? T&. T& self!)
     (TYPE%vstd!cell.PointsTo. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.impl&%1.get_produce_end_0.? T&. T& self!))
   :qid internal_producer_comsumer_example!FifoQueue.impl&__1.get_produce_end_0.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__1.get_produce_end_0.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::Step::is_consume_start
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%1.is_consume_start.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%1.is_consume_start.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%1.is_consume_start.? T&. T& self!) (
      is-producer_comsumer_example!FifoQueue.Step./consume_start (%Poly%producer_comsumer_example!FifoQueue.Step.
       self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%1.is_consume_start.? T&. T& self!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__1.is_consume_start.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__1.is_consume_start.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::Step::is_consume_end
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%1.is_consume_end.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%1.is_consume_end.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%1.is_consume_end.? T&. T& self!) (is-producer_comsumer_example!FifoQueue.Step./consume_end
      (%Poly%producer_comsumer_example!FifoQueue.Step. self!)
    ))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%1.is_consume_end.? T&. T& self!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__1.is_consume_end.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__1.is_consume_end.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::Step::get_consume_end_0
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%1.get_consume_end_0.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%1.get_consume_end_0.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%1.get_consume_end_0.? T&. T& self!)
     (producer_comsumer_example!FifoQueue.Step./consume_end/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step.
       self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%1.get_consume_end_0.? T&. T& self!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__1.get_consume_end_0.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__1.get_consume_end_0.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
    (has_type (producer_comsumer_example!FifoQueue.impl&%1.get_consume_end_0.? T&. T& self!)
     (TYPE%vstd!cell.PointsTo. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.impl&%1.get_consume_end_0.? T&. T& self!))
   :qid internal_producer_comsumer_example!FifoQueue.impl&__1.get_consume_end_0.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__1.get_consume_end_0.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::Step::is_dummy_to_use_type_params
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%1.is_dummy_to_use_type_params.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%1.is_dummy_to_use_type_params.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%1.is_dummy_to_use_type_params.? T&. T&
      self!
     ) (is-producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params (%Poly%producer_comsumer_example!FifoQueue.Step.
       self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%1.is_dummy_to_use_type_params.?
      T&. T& self!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__1.is_dummy_to_use_type_params.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__1.is_dummy_to_use_type_params.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::Step::get_dummy_to_use_type_params_0
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%1.get_dummy_to_use_type_params_0.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%1.get_dummy_to_use_type_params_0.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%1.get_dummy_to_use_type_params_0.? T&.
      T& self!
     ) (producer_comsumer_example!FifoQueue.Step./dummy_to_use_type_params/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step.
       self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%1.get_dummy_to_use_type_params_0.?
      T&. T& self!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__1.get_dummy_to_use_type_params_0.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__1.get_dummy_to_use_type_params_0.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
    (has_type (Poly%producer_comsumer_example!FifoQueue.State. (producer_comsumer_example!FifoQueue.impl&%1.get_dummy_to_use_type_params_0.?
       T&. T& self!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.impl&%1.get_dummy_to_use_type_params_0.?
     T&. T& self!
   ))
   :qid internal_producer_comsumer_example!FifoQueue.impl&__1.get_dummy_to_use_type_params_0.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__1.get_dummy_to_use_type_params_0.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::Config::arrow_1
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_1.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_1.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%2.arrow_1.? T&. T& self!) (producer_comsumer_example!FifoQueue.Config./initialize/1
      T&. T& (%Poly%producer_comsumer_example!FifoQueue.Config. self!)
    ))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%2.arrow_1.? T&. T& self!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__2.arrow_1.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__2.arrow_1.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&))
    (has_type (producer_comsumer_example!FifoQueue.impl&%2.arrow_1.? T&. T& self!) (TYPE%vstd!map.Map.
      $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&)
   )))
   :pattern ((producer_comsumer_example!FifoQueue.impl&%2.arrow_1.? T&. T& self!))
   :qid internal_producer_comsumer_example!FifoQueue.impl&__2.arrow_1.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__2.arrow_1.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::Config::arrow_initialize_0
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_0.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_0.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_0.? T&. T& self!)
     (producer_comsumer_example!FifoQueue.Config./initialize/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Config.
       self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_0.? T&. T&
      self!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__2.arrow_initialize_0.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__2.arrow_initialize_0.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::Config::arrow_initialize_1
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_1.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_1.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_1.? T&. T& self!)
     (producer_comsumer_example!FifoQueue.Config./initialize/1 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Config.
       self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_1.? T&. T&
      self!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__2.arrow_initialize_1.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__2.arrow_initialize_1.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&))
    (has_type (producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_1.? T&. T&
      self!
     ) (TYPE%vstd!map.Map. $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&))
   ))
   :pattern ((producer_comsumer_example!FifoQueue.impl&%2.arrow_initialize_1.? T&. T&
     self!
   ))
   :qid internal_producer_comsumer_example!FifoQueue.impl&__2.arrow_initialize_1.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__2.arrow_initialize_1.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::Config::arrow_dummy_to_use_type_params_0
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_dummy_to_use_type_params_0.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%2.arrow_dummy_to_use_type_params_0.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%2.arrow_dummy_to_use_type_params_0.?
      T&. T& self!
     ) (producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0 T&. T& (
       %Poly%producer_comsumer_example!FifoQueue.Config. self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%2.arrow_dummy_to_use_type_params_0.?
      T&. T& self!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__2.arrow_dummy_to_use_type_params_0.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__2.arrow_dummy_to_use_type_params_0.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&))
    (has_type (Poly%producer_comsumer_example!FifoQueue.State. (producer_comsumer_example!FifoQueue.impl&%2.arrow_dummy_to_use_type_params_0.?
       T&. T& self!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.impl&%2.arrow_dummy_to_use_type_params_0.?
     T&. T& self!
   ))
   :qid internal_producer_comsumer_example!FifoQueue.impl&__2.arrow_dummy_to_use_type_params_0.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__2.arrow_dummy_to_use_type_params_0.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::Config::is_initialize
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%3.is_initialize.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%3.is_initialize.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%3.is_initialize.? T&. T& self!) (is-producer_comsumer_example!FifoQueue.Config./initialize
      (%Poly%producer_comsumer_example!FifoQueue.Config. self!)
    ))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%3.is_initialize.? T&. T& self!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__3.is_initialize.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__3.is_initialize.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::Config::get_initialize_0
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%3.get_initialize_0.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%3.get_initialize_0.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%3.get_initialize_0.? T&. T& self!) (
      producer_comsumer_example!FifoQueue.Config./initialize/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Config.
       self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%3.get_initialize_0.? T&. T& self!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__3.get_initialize_0.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__3.get_initialize_0.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::Config::get_initialize_1
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%3.get_initialize_1.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%3.get_initialize_1.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%3.get_initialize_1.? T&. T& self!) (
      producer_comsumer_example!FifoQueue.Config./initialize/1 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Config.
       self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%3.get_initialize_1.? T&. T& self!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__3.get_initialize_1.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__3.get_initialize_1.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&))
    (has_type (producer_comsumer_example!FifoQueue.impl&%3.get_initialize_1.? T&. T& self!)
     (TYPE%vstd!map.Map. $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&))
   ))
   :pattern ((producer_comsumer_example!FifoQueue.impl&%3.get_initialize_1.? T&. T& self!))
   :qid internal_producer_comsumer_example!FifoQueue.impl&__3.get_initialize_1.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__3.get_initialize_1.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::Config::is_dummy_to_use_type_params
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%3.is_dummy_to_use_type_params.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%3.is_dummy_to_use_type_params.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%3.is_dummy_to_use_type_params.? T&. T&
      self!
     ) (is-producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params (%Poly%producer_comsumer_example!FifoQueue.Config.
       self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%3.is_dummy_to_use_type_params.?
      T&. T& self!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__3.is_dummy_to_use_type_params.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__3.is_dummy_to_use_type_params.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::Config::get_dummy_to_use_type_params_0
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%3.get_dummy_to_use_type_params_0.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%3.get_dummy_to_use_type_params_0.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%3.get_dummy_to_use_type_params_0.? T&.
      T& self!
     ) (producer_comsumer_example!FifoQueue.Config./dummy_to_use_type_params/0 T&. T& (
       %Poly%producer_comsumer_example!FifoQueue.Config. self!
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%3.get_dummy_to_use_type_params_0.?
      T&. T& self!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__3.get_dummy_to_use_type_params_0.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__3.get_dummy_to_use_type_params_0.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%producer_comsumer_example!FifoQueue.Config. T&. T&))
    (has_type (Poly%producer_comsumer_example!FifoQueue.State. (producer_comsumer_example!FifoQueue.impl&%3.get_dummy_to_use_type_params_0.?
       T&. T& self!
      )
     ) (TYPE%producer_comsumer_example!FifoQueue.State. T&. T&)
   ))
   :pattern ((producer_comsumer_example!FifoQueue.impl&%3.get_dummy_to_use_type_params_0.?
     T&. T& self!
   ))
   :qid internal_producer_comsumer_example!FifoQueue.impl&__3.get_dummy_to_use_type_params_0.?_pre_post_definition
   :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__3.get_dummy_to_use_type_params_0.?_pre_post_definition
)))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::initialize_enabled
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.initialize_enabled.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.initialize_enabled.)
  (forall ((T&. Dcr) (T& Type) (backing_cells! Poly) (storage! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.initialize_enabled.? T&. T& backing_cells!
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
        :qid user_producer_comsumer_example__FifoQueue__State__initialize_enabled_37
        :skolemid skolem_user_producer_comsumer_example__FifoQueue__State__initialize_enabled_37
      ))
      (> (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. backing_cells!) 0)
    ))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.initialize_enabled.? T&. T&
      backing_cells! storage!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.initialize_enabled.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.initialize_enabled.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::produce_start_strong
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_start_strong.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_start_strong.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly) (post! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.produce_start_strong.? T&. T& pre!
      post!
     ) (let
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
              (and
               (and
                (<= 0 tail$)
                (< tail$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                   (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                     pre!
               ))))))
               (let
                ((next_tail$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$)
                   (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                      (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                        pre!
                ))))))))
                (and
                 (not (= next_tail$ head$))
                 (let
                  ((update_tmp_producer$ (producer_comsumer_example!ProducerState./Producing (%I (I tail$)))))
                  (and
                   (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                      T&. T&
                     ) update_tmp_storage$
                    ) (I tail$)
                   )
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
                      (and
                       (and
                        (= (vstd!cell.impl&%2.id.? T&. T& perm$) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                           $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                             (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                            )
                           ) (I tail$)
                        )))
                        (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& perm$))
                       )
                       (= (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
                          post!
                         )
                        ) update_tmp_storage$1
                    ))))
                    (= (producer_comsumer_example!FifoQueue.State./State/producer (%Poly%producer_comsumer_example!FifoQueue.State.
                       post!
                      )
                     ) update_tmp_producer$
            )))))))))
            (and
             (= (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
                post!
               )
              ) update_tmp_consumer$
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
               (= (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                  post!
                 )
                ) update_tmp_backing_cells$
    ))))))))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.produce_start_strong.? T&.
      T& pre! post!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.produce_start_strong.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.produce_start_strong.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::produce_start_enabled
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_start_enabled.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_start_enabled.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.produce_start_enabled.? T&. T& pre!)
     (let
      ((tmp_assert$ true))
      (let
       ((update_tmp_storage$ (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
           pre!
       ))))
       (and
        (is-producer_comsumer_example!ProducerState./Idle (producer_comsumer_example!FifoQueue.State./State/producer
          (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
        ))
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
            (=>
             tmp_assert$1
             (not (= next_tail$ head$))
    )))))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.produce_start_enabled.? T&.
      T& pre!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.produce_start_enabled.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.produce_start_enabled.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::produce_end_strong
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_end_strong.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_end_strong.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly) (post! Poly) (perm! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.produce_end_strong.? T&. T& pre! post!
      perm!
     ) (let
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
            (and
             (and
              (<= 0 tail$)
              (< tail$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                 (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                   pre!
             ))))))
             (let
              ((next_tail$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$)
                 (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                    (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                      pre!
              ))))))))
              (and
               (and
                (= (vstd!cell.impl&%2.id.? T&. T& perm!) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                   $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                     (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                    )
                   ) (I tail$)
                )))
                (is-vstd!raw_ptr.MemContents./Init (vstd!cell.impl&%2.mem_contents.? T&. T& perm!))
               )
               (let
                ((update_tmp_producer$ (producer_comsumer_example!ProducerState./Idle (%I (I next_tail$)))))
                (let
                 ((update_tmp_tail$ next_tail$))
                 (and
                  (not (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                      T&. T&
                     ) update_tmp_storage$
                    ) (I tail$)
                  ))
                  (let
                   ((update_tmp_storage$1 (vstd!map.impl&%0.insert.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&.
                       T&
                      ) update_tmp_storage$ (I tail$) perm!
                   )))
                   (and
                    (= (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
                       post!
                      )
                     ) update_tmp_storage$1
                    )
                    (and
                     (= (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
                        post!
                       )
                      ) update_tmp_tail$
                     )
                     (= (producer_comsumer_example!FifoQueue.State./State/producer (%Poly%producer_comsumer_example!FifoQueue.State.
                        post!
                       )
                      ) update_tmp_producer$
           )))))))))))
           (and
            (= (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
               post!
              )
             ) update_tmp_consumer$
            )
            (and
             (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                post!
               )
              ) update_tmp_head$
             )
             (= (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                post!
               )
              ) update_tmp_backing_cells$
    ))))))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.produce_end_strong.? T&. T&
      pre! post! perm!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.produce_end_strong.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.produce_end_strong.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::produce_end_enabled
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_end_enabled.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.produce_end_enabled.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly) (perm! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.produce_end_enabled.? T&. T& pre!
      perm!
     ) (let
      ((tmp_assert$ true))
      (and
       (is-producer_comsumer_example!ProducerState./Producing (producer_comsumer_example!FifoQueue.State./State/producer
         (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
       ))
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
    ))))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.produce_end_enabled.? T&. T&
      pre! perm!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.produce_end_enabled.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.produce_end_enabled.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::consume_start_strong
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_start_strong.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_start_strong.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly) (post! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.consume_start_strong.? T&. T& pre!
      post!
     ) (let
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
              (and
               (and
                (<= 0 head$)
                (< head$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                   (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                     pre!
               ))))))
               (and
                (not (= head$ tail$))
                (let
                 ((update_tmp_consumer$ (producer_comsumer_example!ConsumerState./Consuming (%I (I head$)))))
                 (and
                  (let
                   ((perm$ (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) (producer_comsumer_example!FifoQueue.State./State/storage
                       (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                      ) (I head$)
                   )))
                   (and
                    (vstd!map_lib.impl&%0.contains_pair.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) update_tmp_storage$
                     (I head$) perm$
                    )
                    (let
                     ((update_tmp_storage$1 (vstd!map.impl&%0.remove.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&.
                         T&
                        ) update_tmp_storage$ (I head$)
                     )))
                     (and
                      (= (vstd!cell.impl&%2.id.? T&. T& perm$) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                         $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                           (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                          )
                         ) (I head$)
                      )))
                      (and
                       (is-vstd!raw_ptr.MemContents./Init (vstd!cell.impl&%2.mem_contents.? T&. T& perm$))
                       (= (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
                          post!
                         )
                        ) update_tmp_storage$1
                  ))))))
                  (= (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
                     post!
                    )
                   ) update_tmp_consumer$
            )))))))
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
               (= (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                  post!
                 )
                ) update_tmp_backing_cells$
    ))))))))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.consume_start_strong.? T&.
      T& pre! post!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.consume_start_strong.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.consume_start_strong.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::consume_start_enabled
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_start_enabled.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_start_enabled.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.consume_start_enabled.? T&. T& pre!)
     (let
      ((tmp_assert$ true))
      (and
       (is-producer_comsumer_example!ConsumerState./Idle (producer_comsumer_example!FifoQueue.State./State/consumer
         (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
       ))
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
          (=>
           tmp_assert$1
           (not (= head$ tail$))
    )))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.consume_start_enabled.? T&.
      T& pre!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.consume_start_enabled.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.consume_start_enabled.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::consume_end_strong
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_end_strong.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_end_strong.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly) (post! Poly) (perm! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.consume_end_strong.? T&. T& pre! post!
      perm!
     ) (let
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
            (and
             (and
              (<= 0 head$)
              (< head$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                 (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                   pre!
             ))))))
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
                 (and
                  (= (vstd!cell.impl&%2.id.? T&. T& perm!) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                     $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                       (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
                      )
                     ) (I head$)
                  )))
                  (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& perm!))
                 )
                 (and
                  (not (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                      T&. T&
                     ) update_tmp_storage$
                    ) (I head$)
                  ))
                  (let
                   ((update_tmp_storage$1 (vstd!map.impl&%0.insert.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&.
                       T&
                      ) update_tmp_storage$ (I head$) perm!
                   )))
                   (and
                    (= (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
                       post!
                      )
                     ) update_tmp_storage$1
                    )
                    (and
                     (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                        post!
                       )
                      ) update_tmp_head$
                     )
                     (= (producer_comsumer_example!FifoQueue.State./State/consumer (%Poly%producer_comsumer_example!FifoQueue.State.
                        post!
                       )
                      ) update_tmp_consumer$
           )))))))))))
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
             (= (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                post!
               )
              ) update_tmp_backing_cells$
    ))))))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.consume_end_strong.? T&. T&
      pre! post! perm!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.consume_end_strong.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.consume_end_strong.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::consume_end_enabled
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_end_enabled.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.consume_end_enabled.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly) (perm! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.consume_end_enabled.? T&. T& pre!
      perm!
     ) (let
      ((tmp_assert$ true))
      (and
       (is-producer_comsumer_example!ConsumerState./Consuming (producer_comsumer_example!FifoQueue.State./State/consumer
         (%Poly%producer_comsumer_example!FifoQueue.State. pre!)
       ))
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
    ))))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.consume_end_enabled.? T&. T&
      pre! perm!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.consume_end_enabled.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.consume_end_enabled.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::next_strong_by
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.next_strong_by.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly) (post! Poly) (step! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.next_strong_by.? T&. T& pre! post!
      step!
     ) (ite
      (is-producer_comsumer_example!FifoQueue.Step./produce_start (%Poly%producer_comsumer_example!FifoQueue.Step.
        step!
      ))
      (producer_comsumer_example!FifoQueue.impl&%19.produce_start_strong.? T&. T& pre! post!)
      (ite
       (is-producer_comsumer_example!FifoQueue.Step./produce_end (%Poly%producer_comsumer_example!FifoQueue.Step.
         step!
       ))
       (let
        ((perm$ (producer_comsumer_example!FifoQueue.Step./produce_end/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step.
            step!
        ))))
        (producer_comsumer_example!FifoQueue.impl&%19.produce_end_strong.? T&. T& pre! post!
         perm$
       ))
       (ite
        (is-producer_comsumer_example!FifoQueue.Step./consume_start (%Poly%producer_comsumer_example!FifoQueue.Step.
          step!
        ))
        (producer_comsumer_example!FifoQueue.impl&%19.consume_start_strong.? T&. T& pre! post!)
        (and
         (is-producer_comsumer_example!FifoQueue.Step./consume_end (%Poly%producer_comsumer_example!FifoQueue.Step.
           step!
         ))
         (let
          ((perm$ (producer_comsumer_example!FifoQueue.Step./consume_end/0 T&. T& (%Poly%producer_comsumer_example!FifoQueue.Step.
              step!
          ))))
          (producer_comsumer_example!FifoQueue.impl&%19.consume_end_strong.? T&. T& pre! post!
           perm$
    )))))))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.next_strong_by.? T&. T& pre!
      post! step!
    ))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.next_strong_by.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.next_strong_by.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::next_strong
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.next_strong.)
  (forall ((T&. Dcr) (T& Type) (pre! Poly) (post! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.next_strong.? T&. T& pre! post!)
     (exists ((step$ Poly)) (!
       (and
        (has_type step$ (TYPE%producer_comsumer_example!FifoQueue.Step. T&. T&))
        (producer_comsumer_example!FifoQueue.impl&%19.next_strong_by.? T&. T& pre! post! step$)
       )
       :pattern ((producer_comsumer_example!FifoQueue.impl&%19.next_strong_by.? T&. T& pre!
         post! step$
       ))
       :qid user_producer_comsumer_example__FifoQueue__State__next_strong_38
       :skolemid skolem_user_producer_comsumer_example__FifoQueue__State__next_strong_38
    )))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.next_strong.? T&. T& pre! post!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.next_strong.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.next_strong.?_definition
))))

;; Function-Axioms producer_comsumer_example::FifoQueue::State::invariant
(assert
 (fuel_bool_default fuel%producer_comsumer_example!FifoQueue.impl&%19.invariant.)
)
(assert
 (=>
  (fuel_bool fuel%producer_comsumer_example!FifoQueue.impl&%19.invariant.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& self!) (and
      (and
       (producer_comsumer_example!FifoQueue.impl&%19.not_overlapping.? T&. T& self!)
       (producer_comsumer_example!FifoQueue.impl&%19.in_bounds.? T&. T& self!)
      )
      (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_all.? T&. T& self!)
    ))
    :pattern ((producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& self!))
    :qid internal_producer_comsumer_example!FifoQueue.impl&__19.invariant.?_definition
    :skolemid skolem_internal_producer_comsumer_example!FifoQueue.impl&__19.invariant.?_definition
))))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%vstd!tokens.ValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.head.
      T&. T&
     ) $ NAT
   ))
   :pattern ((tr_bound%vstd!tokens.ValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.head.
      T&. T&
     ) $ NAT
   ))
   :qid internal_producer_comsumer_example__FifoQueue__impl&__5_trait_impl_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__impl&__5_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%vstd!tokens.ValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.tail.
      T&. T&
     ) $ NAT
   ))
   :pattern ((tr_bound%vstd!tokens.ValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.tail.
      T&. T&
     ) $ NAT
   ))
   :qid internal_producer_comsumer_example__FifoQueue__impl&__8_trait_impl_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__impl&__8_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%vstd!tokens.ValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.producer.
      T&. T&
     ) $ TYPE%producer_comsumer_example!ProducerState.
   ))
   :pattern ((tr_bound%vstd!tokens.ValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.producer.
      T&. T&
     ) $ TYPE%producer_comsumer_example!ProducerState.
   ))
   :qid internal_producer_comsumer_example__FifoQueue__impl&__11_trait_impl_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__impl&__11_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%vstd!tokens.ValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
      T&. T&
     ) $ TYPE%producer_comsumer_example!ConsumerState.
   ))
   :pattern ((tr_bound%vstd!tokens.ValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
      T&. T&
     ) $ TYPE%producer_comsumer_example!ConsumerState.
   ))
   :qid internal_producer_comsumer_example__FifoQueue__impl&__14_trait_impl_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__impl&__14_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%core!clone.Clone. $ (TYPE%vstd!state_machine_internal.SyncSendIfSyncSend.
      T&. T&
   )))
   :pattern ((tr_bound%core!clone.Clone. $ (TYPE%vstd!state_machine_internal.SyncSendIfSyncSend.
      T&. T&
   )))
   :qid internal_vstd__state_machine_internal__impl&__1_trait_impl_definition
   :skolemid skolem_internal_vstd__state_machine_internal__impl&__1_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!clone.Clone. $ BOOL)
)

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (tr_bound%core!clone.Clone. (REF T&.) T&)
   :pattern ((tr_bound%core!clone.Clone. (REF T&.) T&))
   :qid internal_core__clone__impls__impl&__3_trait_impl_definition
   :skolemid skolem_internal_core__clone__impls__impl&__3_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (and
     (sized T&.)
     (tr_bound%core!clone.Clone. T&. T&)
    )
    (tr_bound%core!clone.Clone. $ (TYPE%core!option.Option. T&. T&))
   )
   :pattern ((tr_bound%core!clone.Clone. $ (TYPE%core!option.Option. T&. T&)))
   :qid internal_core__option__impl&__5_trait_impl_definition
   :skolemid skolem_internal_core__option__impl&__5_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%core!alloc.Allocator. A&. A&)
    (tr_bound%core!alloc.Allocator. (REF A&.) A&)
   )
   :pattern ((tr_bound%core!alloc.Allocator. (REF A&.) A&))
   :qid internal_core__alloc__impl&__2_trait_impl_definition
   :skolemid skolem_internal_core__alloc__impl&__2_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (sized A&.)
    (tr_bound%core!clone.Clone. (TRACKED A&.) A&)
   )
   :pattern ((tr_bound%core!clone.Clone. (TRACKED A&.) A&))
   :qid internal_builtin__impl&__5_trait_impl_definition
   :skolemid skolem_internal_builtin__impl&__5_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (sized A&.)
    (tr_bound%core!clone.Clone. (GHOST A&.) A&)
   )
   :pattern ((tr_bound%core!clone.Clone. (GHOST A&.) A&))
   :qid internal_builtin__impl&__3_trait_impl_definition
   :skolemid skolem_internal_builtin__impl&__3_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (=>
    (and
     (sized T&.)
     (sized A&.)
     (tr_bound%core!clone.Clone. T&. T&)
     (tr_bound%core!alloc.Allocator. A&. A&)
     (tr_bound%core!clone.Clone. A&. A&)
    )
    (tr_bound%core!clone.Clone. (BOX A&. A& T&.) T&)
   )
   :pattern ((tr_bound%core!clone.Clone. (BOX A&. A& T&.) T&))
   :qid internal_alloc__boxed__impl&__12_trait_impl_definition
   :skolemid skolem_internal_alloc__boxed__impl&__12_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%vstd!tokens.UniqueValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.head.
      T&. T&
     ) $ NAT
   ))
   :pattern ((tr_bound%vstd!tokens.UniqueValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.head.
      T&. T&
     ) $ NAT
   ))
   :qid internal_producer_comsumer_example__FifoQueue__impl&__6_trait_impl_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__impl&__6_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%vstd!tokens.UniqueValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.tail.
      T&. T&
     ) $ NAT
   ))
   :pattern ((tr_bound%vstd!tokens.UniqueValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.tail.
      T&. T&
     ) $ NAT
   ))
   :qid internal_producer_comsumer_example__FifoQueue__impl&__9_trait_impl_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__impl&__9_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%vstd!tokens.UniqueValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.producer.
      T&. T&
     ) $ TYPE%producer_comsumer_example!ProducerState.
   ))
   :pattern ((tr_bound%vstd!tokens.UniqueValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.producer.
      T&. T&
     ) $ TYPE%producer_comsumer_example!ProducerState.
   ))
   :qid internal_producer_comsumer_example__FifoQueue__impl&__12_trait_impl_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__impl&__12_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%vstd!tokens.UniqueValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
      T&. T&
     ) $ TYPE%producer_comsumer_example!ConsumerState.
   ))
   :pattern ((tr_bound%vstd!tokens.UniqueValueToken. $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
      T&. T&
     ) $ TYPE%producer_comsumer_example!ConsumerState.
   ))
   :qid internal_producer_comsumer_example__FifoQueue__impl&__15_trait_impl_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__impl&__15_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%core!clone.Clone. $ (TYPE%producer_comsumer_example!FifoQueue.Instance. T&.
      T&
   )))
   :pattern ((tr_bound%core!clone.Clone. $ (TYPE%producer_comsumer_example!FifoQueue.Instance.
      T&. T&
   )))
   :qid internal_producer_comsumer_example__FifoQueue__impl&__17_trait_impl_definition
   :skolemid skolem_internal_producer_comsumer_example__FifoQueue__impl&__17_trait_impl_definition
)))

;; Function-Specs producer_comsumer_example::FifoQueue::State::initialize_inductive
(declare-fun req%producer_comsumer_example!FifoQueue.impl&%19.initialize_inductive.
 (Dcr Type producer_comsumer_example!FifoQueue.State. vstd!seq.Seq<vstd!cell.CellId.>.
  Poly
 ) Bool
)
(declare-const %%global_location_label%%6 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (post! producer_comsumer_example!FifoQueue.State.) (backing_cells!
    vstd!seq.Seq<vstd!cell.CellId.>.
   ) (storage! Poly)
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.impl&%19.initialize_inductive. T&. T& post!
     backing_cells! storage!
    ) (=>
     %%global_location_label%%6
     (producer_comsumer_example!FifoQueue.impl&%19.initialize.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
       post!
      ) (Poly%vstd!seq.Seq<vstd!cell.CellId.>. backing_cells!) storage!
   )))
   :pattern ((req%producer_comsumer_example!FifoQueue.impl&%19.initialize_inductive. T&.
     T& post! backing_cells! storage!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.impl&__19.initialize_inductive._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.impl&__19.initialize_inductive._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.impl&%19.initialize_inductive.
 (Dcr Type producer_comsumer_example!FifoQueue.State. vstd!seq.Seq<vstd!cell.CellId.>.
  Poly
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (post! producer_comsumer_example!FifoQueue.State.) (backing_cells!
    vstd!seq.Seq<vstd!cell.CellId.>.
   ) (storage! Poly)
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.impl&%19.initialize_inductive. T&. T& post!
     backing_cells! storage!
    ) (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      post!
   )))
   :pattern ((ens%producer_comsumer_example!FifoQueue.impl&%19.initialize_inductive. T&.
     T& post! backing_cells! storage!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.impl&__19.initialize_inductive._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.impl&__19.initialize_inductive._definition
)))

;; Function-Def producer_comsumer_example::FifoQueue::State::initialize_inductive
;; producer_comsumer_example.rs:325:5: 325:106 (#0)
(get-info :all-statistics)
(push)
 (declare-const T&. Dcr)
 (declare-const T& Type)
 (declare-const post! producer_comsumer_example!FifoQueue.State.)
 (declare-const backing_cells! vstd!seq.Seq<vstd!cell.CellId.>.)
 (declare-const storage! Poly)
 (declare-const i@ Poly)
 (declare-const tmp%1 Bool)
 (assert
  fuel_defaults
 )
 (assert
  (sized T&.)
 )
 (assert
  (has_type (Poly%producer_comsumer_example!FifoQueue.State. post!) (TYPE%producer_comsumer_example!FifoQueue.State.
    T&. T&
 )))
 (assert
  (has_type storage! (TYPE%vstd!map.Map. $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&)))
 )
 (assert
  (producer_comsumer_example!FifoQueue.impl&%19.initialize.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
    post!
   ) (Poly%vstd!seq.Seq<vstd!cell.CellId.>. backing_cells!) storage!
 ))
 ;; assertion failed
 (declare-const %%location_label%%0 Bool)
 ;; assertion failed
 (declare-const %%location_label%%1 Bool)
 ;; could not show invariant `not_overlapping` on the `post` state
 (declare-const %%location_label%%2 Bool)
 ;; could not show invariant `in_bounds` on the `post` state
 (declare-const %%location_label%%3 Bool)
 ;; could not show invariant `valid_storage_all` on the `post` state
 (declare-const %%location_label%%4 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%5 Bool)
 (assert
  (not (and
    (=>
     (has_type i@ NAT)
     (=>
      (and
       (<= 0 (%I i@))
       (< (%I i@) (producer_comsumer_example!FifoQueue.impl&%19.len.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
          post!
      ))))
      (=>
       (= tmp%1 (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
           T&. T&
          ) (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
            (Poly%producer_comsumer_example!FifoQueue.State. post!)
          ))
         ) i@
       ))
       (and
        (=>
         %%location_label%%0
         tmp%1
        )
        (=>
         tmp%1
         (=>
          %%location_label%%1
          (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
            post!
           ) i@
    )))))))
    (=>
     (forall ((i$ Poly)) (!
       (=>
        (has_type i$ NAT)
        (=>
         (and
          (<= 0 (%I i$))
          (< (%I i$) (producer_comsumer_example!FifoQueue.impl&%19.len.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
             post!
         ))))
         (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
           post!
          ) i$
       )))
       :pattern ((producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&.
         T& (Poly%producer_comsumer_example!FifoQueue.State. post!) i$
       ))
       :qid user_producer_comsumer_example__FifoQueue__State__initialize_inductive_39
       :skolemid skolem_user_producer_comsumer_example__FifoQueue__State__initialize_inductive_39
     ))
     (and
      (=>
       %%location_label%%2
       (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping. T&. T&
        post!
      ))
      (=>
       (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping. T&. T&
        post!
       )
       (and
        (=>
         %%location_label%%3
         (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds. T&. T& post!)
        )
        (=>
         (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds. T&. T& post!)
         (and
          (=>
           %%location_label%%4
           (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all. T&.
            T& post!
          ))
          (=>
           (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all. T&.
            T& post!
           )
           (=>
            %%location_label%%5
            (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
              post!
 )))))))))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Specs producer_comsumer_example::FifoQueue::State::produce_start_inductive
(declare-fun req%producer_comsumer_example!FifoQueue.impl&%19.produce_start_inductive.
 (Dcr Type producer_comsumer_example!FifoQueue.State. producer_comsumer_example!FifoQueue.State.)
 Bool
)
(declare-const %%global_location_label%%7 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   )
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.impl&%19.produce_start_inductive. T&. T&
     pre! post!
    ) (=>
     %%global_location_label%%7
     (and
      (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
        pre!
      ))
      (producer_comsumer_example!FifoQueue.impl&%19.produce_start_strong.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
        pre!
       ) (Poly%producer_comsumer_example!FifoQueue.State. post!)
   ))))
   :pattern ((req%producer_comsumer_example!FifoQueue.impl&%19.produce_start_inductive.
     T&. T& pre! post!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.impl&__19.produce_start_inductive._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.impl&__19.produce_start_inductive._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.impl&%19.produce_start_inductive.
 (Dcr Type producer_comsumer_example!FifoQueue.State. producer_comsumer_example!FifoQueue.State.)
 Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   )
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.impl&%19.produce_start_inductive. T&. T&
     pre! post!
    ) (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      post!
   )))
   :pattern ((ens%producer_comsumer_example!FifoQueue.impl&%19.produce_start_inductive.
     T&. T& pre! post!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.impl&__19.produce_start_inductive._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.impl&__19.produce_start_inductive._definition
)))

;; Function-Def producer_comsumer_example::FifoQueue::State::produce_start_inductive
;; producer_comsumer_example.rs:346:5: 346:54 (#0)
(get-info :all-statistics)
(push)
 (declare-const T&. Dcr)
 (declare-const T& Type)
 (declare-const pre! producer_comsumer_example!FifoQueue.State.)
 (declare-const post! producer_comsumer_example!FifoQueue.State.)
 (declare-const tmp%1 Bool)
 (declare-const tmp%2 Bool)
 (declare-const tail$1@ Int)
 (declare-const head@ Int)
 (declare-const tmp%3 Bool)
 (declare-const tmp%4 Bool)
 (declare-const tail$2@ Int)
 (declare-const head$1@ Int)
 (declare-const tail$3@ Int)
 (declare-const head$2@ Int)
 (declare-const tmp%5 Bool)
 (declare-const tail$4@ Int)
 (declare-const head$3@ Int)
 (declare-const tmp%%@ tuple%2.)
 (declare-const tmp%6 Bool)
 (declare-const tail@ Int)
 (assert
  fuel_defaults
 )
 (assert
  (sized T&.)
 )
 (assert
  (has_type (Poly%producer_comsumer_example!FifoQueue.State. pre!) (TYPE%producer_comsumer_example!FifoQueue.State.
    T&. T&
 )))
 (assert
  (has_type (Poly%producer_comsumer_example!FifoQueue.State. post!) (TYPE%producer_comsumer_example!FifoQueue.State.
    T&. T&
 )))
 (assert
  (and
   (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
     pre!
   ))
   (producer_comsumer_example!FifoQueue.impl&%19.produce_start_strong.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
     pre!
    ) (Poly%producer_comsumer_example!FifoQueue.State. post!)
 )))
 (declare-const %%switch_label%%0 Bool)
 (declare-const %%switch_label%%1 Bool)
 (declare-const %%switch_label%%2 Bool)
 ;; assertion failed
 (declare-const %%location_label%%0 Bool)
 ;; assertion failed
 (declare-const %%location_label%%1 Bool)
 ;; assertion failed
 (declare-const %%location_label%%2 Bool)
 ;; assertion failed
 (declare-const %%location_label%%3 Bool)
 ;; assertion failed
 (declare-const %%location_label%%4 Bool)
 ;; assertion failed
 (declare-const %%location_label%%5 Bool)
 ;; could not show invariant `not_overlapping` on the `post` state
 (declare-const %%location_label%%6 Bool)
 ;; could not show invariant `in_bounds` on the `post` state
 (declare-const %%location_label%%7 Bool)
 ;; could not show invariant `valid_storage_all` on the `post` state
 (declare-const %%location_label%%8 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%9 Bool)
 (assert
  (not (=>
    (= tail@ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
       (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!FifoQueue.State./State/producer
         (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
           pre!
    )))))))
    (=>
     (= tmp%1 (not (producer_comsumer_example!FifoQueue.impl&%19.in_active_range.? T&. T&
        (Poly%producer_comsumer_example!FifoQueue.State. pre!) (I tail@)
     )))
     (and
      (=>
       %%location_label%%0
       tmp%1
      )
      (=>
       tmp%1
       (=>
        (= tmp%%@ (tuple%2./tuple%2 (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!FifoQueue.State./State/producer
            (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
              post!
           )))
          ) (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!FifoQueue.State./State/consumer
            (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
              post!
        ))))))
        (or
         (and
          (=>
           (and
            (and
             (is-tuple%2./tuple%2 tmp%%@)
             (is-producer_comsumer_example!ProducerState./Producing (%Poly%producer_comsumer_example!ProducerState.
               (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
            )))
            (is-producer_comsumer_example!ConsumerState./Idle (%Poly%producer_comsumer_example!ConsumerState.
              (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
           )))
           (=>
            (= tail$1@ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
               (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
            )))
            (=>
             (= head@ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
                (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
             )))
             (=>
              (= tmp%2 (not (= (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$1@)
                  (I (producer_comsumer_example!FifoQueue.impl&%19.len.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
                     post!
                  )))
                 ) head@
              )))
              (and
               (=>
                %%location_label%%1
                tmp%2
               )
               (=>
                tmp%2
                %%switch_label%%0
          ))))))
          (=>
           (not (and
             (and
              (is-tuple%2./tuple%2 tmp%%@)
              (is-producer_comsumer_example!ProducerState./Producing (%Poly%producer_comsumer_example!ProducerState.
                (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
             )))
             (is-producer_comsumer_example!ConsumerState./Idle (%Poly%producer_comsumer_example!ConsumerState.
               (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
           ))))
           (or
            (and
             (=>
              (and
               (and
                (is-tuple%2./tuple%2 tmp%%@)
                (is-producer_comsumer_example!ProducerState./Producing (%Poly%producer_comsumer_example!ProducerState.
                  (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
               )))
               (is-producer_comsumer_example!ConsumerState./Consuming (%Poly%producer_comsumer_example!ConsumerState.
                 (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
              )))
              (=>
               (= tail$2@ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
                  (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
               )))
               (=>
                (= head$1@ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
                   (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                )))
                (=>
                 (= tmp%3 (not (= head$1@ tail$2@)))
                 (and
                  (=>
                   %%location_label%%2
                   tmp%3
                  )
                  (=>
                   tmp%3
                   (=>
                    (= tmp%4 (not (= (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$2@)
                        (I (producer_comsumer_example!FifoQueue.impl&%19.len.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
                           post!
                        )))
                       ) head$1@
                    )))
                    (and
                     (=>
                      %%location_label%%3
                      tmp%4
                     )
                     (=>
                      tmp%4
                      %%switch_label%%1
             )))))))))
             (=>
              (not (and
                (and
                 (is-tuple%2./tuple%2 tmp%%@)
                 (is-producer_comsumer_example!ProducerState./Producing (%Poly%producer_comsumer_example!ProducerState.
                   (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                )))
                (is-producer_comsumer_example!ConsumerState./Consuming (%Poly%producer_comsumer_example!ConsumerState.
                  (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
              ))))
              (or
               (and
                (=>
                 (and
                  (and
                   (is-tuple%2./tuple%2 tmp%%@)
                   (is-producer_comsumer_example!ProducerState./Idle (%Poly%producer_comsumer_example!ProducerState.
                     (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                  )))
                  (is-producer_comsumer_example!ConsumerState./Idle (%Poly%producer_comsumer_example!ConsumerState.
                    (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                 )))
                 (=>
                  (= tail$3@ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
                     (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                  )))
                  (=>
                   (= head$2@ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
                      (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                   )))
                   %%switch_label%%2
                )))
                (=>
                 (not (and
                   (and
                    (is-tuple%2./tuple%2 tmp%%@)
                    (is-producer_comsumer_example!ProducerState./Idle (%Poly%producer_comsumer_example!ProducerState.
                      (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                   )))
                   (is-producer_comsumer_example!ConsumerState./Idle (%Poly%producer_comsumer_example!ConsumerState.
                     (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                 ))))
                 (=>
                  (= tail$4@ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
                     (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                  )))
                  (=>
                   (= head$3@ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
                      (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                   )))
                   (=>
                    (= tmp%5 (not (= head$3@ tail$4@)))
                    (and
                     (=>
                      %%location_label%%4
                      tmp%5
                     )
                     (=>
                      tmp%5
                      %%switch_label%%2
               )))))))
               (and
                (not %%switch_label%%2)
                %%switch_label%%1
            ))))
            (and
             (not %%switch_label%%1)
             %%switch_label%%0
         ))))
         (and
          (not %%switch_label%%0)
          (=>
           (= tmp%6 (forall ((i$ Poly)) (!
              (=>
               (has_type i$ NAT)
               (=>
                (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
                  pre!
                 ) i$
                )
                (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
                  post!
                 ) i$
              )))
              :pattern ((producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&.
                T& (Poly%producer_comsumer_example!FifoQueue.State. pre!) i$
              ))
              :pattern ((producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&.
                T& (Poly%producer_comsumer_example!FifoQueue.State. post!) i$
              ))
              :qid user_producer_comsumer_example__FifoQueue__State__produce_start_inductive_40
              :skolemid skolem_user_producer_comsumer_example__FifoQueue__State__produce_start_inductive_40
           )))
           (and
            (=>
             %%location_label%%5
             tmp%6
            )
            (=>
             tmp%6
             (and
              (=>
               %%location_label%%6
               (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping. T&. T&
                post!
              ))
              (=>
               (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping. T&. T&
                post!
               )
               (and
                (=>
                 %%location_label%%7
                 (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds. T&. T& post!)
                )
                (=>
                 (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds. T&. T& post!)
                 (and
                  (=>
                   %%location_label%%8
                   (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all. T&.
                    T& post!
                  ))
                  (=>
                   (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all. T&.
                    T& post!
                   )
                   (=>
                    %%location_label%%9
                    (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
                      post!
 )))))))))))))))))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Def producer_comsumer_example::FifoQueue::State::produce_start_asserts
;; producer_comsumer_example.rs:20:1: 433:3 (#27)
(get-info :all-statistics)
(push)
 (declare-const T&. Dcr)
 (declare-const T& Type)
 (declare-const pre! producer_comsumer_example!FifoQueue.State.)
 (declare-const tmp%1 Bool)
 (declare-const tmp%2 Bool)
 (declare-const tmp%3 Bool)
 (declare-const tmp%4 Bool)
 (declare-const tmp%5 Bool)
 (declare-const tmp%6 Bool)
 (declare-const perm@ Poly)
 (declare-const update_tmp_storage$1@ Poly)
 (declare-const tail@ Int)
 (declare-const head@ Int)
 (declare-const next_tail@ Int)
 (declare-const update_tmp_producer$1@ producer_comsumer_example!ProducerState.)
 (declare-const update_tmp_backing_cells@ vstd!seq.Seq<vstd!cell.CellId.>.)
 (declare-const update_tmp_storage@ Poly)
 (declare-const update_tmp_head@ Int)
 (declare-const update_tmp_tail@ Int)
 (declare-const update_tmp_producer@ producer_comsumer_example!ProducerState.)
 (declare-const update_tmp_consumer@ producer_comsumer_example!ConsumerState.)
 (assert
  fuel_defaults
 )
 (assert
  (sized T&.)
 )
 (assert
  (has_type (Poly%producer_comsumer_example!FifoQueue.State. pre!) (TYPE%producer_comsumer_example!FifoQueue.State.
    T&. T&
 )))
 ;; unable to prove assertion safety condition
 (declare-const %%location_label%%0 Bool)
 ;; assertion failed
 (declare-const %%location_label%%1 Bool)
 ;; unable to prove inherent safety condition: the value to be withdrawn must be stored at the given key before the withdraw
 (declare-const %%location_label%%2 Bool)
 ;; assertion failed
 (declare-const %%location_label%%3 Bool)
 ;; assertion failed
 (declare-const %%location_label%%4 Bool)
 ;; assertion failed
 (declare-const %%location_label%%5 Bool)
 ;; unable to prove assertion safety condition
 (declare-const %%location_label%%6 Bool)
 ;; assertion failed
 (declare-const %%location_label%%7 Bool)
 (assert
  (not (=>
    (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      pre!
    ))
    (=>
     (= update_tmp_backing_cells@ (producer_comsumer_example!FifoQueue.State./State/backing_cells
       (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
         pre!
     ))))
     (=>
      (= update_tmp_storage@ (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
         (Poly%producer_comsumer_example!FifoQueue.State. pre!)
      )))
      (=>
       (= update_tmp_head@ (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
          (Poly%producer_comsumer_example!FifoQueue.State. pre!)
       )))
       (=>
        (= update_tmp_tail@ (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
           (Poly%producer_comsumer_example!FifoQueue.State. pre!)
        )))
        (=>
         (= update_tmp_producer@ (producer_comsumer_example!FifoQueue.State./State/producer
           (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
             pre!
         ))))
         (=>
          (= update_tmp_consumer@ (producer_comsumer_example!FifoQueue.State./State/consumer
            (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
              pre!
          ))))
          (=>
           (is-producer_comsumer_example!ProducerState./Idle (producer_comsumer_example!FifoQueue.State./State/producer
             (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
               pre!
           ))))
           (=>
            (= tail@ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
               (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!FifoQueue.State./State/producer
                 (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                   pre!
            )))))))
            (=>
             (= head@ (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                (Poly%producer_comsumer_example!FifoQueue.State. pre!)
             )))
             (=>
              (= tmp%1 (and
                (<= 0 tail@)
                (< tail@ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                   (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                     (Poly%producer_comsumer_example!FifoQueue.State. pre!)
              )))))))
              (and
               (=>
                %%location_label%%0
                (req%vstd!state_machine_internal.assert_safety. tmp%1)
               )
               (=>
                (ens%vstd!state_machine_internal.assert_safety. tmp%1)
                (=>
                 (= next_tail@ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail@)
                   (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                      (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                        (Poly%producer_comsumer_example!FifoQueue.State. pre!)
                 )))))))
                 (=>
                  (not (= next_tail@ head@))
                  (=>
                   (= update_tmp_producer$1@ (producer_comsumer_example!ProducerState./Producing (%I (I
                       tail@
                   ))))
                   (and
                    (=>
                     (= tmp%2 (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T&
                       (Poly%producer_comsumer_example!FifoQueue.State. pre!) (I tail@)
                     ))
                     (and
                      (=>
                       %%location_label%%1
                       tmp%2
                      )
                      (=>
                       tmp%2
                       (=>
                        (= tmp%3 (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                            T&. T&
                           ) update_tmp_storage@
                          ) (I tail@)
                        ))
                        (and
                         (=>
                          %%location_label%%2
                          (req%vstd!state_machine_internal.assert_withdraw_map. tmp%3)
                         )
                         (=>
                          (ens%vstd!state_machine_internal.assert_withdraw_map. tmp%3)
                          (=>
                           %%location_label%%3
                           (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                              T&. T&
                             ) update_tmp_storage@
                            ) (I tail@)
                    ))))))))
                    (=>
                     (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                        T&. T&
                       ) update_tmp_storage@
                      ) (I tail@)
                     )
                     (=>
                      (= perm@ (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) update_tmp_storage@
                        (I tail@)
                      ))
                      (=>
                       (= update_tmp_storage$1@ (vstd!map.impl&%0.remove.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                          T&. T&
                         ) update_tmp_storage@ (I tail@)
                       ))
                       (=>
                        (= tmp%4 (not (producer_comsumer_example!FifoQueue.impl&%19.in_active_range.? T&. T&
                           (Poly%producer_comsumer_example!FifoQueue.State. pre!) (I tail@)
                        )))
                        (and
                         (=>
                          %%location_label%%4
                          tmp%4
                         )
                         (=>
                          tmp%4
                          (=>
                           (= tmp%5 (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T&
                             (Poly%producer_comsumer_example!FifoQueue.State. pre!) (I tail@)
                           ))
                           (and
                            (=>
                             %%location_label%%5
                             tmp%5
                            )
                            (=>
                             tmp%5
                             (=>
                              (= tmp%6 (and
                                (= (vstd!cell.impl&%2.id.? T&. T& perm@) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                                   $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                                     (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                                       pre!
                                    )))
                                   ) (I tail@)
                                )))
                                (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& perm@))
                              ))
                              (and
                               (=>
                                %%location_label%%6
                                (req%vstd!state_machine_internal.assert_safety. tmp%6)
                               )
                               (=>
                                (ens%vstd!state_machine_internal.assert_safety. tmp%6)
                                (=>
                                 %%location_label%%7
                                 (and
                                  (= (vstd!cell.impl&%2.id.? T&. T& perm@) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                                     $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                                       (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                                         pre!
                                      )))
                                     ) (I tail@)
                                  )))
                                  (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& perm@))
 )))))))))))))))))))))))))))))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Specs producer_comsumer_example::FifoQueue::State::produce_end_inductive
(declare-fun req%producer_comsumer_example!FifoQueue.impl&%19.produce_end_inductive.
 (Dcr Type producer_comsumer_example!FifoQueue.State. producer_comsumer_example!FifoQueue.State.
  Poly
 ) Bool
)
(declare-const %%global_location_label%%8 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   ) (perm! Poly)
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.impl&%19.produce_end_inductive. T&. T&
     pre! post! perm!
    ) (=>
     %%global_location_label%%8
     (and
      (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
        pre!
      ))
      (producer_comsumer_example!FifoQueue.impl&%19.produce_end_strong.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
        pre!
       ) (Poly%producer_comsumer_example!FifoQueue.State. post!) perm!
   ))))
   :pattern ((req%producer_comsumer_example!FifoQueue.impl&%19.produce_end_inductive.
     T&. T& pre! post! perm!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.impl&__19.produce_end_inductive._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.impl&__19.produce_end_inductive._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.impl&%19.produce_end_inductive.
 (Dcr Type producer_comsumer_example!FifoQueue.State. producer_comsumer_example!FifoQueue.State.
  Poly
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   ) (perm! Poly)
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.impl&%19.produce_end_inductive. T&. T&
     pre! post! perm!
    ) (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      post!
   )))
   :pattern ((ens%producer_comsumer_example!FifoQueue.impl&%19.produce_end_inductive.
     T&. T& pre! post! perm!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.impl&__19.produce_end_inductive._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.impl&__19.produce_end_inductive._definition
)))

;; Function-Def producer_comsumer_example::FifoQueue::State::produce_end_inductive
;; producer_comsumer_example.rs:367:5: 367:77 (#0)
(get-info :all-statistics)
(push)
 (declare-const T&. Dcr)
 (declare-const T& Type)
 (declare-const pre! producer_comsumer_example!FifoQueue.State.)
 (declare-const post! producer_comsumer_example!FifoQueue.State.)
 (declare-const perm! Poly)
 (declare-const i@ Poly)
 (assert
  fuel_defaults
 )
 (assert
  (sized T&.)
 )
 (assert
  (has_type (Poly%producer_comsumer_example!FifoQueue.State. pre!) (TYPE%producer_comsumer_example!FifoQueue.State.
    T&. T&
 )))
 (assert
  (has_type (Poly%producer_comsumer_example!FifoQueue.State. post!) (TYPE%producer_comsumer_example!FifoQueue.State.
    T&. T&
 )))
 (assert
  (has_type perm! (TYPE%vstd!cell.PointsTo. T&. T&))
 )
 (assert
  (and
   (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
     pre!
   ))
   (producer_comsumer_example!FifoQueue.impl&%19.produce_end_strong.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
     pre!
    ) (Poly%producer_comsumer_example!FifoQueue.State. post!) perm!
 )))
 ;; assertion failed
 (declare-const %%location_label%%0 Bool)
 ;; could not show invariant `not_overlapping` on the `post` state
 (declare-const %%location_label%%1 Bool)
 ;; could not show invariant `in_bounds` on the `post` state
 (declare-const %%location_label%%2 Bool)
 ;; could not show invariant `valid_storage_all` on the `post` state
 (declare-const %%location_label%%3 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%4 Bool)
 (assert
  (not (and
    (=>
     (has_type i@ NAT)
     (=>
      (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
        pre!
       ) i@
      )
      (=>
       %%location_label%%0
       (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
         post!
        ) i@
    ))))
    (=>
     (forall ((i$ Poly)) (!
       (=>
        (has_type i$ NAT)
        (=>
         (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
           pre!
          ) i$
         )
         (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
           post!
          ) i$
       )))
       :pattern ((producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&.
         T& (Poly%producer_comsumer_example!FifoQueue.State. pre!) i$
       ))
       :pattern ((producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&.
         T& (Poly%producer_comsumer_example!FifoQueue.State. post!) i$
       ))
       :qid user_producer_comsumer_example__FifoQueue__State__produce_end_inductive_43
       :skolemid skolem_user_producer_comsumer_example__FifoQueue__State__produce_end_inductive_43
     ))
     (and
      (=>
       %%location_label%%1
       (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping. T&. T&
        post!
      ))
      (=>
       (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping. T&. T&
        post!
       )
       (and
        (=>
         %%location_label%%2
         (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds. T&. T& post!)
        )
        (=>
         (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds. T&. T& post!)
         (and
          (=>
           %%location_label%%3
           (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all. T&.
            T& post!
          ))
          (=>
           (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all. T&.
            T& post!
           )
           (=>
            %%location_label%%4
            (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
              post!
 )))))))))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Def producer_comsumer_example::FifoQueue::State::produce_end_asserts
;; producer_comsumer_example.rs:20:1: 433:3 (#27)
(get-info :all-statistics)
(push)
 (declare-const T&. Dcr)
 (declare-const T& Type)
 (declare-const pre! producer_comsumer_example!FifoQueue.State.)
 (declare-const perm! Poly)
 (declare-const tmp%1 Bool)
 (declare-const tmp%2 Bool)
 (declare-const tmp%3 Bool)
 (declare-const tail@ Int)
 (declare-const next_tail@ Int)
 (declare-const update_tmp_producer$1@ producer_comsumer_example!ProducerState.)
 (declare-const update_tmp_tail$1@ Int)
 (declare-const update_tmp_storage$1@ Poly)
 (declare-const update_tmp_backing_cells@ vstd!seq.Seq<vstd!cell.CellId.>.)
 (declare-const update_tmp_storage@ Poly)
 (declare-const update_tmp_head@ Int)
 (declare-const update_tmp_tail@ Int)
 (declare-const update_tmp_producer@ producer_comsumer_example!ProducerState.)
 (declare-const update_tmp_consumer@ producer_comsumer_example!ConsumerState.)
 (assert
  fuel_defaults
 )
 (assert
  (sized T&.)
 )
 (assert
  (has_type (Poly%producer_comsumer_example!FifoQueue.State. pre!) (TYPE%producer_comsumer_example!FifoQueue.State.
    T&. T&
 )))
 (assert
  (has_type perm! (TYPE%vstd!cell.PointsTo. T&. T&))
 )
 ;; unable to prove assertion safety condition
 (declare-const %%location_label%%0 Bool)
 ;; assertion failed
 (declare-const %%location_label%%1 Bool)
 ;; unable to prove inherent safety condition: the given key must be absent from the map before the deposit
 (declare-const %%location_label%%2 Bool)
 ;; assertion failed
 (declare-const %%location_label%%3 Bool)
 (assert
  (not (=>
    (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      pre!
    ))
    (=>
     (= update_tmp_backing_cells@ (producer_comsumer_example!FifoQueue.State./State/backing_cells
       (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
         pre!
     ))))
     (=>
      (= update_tmp_storage@ (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
         (Poly%producer_comsumer_example!FifoQueue.State. pre!)
      )))
      (=>
       (= update_tmp_head@ (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
          (Poly%producer_comsumer_example!FifoQueue.State. pre!)
       )))
       (=>
        (= update_tmp_tail@ (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
           (Poly%producer_comsumer_example!FifoQueue.State. pre!)
        )))
        (=>
         (= update_tmp_producer@ (producer_comsumer_example!FifoQueue.State./State/producer
           (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
             pre!
         ))))
         (=>
          (= update_tmp_consumer@ (producer_comsumer_example!FifoQueue.State./State/consumer
            (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
              pre!
          ))))
          (=>
           (is-producer_comsumer_example!ProducerState./Producing (producer_comsumer_example!FifoQueue.State./State/producer
             (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
               pre!
           ))))
           (=>
            (= tail@ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
               (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!FifoQueue.State./State/producer
                 (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                   pre!
            )))))))
            (=>
             (= tmp%1 (and
               (<= 0 tail@)
               (< tail@ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                  (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                    (Poly%producer_comsumer_example!FifoQueue.State. pre!)
             )))))))
             (and
              (=>
               %%location_label%%0
               (req%vstd!state_machine_internal.assert_safety. tmp%1)
              )
              (=>
               (ens%vstd!state_machine_internal.assert_safety. tmp%1)
               (=>
                (= next_tail@ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail@)
                  (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                     (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                       (Poly%producer_comsumer_example!FifoQueue.State. pre!)
                )))))))
                (=>
                 (and
                  (= (vstd!cell.impl&%2.id.? T&. T& perm!) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                     $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                       (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                         pre!
                      )))
                     ) (I tail@)
                  )))
                  (is-vstd!raw_ptr.MemContents./Init (vstd!cell.impl&%2.mem_contents.? T&. T& perm!))
                 )
                 (=>
                  (= update_tmp_producer$1@ (producer_comsumer_example!ProducerState./Idle (%I (I next_tail@))))
                  (=>
                   (= update_tmp_tail$1@ next_tail@)
                   (=>
                    (= tmp%2 (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T&
                      (Poly%producer_comsumer_example!FifoQueue.State. pre!) (I tail@)
                    ))
                    (and
                     (=>
                      %%location_label%%1
                      tmp%2
                     )
                     (=>
                      tmp%2
                      (=>
                       (= tmp%3 (not (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                            T&. T&
                           ) update_tmp_storage@
                          ) (I tail@)
                       )))
                       (and
                        (=>
                         %%location_label%%2
                         (req%vstd!state_machine_internal.assert_deposit_map. tmp%3)
                        )
                        (=>
                         (ens%vstd!state_machine_internal.assert_deposit_map. tmp%3)
                         (=>
                          %%location_label%%3
                          (not (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                              T&. T&
                             ) update_tmp_storage@
                            ) (I tail@)
 )))))))))))))))))))))))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Specs producer_comsumer_example::FifoQueue::State::consume_start_inductive
(declare-fun req%producer_comsumer_example!FifoQueue.impl&%19.consume_start_inductive.
 (Dcr Type producer_comsumer_example!FifoQueue.State. producer_comsumer_example!FifoQueue.State.)
 Bool
)
(declare-const %%global_location_label%%9 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   )
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.impl&%19.consume_start_inductive. T&. T&
     pre! post!
    ) (=>
     %%global_location_label%%9
     (and
      (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
        pre!
      ))
      (producer_comsumer_example!FifoQueue.impl&%19.consume_start_strong.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
        pre!
       ) (Poly%producer_comsumer_example!FifoQueue.State. post!)
   ))))
   :pattern ((req%producer_comsumer_example!FifoQueue.impl&%19.consume_start_inductive.
     T&. T& pre! post!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.impl&__19.consume_start_inductive._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.impl&__19.consume_start_inductive._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.impl&%19.consume_start_inductive.
 (Dcr Type producer_comsumer_example!FifoQueue.State. producer_comsumer_example!FifoQueue.State.)
 Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   )
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.impl&%19.consume_start_inductive. T&. T&
     pre! post!
    ) (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      post!
   )))
   :pattern ((ens%producer_comsumer_example!FifoQueue.impl&%19.consume_start_inductive.
     T&. T& pre! post!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.impl&__19.consume_start_inductive._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.impl&__19.consume_start_inductive._definition
)))

;; Function-Def producer_comsumer_example::FifoQueue::State::consume_start_inductive
;; producer_comsumer_example.rs:390:5: 390:54 (#0)
(get-info :all-statistics)
(push)
 (declare-const T&. Dcr)
 (declare-const T& Type)
 (declare-const pre! producer_comsumer_example!FifoQueue.State.)
 (declare-const post! producer_comsumer_example!FifoQueue.State.)
 (declare-const i@ Poly)
 (assert
  fuel_defaults
 )
 (assert
  (sized T&.)
 )
 (assert
  (has_type (Poly%producer_comsumer_example!FifoQueue.State. pre!) (TYPE%producer_comsumer_example!FifoQueue.State.
    T&. T&
 )))
 (assert
  (has_type (Poly%producer_comsumer_example!FifoQueue.State. post!) (TYPE%producer_comsumer_example!FifoQueue.State.
    T&. T&
 )))
 (assert
  (and
   (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
     pre!
   ))
   (producer_comsumer_example!FifoQueue.impl&%19.consume_start_strong.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
     pre!
    ) (Poly%producer_comsumer_example!FifoQueue.State. post!)
 )))
 ;; assertion failed
 (declare-const %%location_label%%0 Bool)
 ;; could not show invariant `not_overlapping` on the `post` state
 (declare-const %%location_label%%1 Bool)
 ;; could not show invariant `in_bounds` on the `post` state
 (declare-const %%location_label%%2 Bool)
 ;; could not show invariant `valid_storage_all` on the `post` state
 (declare-const %%location_label%%3 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%4 Bool)
 (assert
  (not (and
    (=>
     (has_type i@ NAT)
     (=>
      (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
        pre!
       ) i@
      )
      (=>
       %%location_label%%0
       (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
         post!
        ) i@
    ))))
    (=>
     (forall ((i$ Poly)) (!
       (=>
        (has_type i$ NAT)
        (=>
         (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
           pre!
          ) i$
         )
         (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
           post!
          ) i$
       )))
       :pattern ((producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&.
         T& (Poly%producer_comsumer_example!FifoQueue.State. pre!) i$
       ))
       :pattern ((producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&.
         T& (Poly%producer_comsumer_example!FifoQueue.State. post!) i$
       ))
       :qid user_producer_comsumer_example__FifoQueue__State__consume_start_inductive_45
       :skolemid skolem_user_producer_comsumer_example__FifoQueue__State__consume_start_inductive_45
     ))
     (and
      (=>
       %%location_label%%1
       (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping. T&. T&
        post!
      ))
      (=>
       (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping. T&. T&
        post!
       )
       (and
        (=>
         %%location_label%%2
         (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds. T&. T& post!)
        )
        (=>
         (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds. T&. T& post!)
         (and
          (=>
           %%location_label%%3
           (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all. T&.
            T& post!
          ))
          (=>
           (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all. T&.
            T& post!
           )
           (=>
            %%location_label%%4
            (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
              post!
 )))))))))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Def producer_comsumer_example::FifoQueue::State::consume_start_asserts
;; producer_comsumer_example.rs:20:1: 433:3 (#27)
(get-info :all-statistics)
(push)
 (declare-const T&. Dcr)
 (declare-const T& Type)
 (declare-const pre! producer_comsumer_example!FifoQueue.State.)
 (declare-const tmp%1 Bool)
 (declare-const tmp%2 Bool)
 (declare-const tmp%3 Bool)
 (declare-const tmp%4 Bool)
 (declare-const tmp%5 Bool)
 (declare-const tmp%6 Bool)
 (declare-const tmp%7 Bool)
 (declare-const tmp%8 Bool)
 (declare-const perm@ Poly)
 (declare-const update_tmp_storage$1@ Poly)
 (declare-const head@ Int)
 (declare-const tail@ Int)
 (declare-const update_tmp_consumer$1@ producer_comsumer_example!ConsumerState.)
 (declare-const update_tmp_backing_cells@ vstd!seq.Seq<vstd!cell.CellId.>.)
 (declare-const update_tmp_storage@ Poly)
 (declare-const update_tmp_head@ Int)
 (declare-const update_tmp_tail@ Int)
 (declare-const update_tmp_producer@ producer_comsumer_example!ProducerState.)
 (declare-const update_tmp_consumer@ producer_comsumer_example!ConsumerState.)
 (assert
  fuel_defaults
 )
 (assert
  (sized T&.)
 )
 (assert
  (has_type (Poly%producer_comsumer_example!FifoQueue.State. pre!) (TYPE%producer_comsumer_example!FifoQueue.State.
    T&. T&
 )))
 ;; unable to prove assertion safety condition
 (declare-const %%location_label%%0 Bool)
 ;; assertion failed
 (declare-const %%location_label%%1 Bool)
 ;; unable to prove inherent safety condition: the value to be withdrawn must be stored at the given key before the withdraw
 (declare-const %%location_label%%2 Bool)
 ;; assertion failed
 (declare-const %%location_label%%3 Bool)
 ;; assertion failed
 (declare-const %%location_label%%4 Bool)
 ;; unable to prove assertion safety condition
 (declare-const %%location_label%%5 Bool)
 ;; assertion failed
 (declare-const %%location_label%%6 Bool)
 ;; assertion failed
 (declare-const %%location_label%%7 Bool)
 ;; assertion failed
 (declare-const %%location_label%%8 Bool)
 ;; unable to prove assertion safety condition
 (declare-const %%location_label%%9 Bool)
 ;; assertion failed
 (declare-const %%location_label%%10 Bool)
 (assert
  (not (=>
    (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      pre!
    ))
    (=>
     (= update_tmp_backing_cells@ (producer_comsumer_example!FifoQueue.State./State/backing_cells
       (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
         pre!
     ))))
     (=>
      (= update_tmp_storage@ (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
         (Poly%producer_comsumer_example!FifoQueue.State. pre!)
      )))
      (=>
       (= update_tmp_head@ (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
          (Poly%producer_comsumer_example!FifoQueue.State. pre!)
       )))
       (=>
        (= update_tmp_tail@ (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
           (Poly%producer_comsumer_example!FifoQueue.State. pre!)
        )))
        (=>
         (= update_tmp_producer@ (producer_comsumer_example!FifoQueue.State./State/producer
           (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
             pre!
         ))))
         (=>
          (= update_tmp_consumer@ (producer_comsumer_example!FifoQueue.State./State/consumer
            (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
              pre!
          ))))
          (=>
           (is-producer_comsumer_example!ConsumerState./Idle (producer_comsumer_example!FifoQueue.State./State/consumer
             (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
               pre!
           ))))
           (=>
            (= head@ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
               (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!FifoQueue.State./State/consumer
                 (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                   pre!
            )))))))
            (=>
             (= tail@ (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
                (Poly%producer_comsumer_example!FifoQueue.State. pre!)
             )))
             (=>
              (= tmp%1 (and
                (<= 0 head@)
                (< head@ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                   (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                     (Poly%producer_comsumer_example!FifoQueue.State. pre!)
              )))))))
              (and
               (=>
                %%location_label%%0
                (req%vstd!state_machine_internal.assert_safety. tmp%1)
               )
               (=>
                (ens%vstd!state_machine_internal.assert_safety. tmp%1)
                (=>
                 (not (= head@ tail@))
                 (=>
                  (= update_tmp_consumer$1@ (producer_comsumer_example!ConsumerState./Consuming (%I (I
                      head@
                  ))))
                  (=>
                   (= perm@ (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) (producer_comsumer_example!FifoQueue.State./State/storage
                      (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                        pre!
                      ))
                     ) (I head@)
                   ))
                   (and
                    (=>
                     (= tmp%2 (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T&
                       (Poly%producer_comsumer_example!FifoQueue.State. pre!) (I head@)
                     ))
                     (and
                      (=>
                       %%location_label%%1
                       tmp%2
                      )
                      (=>
                       tmp%2
                       (=>
                        (= tmp%3 (vstd!map_lib.impl&%0.contains_pair.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&.
                           T&
                          ) update_tmp_storage@ (I head@) perm@
                        ))
                        (and
                         (=>
                          %%location_label%%2
                          (req%vstd!state_machine_internal.assert_withdraw_map. tmp%3)
                         )
                         (=>
                          (ens%vstd!state_machine_internal.assert_withdraw_map. tmp%3)
                          (=>
                           %%location_label%%3
                           (vstd!map_lib.impl&%0.contains_pair.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) update_tmp_storage@
                            (I head@) perm@
                    ))))))))
                    (=>
                     (vstd!map_lib.impl&%0.contains_pair.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) update_tmp_storage@
                      (I head@) perm@
                     )
                     (=>
                      (= update_tmp_storage$1@ (vstd!map.impl&%0.remove.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                         T&. T&
                        ) update_tmp_storage@ (I head@)
                      ))
                      (and
                       (=>
                        (= tmp%4 (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T&
                          (Poly%producer_comsumer_example!FifoQueue.State. pre!) (I head@)
                        ))
                        (and
                         (=>
                          %%location_label%%4
                          tmp%4
                         )
                         (=>
                          tmp%4
                          (=>
                           (= tmp%5 (= (vstd!cell.impl&%2.id.? T&. T& perm@) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                               $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                                 (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                                   pre!
                                )))
                               ) (I head@)
                           ))))
                           (and
                            (=>
                             %%location_label%%5
                             (req%vstd!state_machine_internal.assert_safety. tmp%5)
                            )
                            (=>
                             (ens%vstd!state_machine_internal.assert_safety. tmp%5)
                             (=>
                              %%location_label%%6
                              (= (vstd!cell.impl&%2.id.? T&. T& perm@) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                                 $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                                   (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                                     pre!
                                  )))
                                 ) (I head@)
                       ))))))))))
                       (=>
                        (= (vstd!cell.impl&%2.id.? T&. T& perm@) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                           $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                             (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                               pre!
                            )))
                           ) (I head@)
                        )))
                        (=>
                         (= tmp%6 (producer_comsumer_example!FifoQueue.impl&%19.in_active_range.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
                            pre!
                           ) (I head@)
                         ))
                         (and
                          (=>
                           %%location_label%%7
                           tmp%6
                          )
                          (=>
                           tmp%6
                           (=>
                            (= tmp%7 (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T&
                              (Poly%producer_comsumer_example!FifoQueue.State. pre!) (I head@)
                            ))
                            (and
                             (=>
                              %%location_label%%8
                              tmp%7
                             )
                             (=>
                              tmp%7
                              (=>
                               (= tmp%8 (is-vstd!raw_ptr.MemContents./Init (vstd!cell.impl&%2.mem_contents.? T&. T&
                                  perm@
                               )))
                               (and
                                (=>
                                 %%location_label%%9
                                 (req%vstd!state_machine_internal.assert_safety. tmp%8)
                                )
                                (=>
                                 (ens%vstd!state_machine_internal.assert_safety. tmp%8)
                                 (=>
                                  %%location_label%%10
                                  (is-vstd!raw_ptr.MemContents./Init (vstd!cell.impl&%2.mem_contents.? T&. T& perm@))
 )))))))))))))))))))))))))))))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Specs producer_comsumer_example::FifoQueue::State::consume_end_inductive
(declare-fun req%producer_comsumer_example!FifoQueue.impl&%19.consume_end_inductive.
 (Dcr Type producer_comsumer_example!FifoQueue.State. producer_comsumer_example!FifoQueue.State.
  Poly
 ) Bool
)
(declare-const %%global_location_label%%10 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   ) (perm! Poly)
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.impl&%19.consume_end_inductive. T&. T&
     pre! post! perm!
    ) (=>
     %%global_location_label%%10
     (and
      (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
        pre!
      ))
      (producer_comsumer_example!FifoQueue.impl&%19.consume_end_strong.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
        pre!
       ) (Poly%producer_comsumer_example!FifoQueue.State. post!) perm!
   ))))
   :pattern ((req%producer_comsumer_example!FifoQueue.impl&%19.consume_end_inductive.
     T&. T& pre! post! perm!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.impl&__19.consume_end_inductive._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.impl&__19.consume_end_inductive._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.impl&%19.consume_end_inductive.
 (Dcr Type producer_comsumer_example!FifoQueue.State. producer_comsumer_example!FifoQueue.State.
  Poly
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (pre! producer_comsumer_example!FifoQueue.State.) (post!
    producer_comsumer_example!FifoQueue.State.
   ) (perm! Poly)
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.impl&%19.consume_end_inductive. T&. T&
     pre! post! perm!
    ) (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      post!
   )))
   :pattern ((ens%producer_comsumer_example!FifoQueue.impl&%19.consume_end_inductive.
     T&. T& pre! post! perm!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.impl&__19.consume_end_inductive._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.impl&__19.consume_end_inductive._definition
)))

;; Function-Def producer_comsumer_example::FifoQueue::State::consume_end_inductive
;; producer_comsumer_example.rs:397:5: 397:77 (#0)
(get-info :all-statistics)
(push)
 (declare-const T&. Dcr)
 (declare-const T& Type)
 (declare-const pre! producer_comsumer_example!FifoQueue.State.)
 (declare-const post! producer_comsumer_example!FifoQueue.State.)
 (declare-const perm! Poly)
 (declare-const tmp%1 Bool)
 (declare-const tmp%2 Bool)
 (declare-const tmp%3 Bool)
 (declare-const tmp%4 Bool)
 (declare-const tail@ Int)
 (declare-const head$1@ Int)
 (declare-const tmp%5 Bool)
 (declare-const tail$1@ Int)
 (declare-const head$2@ Int)
 (declare-const tmp%6 Bool)
 (declare-const tail$2@ Int)
 (declare-const head$3@ Int)
 (declare-const tmp%7 Bool)
 (declare-const tail$3@ Int)
 (declare-const head$4@ Int)
 (declare-const tmp%%@ tuple%2.)
 (declare-const tmp%8 Bool)
 (declare-const tmp%9 Bool)
 (declare-const tmp%10 Bool)
 (declare-const i@ Poly)
 (declare-const head@ Int)
 (assert
  fuel_defaults
 )
 (assert
  (sized T&.)
 )
 (assert
  (has_type (Poly%producer_comsumer_example!FifoQueue.State. pre!) (TYPE%producer_comsumer_example!FifoQueue.State.
    T&. T&
 )))
 (assert
  (has_type (Poly%producer_comsumer_example!FifoQueue.State. post!) (TYPE%producer_comsumer_example!FifoQueue.State.
    T&. T&
 )))
 (assert
  (has_type perm! (TYPE%vstd!cell.PointsTo. T&. T&))
 )
 (assert
  (and
   (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
     pre!
   ))
   (producer_comsumer_example!FifoQueue.impl&%19.consume_end_strong.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
     pre!
    ) (Poly%producer_comsumer_example!FifoQueue.State. post!) perm!
 )))
 (declare-const %%switch_label%%0 Bool)
 (declare-const %%switch_label%%1 Bool)
 (declare-const %%switch_label%%2 Bool)
 ;; assertion failed
 (declare-const %%location_label%%0 Bool)
 ;; assertion failed
 (declare-const %%location_label%%1 Bool)
 ;; assertion failed
 (declare-const %%location_label%%2 Bool)
 ;; assertion failed
 (declare-const %%location_label%%3 Bool)
 ;; assertion failed
 (declare-const %%location_label%%4 Bool)
 ;; assertion failed
 (declare-const %%location_label%%5 Bool)
 ;; assertion failed
 (declare-const %%location_label%%6 Bool)
 ;; assertion failed
 (declare-const %%location_label%%7 Bool)
 ;; assertion failed
 (declare-const %%location_label%%8 Bool)
 ;; assertion failed
 (declare-const %%location_label%%9 Bool)
 ;; assertion failed
 (declare-const %%location_label%%10 Bool)
 ;; could not show invariant `not_overlapping` on the `post` state
 (declare-const %%location_label%%11 Bool)
 ;; could not show invariant `in_bounds` on the `post` state
 (declare-const %%location_label%%12 Bool)
 ;; could not show invariant `valid_storage_all` on the `post` state
 (declare-const %%location_label%%13 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%14 Bool)
 (assert
  (not (=>
    (= head@ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
       (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!FifoQueue.State./State/consumer
         (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
           pre!
    )))))))
    (=>
     (= tmp%1 (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
         T&. T&
        ) (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
          (Poly%producer_comsumer_example!FifoQueue.State. post!)
        ))
       ) (I head@)
     ))
     (and
      (=>
       %%location_label%%0
       tmp%1
      )
      (=>
       tmp%1
       (=>
        (= tmp%2 (= (vstd!cell.impl&%2.id.? T&. T& (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo.
             T&. T&
            ) (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
              (Poly%producer_comsumer_example!FifoQueue.State. post!)
             )
            ) (I head@)
           )
          ) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
             (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
               (Poly%producer_comsumer_example!FifoQueue.State. post!)
             ))
            ) (I head@)
        ))))
        (and
         (=>
          %%location_label%%1
          tmp%2
         )
         (=>
          tmp%2
          (=>
           (= tmp%3 (ite
             (producer_comsumer_example!FifoQueue.impl&%19.in_active_range.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
               post!
              ) (I head@)
             )
             (is-vstd!raw_ptr.MemContents./Init (vstd!cell.impl&%2.mem_contents.? T&. T& (vstd!map.impl&%0.index.?
                $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) (producer_comsumer_example!FifoQueue.State./State/storage
                 (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                   post!
                 ))
                ) (I head@)
             )))
             (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& (vstd!map.impl&%0.index.?
                $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) (producer_comsumer_example!FifoQueue.State./State/storage
                 (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                   post!
                 ))
                ) (I head@)
           )))))
           (and
            (=>
             %%location_label%%2
             tmp%3
            )
            (=>
             tmp%3
             (=>
              (= tmp%%@ (tuple%2./tuple%2 (Poly%producer_comsumer_example!ProducerState. (producer_comsumer_example!FifoQueue.State./State/producer
                  (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                    pre!
                 )))
                ) (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!FifoQueue.State./State/consumer
                  (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                    pre!
              ))))))
              (or
               (and
                (=>
                 (and
                  (and
                   (is-tuple%2./tuple%2 tmp%%@)
                   (is-producer_comsumer_example!ProducerState./Producing (%Poly%producer_comsumer_example!ProducerState.
                     (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                  )))
                  (is-producer_comsumer_example!ConsumerState./Idle (%Poly%producer_comsumer_example!ConsumerState.
                    (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                 )))
                 (=>
                  (= tail@ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
                     (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                  )))
                  (=>
                   (= head$1@ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
                      (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                   )))
                   (=>
                    (= tmp%4 (not (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                         (Poly%producer_comsumer_example!FifoQueue.State. pre!)
                        )
                       ) (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
                         (Poly%producer_comsumer_example!FifoQueue.State. pre!)
                    )))))
                    (and
                     (=>
                      %%location_label%%3
                      tmp%4
                     )
                     (=>
                      tmp%4
                      %%switch_label%%0
                ))))))
                (=>
                 (not (and
                   (and
                    (is-tuple%2./tuple%2 tmp%%@)
                    (is-producer_comsumer_example!ProducerState./Producing (%Poly%producer_comsumer_example!ProducerState.
                      (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                   )))
                   (is-producer_comsumer_example!ConsumerState./Idle (%Poly%producer_comsumer_example!ConsumerState.
                     (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                 ))))
                 (or
                  (and
                   (=>
                    (and
                     (and
                      (is-tuple%2./tuple%2 tmp%%@)
                      (is-producer_comsumer_example!ProducerState./Producing (%Poly%producer_comsumer_example!ProducerState.
                        (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                     )))
                     (is-producer_comsumer_example!ConsumerState./Consuming (%Poly%producer_comsumer_example!ConsumerState.
                       (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                    )))
                    (=>
                     (= tail$1@ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
                        (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                     )))
                     (=>
                      (= head$2@ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
                         (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                      )))
                      (=>
                       (= tmp%5 (not (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                            (Poly%producer_comsumer_example!FifoQueue.State. pre!)
                           )
                          ) (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
                            (Poly%producer_comsumer_example!FifoQueue.State. pre!)
                       )))))
                       (and
                        (=>
                         %%location_label%%4
                         tmp%5
                        )
                        (=>
                         tmp%5
                         %%switch_label%%1
                   ))))))
                   (=>
                    (not (and
                      (and
                       (is-tuple%2./tuple%2 tmp%%@)
                       (is-producer_comsumer_example!ProducerState./Producing (%Poly%producer_comsumer_example!ProducerState.
                         (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                      )))
                      (is-producer_comsumer_example!ConsumerState./Consuming (%Poly%producer_comsumer_example!ConsumerState.
                        (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                    ))))
                    (or
                     (and
                      (=>
                       (and
                        (and
                         (is-tuple%2./tuple%2 tmp%%@)
                         (is-producer_comsumer_example!ProducerState./Idle (%Poly%producer_comsumer_example!ProducerState.
                           (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                        )))
                        (is-producer_comsumer_example!ConsumerState./Idle (%Poly%producer_comsumer_example!ConsumerState.
                          (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                       )))
                       (=>
                        (= tail$2@ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
                           (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                        )))
                        (=>
                         (= head$3@ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
                            (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                         )))
                         (=>
                          (= tmp%6 (not (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                               (Poly%producer_comsumer_example!FifoQueue.State. pre!)
                              )
                             ) (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
                               (Poly%producer_comsumer_example!FifoQueue.State. pre!)
                          )))))
                          (and
                           (=>
                            %%location_label%%5
                            tmp%6
                           )
                           (=>
                            tmp%6
                            %%switch_label%%2
                      ))))))
                      (=>
                       (not (and
                         (and
                          (is-tuple%2./tuple%2 tmp%%@)
                          (is-producer_comsumer_example!ProducerState./Idle (%Poly%producer_comsumer_example!ProducerState.
                            (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                         )))
                         (is-producer_comsumer_example!ConsumerState./Idle (%Poly%producer_comsumer_example!ConsumerState.
                           (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                       ))))
                       (=>
                        (= tail$3@ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
                           (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                        )))
                        (=>
                         (= head$4@ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
                            (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%@)))
                         )))
                         (=>
                          (= tmp%7 (not (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                               (Poly%producer_comsumer_example!FifoQueue.State. pre!)
                              )
                             ) (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
                               (Poly%producer_comsumer_example!FifoQueue.State. pre!)
                          )))))
                          (and
                           (=>
                            %%location_label%%6
                            tmp%7
                           )
                           (=>
                            tmp%7
                            %%switch_label%%2
                     )))))))
                     (and
                      (not %%switch_label%%2)
                      %%switch_label%%1
                  ))))
                  (and
                   (not %%switch_label%%1)
                   %%switch_label%%0
               ))))
               (and
                (not %%switch_label%%0)
                (=>
                 (= tmp%8 (not (= (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
                      (Poly%producer_comsumer_example!FifoQueue.State. pre!)
                     )
                    ) (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
                      (Poly%producer_comsumer_example!FifoQueue.State. pre!)
                 )))))
                 (and
                  (=>
                   %%location_label%%7
                   tmp%8
                  )
                  (=>
                   tmp%8
                   (=>
                    (= tmp%9 (not (producer_comsumer_example!FifoQueue.impl&%19.is_checked_out.? T&. T&
                       (Poly%producer_comsumer_example!FifoQueue.State. post!) (I head@)
                    )))
                    (and
                     (=>
                      %%location_label%%8
                      tmp%9
                     )
                     (=>
                      tmp%9
                      (=>
                       (= tmp%10 (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&.
                         T& (Poly%producer_comsumer_example!FifoQueue.State. post!) (I head@)
                       ))
                       (and
                        (=>
                         %%location_label%%9
                         tmp%10
                        )
                        (=>
                         tmp%10
                         (and
                          (=>
                           (has_type i@ NAT)
                           (=>
                            (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
                              pre!
                             ) i@
                            )
                            (=>
                             %%location_label%%10
                             (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
                               post!
                              ) i@
                          ))))
                          (=>
                           (forall ((i$ Poly)) (!
                             (=>
                              (has_type i$ NAT)
                              (=>
                               (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
                                 pre!
                                ) i$
                               )
                               (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
                                 post!
                                ) i$
                             )))
                             :pattern ((producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&.
                               T& (Poly%producer_comsumer_example!FifoQueue.State. pre!) i$
                             ))
                             :pattern ((producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&.
                               T& (Poly%producer_comsumer_example!FifoQueue.State. post!) i$
                             ))
                             :qid user_producer_comsumer_example__FifoQueue__State__consume_end_inductive_49
                             :skolemid skolem_user_producer_comsumer_example__FifoQueue__State__consume_end_inductive_49
                           ))
                           (and
                            (=>
                             %%location_label%%11
                             (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping. T&. T&
                              post!
                            ))
                            (=>
                             (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_not_overlapping. T&. T&
                              post!
                             )
                             (and
                              (=>
                               %%location_label%%12
                               (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds. T&. T& post!)
                              )
                              (=>
                               (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_in_bounds. T&. T& post!)
                               (and
                                (=>
                                 %%location_label%%13
                                 (req%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all. T&.
                                  T& post!
                                ))
                                (=>
                                 (ens%producer_comsumer_example!FifoQueue.impl&%19.lemma_msg_valid_storage_all. T&.
                                  T& post!
                                 )
                                 (=>
                                  %%location_label%%14
                                  (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
                                    post!
 )))))))))))))))))))))))))))))))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Def producer_comsumer_example::FifoQueue::State::consume_end_asserts
;; producer_comsumer_example.rs:20:1: 433:3 (#27)
(get-info :all-statistics)
(push)
 (declare-const T&. Dcr)
 (declare-const T& Type)
 (declare-const pre! producer_comsumer_example!FifoQueue.State.)
 (declare-const perm! Poly)
 (declare-const tmp%1 Bool)
 (declare-const tmp%2 Bool)
 (declare-const tmp%3 Bool)
 (declare-const head@ Int)
 (declare-const next_head@ Int)
 (declare-const update_tmp_consumer$1@ producer_comsumer_example!ConsumerState.)
 (declare-const update_tmp_head$1@ Int)
 (declare-const update_tmp_storage$1@ Poly)
 (declare-const update_tmp_backing_cells@ vstd!seq.Seq<vstd!cell.CellId.>.)
 (declare-const update_tmp_storage@ Poly)
 (declare-const update_tmp_head@ Int)
 (declare-const update_tmp_tail@ Int)
 (declare-const update_tmp_producer@ producer_comsumer_example!ProducerState.)
 (declare-const update_tmp_consumer@ producer_comsumer_example!ConsumerState.)
 (assert
  fuel_defaults
 )
 (assert
  (sized T&.)
 )
 (assert
  (has_type (Poly%producer_comsumer_example!FifoQueue.State. pre!) (TYPE%producer_comsumer_example!FifoQueue.State.
    T&. T&
 )))
 (assert
  (has_type perm! (TYPE%vstd!cell.PointsTo. T&. T&))
 )
 ;; unable to prove assertion safety condition
 (declare-const %%location_label%%0 Bool)
 ;; assertion failed
 (declare-const %%location_label%%1 Bool)
 ;; unable to prove inherent safety condition: the given key must be absent from the map before the deposit
 (declare-const %%location_label%%2 Bool)
 ;; assertion failed
 (declare-const %%location_label%%3 Bool)
 (assert
  (not (=>
    (producer_comsumer_example!FifoQueue.impl&%19.invariant.? T&. T& (Poly%producer_comsumer_example!FifoQueue.State.
      pre!
    ))
    (=>
     (= update_tmp_backing_cells@ (producer_comsumer_example!FifoQueue.State./State/backing_cells
       (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
         pre!
     ))))
     (=>
      (= update_tmp_storage@ (producer_comsumer_example!FifoQueue.State./State/storage (%Poly%producer_comsumer_example!FifoQueue.State.
         (Poly%producer_comsumer_example!FifoQueue.State. pre!)
      )))
      (=>
       (= update_tmp_head@ (producer_comsumer_example!FifoQueue.State./State/head (%Poly%producer_comsumer_example!FifoQueue.State.
          (Poly%producer_comsumer_example!FifoQueue.State. pre!)
       )))
       (=>
        (= update_tmp_tail@ (producer_comsumer_example!FifoQueue.State./State/tail (%Poly%producer_comsumer_example!FifoQueue.State.
           (Poly%producer_comsumer_example!FifoQueue.State. pre!)
        )))
        (=>
         (= update_tmp_producer@ (producer_comsumer_example!FifoQueue.State./State/producer
           (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
             pre!
         ))))
         (=>
          (= update_tmp_consumer@ (producer_comsumer_example!FifoQueue.State./State/consumer
            (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
              pre!
          ))))
          (=>
           (is-producer_comsumer_example!ConsumerState./Consuming (producer_comsumer_example!FifoQueue.State./State/consumer
             (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
               pre!
           ))))
           (=>
            (= head@ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
               (Poly%producer_comsumer_example!ConsumerState. (producer_comsumer_example!FifoQueue.State./State/consumer
                 (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                   pre!
            )))))))
            (=>
             (= tmp%1 (and
               (<= 0 head@)
               (< head@ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                  (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                    (Poly%producer_comsumer_example!FifoQueue.State. pre!)
             )))))))
             (and
              (=>
               %%location_label%%0
               (req%vstd!state_machine_internal.assert_safety. tmp%1)
              )
              (=>
               (ens%vstd!state_machine_internal.assert_safety. tmp%1)
               (=>
                (= next_head@ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I head@)
                  (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                     (producer_comsumer_example!FifoQueue.State./State/backing_cells (%Poly%producer_comsumer_example!FifoQueue.State.
                       (Poly%producer_comsumer_example!FifoQueue.State. pre!)
                )))))))
                (=>
                 (= update_tmp_consumer$1@ (producer_comsumer_example!ConsumerState./Idle (%I (I next_head@))))
                 (=>
                  (= update_tmp_head$1@ next_head@)
                  (=>
                   (and
                    (= (vstd!cell.impl&%2.id.? T&. T& perm!) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                       $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.State./State/backing_cells
                         (%Poly%producer_comsumer_example!FifoQueue.State. (Poly%producer_comsumer_example!FifoQueue.State.
                           pre!
                        )))
                       ) (I head@)
                    )))
                    (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& perm!))
                   )
                   (=>
                    (= tmp%2 (producer_comsumer_example!FifoQueue.impl&%19.valid_storage_at_idx.? T&. T&
                      (Poly%producer_comsumer_example!FifoQueue.State. pre!) (I head@)
                    ))
                    (and
                     (=>
                      %%location_label%%1
                      tmp%2
                     )
                     (=>
                      tmp%2
                      (=>
                       (= tmp%3 (not (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                            T&. T&
                           ) update_tmp_storage@
                          ) (I head@)
                       )))
                       (and
                        (=>
                         %%location_label%%2
                         (req%vstd!state_machine_internal.assert_deposit_map. tmp%3)
                        )
                        (=>
                         (ens%vstd!state_machine_internal.assert_deposit_map. tmp%3)
                         (=>
                          %%location_label%%3
                          (not (vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
                              T&. T&
                             ) update_tmp_storage@
                            ) (I head@)
 )))))))))))))))))))))))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Specs producer_comsumer_example::FifoQueue::Instance::initialize
(declare-fun req%producer_comsumer_example!FifoQueue.impl&%16.initialize. (Dcr Type
  vstd!seq.Seq<vstd!cell.CellId.>. Poly Poly
 ) Bool
)
(declare-const %%global_location_label%%11 Bool)
(declare-const %%global_location_label%%12 Bool)
(declare-const %%global_location_label%%13 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (backing_cells! vstd!seq.Seq<vstd!cell.CellId.>.) (storage!
    Poly
   ) (param_token_storage! Poly)
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.impl&%16.initialize. T&. T& backing_cells!
     storage! param_token_storage!
    ) (and
     (=>
      %%global_location_label%%11
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ NAT)
         (=>
          (and
           (<= 0 (%I i$))
           (< (%I i$) (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
              backing_cells!
          ))))
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
             ) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                backing_cells!
               ) i$
           ))))
           (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& (vstd!map.impl&%0.index.?
              $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) storage! i$
        ))))))
        :pattern ((vstd!set.Set.contains.? $ NAT (vstd!map.impl&%0.dom.? $ NAT $ (TYPE%vstd!cell.PointsTo.
            T&. T&
           ) storage!
          ) i$
        ))
        :qid user_producer_comsumer_example__FifoQueue__Instance__initialize_51
        :skolemid skolem_user_producer_comsumer_example__FifoQueue__Instance__initialize_51
     )))
     (=>
      %%global_location_label%%12
      (> (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
         backing_cells!
        )
       ) 0
     ))
     (=>
      %%global_location_label%%13
      (= param_token_storage! storage!)
   )))
   :pattern ((req%producer_comsumer_example!FifoQueue.impl&%16.initialize. T&. T& backing_cells!
     storage! param_token_storage!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.impl&__16.initialize._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.impl&__16.initialize._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.impl&%16.initialize. (Dcr Type
  vstd!seq.Seq<vstd!cell.CellId.>. Poly Poly tuple%5.
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (backing_cells! vstd!seq.Seq<vstd!cell.CellId.>.) (storage!
    Poly
   ) (param_token_storage! Poly) (tmp_tuple! tuple%5.)
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.impl&%16.initialize. T&. T& backing_cells!
     storage! param_token_storage! tmp_tuple!
    ) (and
     (has_type (Poly%tuple%5. tmp_tuple!) (TYPE%tuple%5. (TRACKED $) (TYPE%producer_comsumer_example!FifoQueue.Instance.
        T&. T&
       ) (TRACKED $) (TYPE%producer_comsumer_example!FifoQueue.head. T&. T&) (TRACKED $)
       (TYPE%producer_comsumer_example!FifoQueue.tail. T&. T&) (TRACKED $) (TYPE%producer_comsumer_example!FifoQueue.producer.
        T&. T&
       ) (TRACKED $) (TYPE%producer_comsumer_example!FifoQueue.consumer. T&. T&)
     ))
     (let
      ((instance$ (%Poly%producer_comsumer_example!FifoQueue.Instance. (tuple%5./tuple%5/0
          (%Poly%tuple%5. (Poly%tuple%5. tmp_tuple!))
      ))))
      (let
       ((param_token_head$ (%Poly%producer_comsumer_example!FifoQueue.head. (tuple%5./tuple%5/1
           (%Poly%tuple%5. (Poly%tuple%5. tmp_tuple!))
       ))))
       (let
        ((param_token_tail$ (%Poly%producer_comsumer_example!FifoQueue.tail. (tuple%5./tuple%5/2
            (%Poly%tuple%5. (Poly%tuple%5. tmp_tuple!))
        ))))
        (let
         ((param_token_producer$ (%Poly%producer_comsumer_example!FifoQueue.producer. (tuple%5./tuple%5/3
             (%Poly%tuple%5. (Poly%tuple%5. tmp_tuple!))
         ))))
         (let
          ((param_token_consumer$ (%Poly%producer_comsumer_example!FifoQueue.consumer. (tuple%5./tuple%5/4
              (%Poly%tuple%5. (Poly%tuple%5. tmp_tuple!))
          ))))
          (let
           ((instance$1 instance$))
           (let
            ((param_token_head$1 param_token_head$))
            (let
             ((param_token_tail$1 param_token_tail$))
             (let
              ((param_token_producer$1 param_token_producer$))
              (let
               ((param_token_consumer$1 param_token_consumer$))
               (and
                (and
                 (and
                  (and
                   (and
                    (and
                     (and
                      (and
                       (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.head.
                           T&. T&
                          ) $ NAT (Poly%producer_comsumer_example!FifoQueue.head. param_token_head$1)
                         )
                        ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                          instance$1
                       )))
                       (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.tail.
                           T&. T&
                          ) $ NAT (Poly%producer_comsumer_example!FifoQueue.tail. param_token_tail$1)
                         )
                        ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                          instance$1
                      ))))
                      (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
                          T&. T&
                         ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
                          param_token_producer$1
                        ))
                       ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                         instance$1
                     ))))
                     (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
                         T&. T&
                        ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
                         param_token_consumer$1
                       ))
                      ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                        instance$1
                    ))))
                    (= (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                       instance$1
                      )
                     ) backing_cells!
                   ))
                   (= (%I (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.head.
                       T&. T&
                      ) $ NAT (Poly%producer_comsumer_example!FifoQueue.head. param_token_head$1)
                     )
                    ) 0
                  ))
                  (= (%I (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.tail.
                      T&. T&
                     ) $ NAT (Poly%producer_comsumer_example!FifoQueue.tail. param_token_tail$1)
                    )
                   ) 0
                 ))
                 (= (%Poly%producer_comsumer_example!ProducerState. (vstd!tokens.ValueToken.value.? $
                    (TYPE%producer_comsumer_example!FifoQueue.producer. T&. T&) $ TYPE%producer_comsumer_example!ProducerState.
                    (Poly%producer_comsumer_example!FifoQueue.producer. param_token_producer$1)
                   )
                  ) (producer_comsumer_example!ProducerState./Idle (%I (I 0)))
                ))
                (= (%Poly%producer_comsumer_example!ConsumerState. (vstd!tokens.ValueToken.value.? $
                   (TYPE%producer_comsumer_example!FifoQueue.consumer. T&. T&) $ TYPE%producer_comsumer_example!ConsumerState.
                   (Poly%producer_comsumer_example!FifoQueue.consumer. param_token_consumer$1)
                  )
                 ) (producer_comsumer_example!ConsumerState./Idle (%I (I 0)))
   ))))))))))))))
   :pattern ((ens%producer_comsumer_example!FifoQueue.impl&%16.initialize. T&. T& backing_cells!
     storage! param_token_storage! tmp_tuple!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.impl&__16.initialize._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.impl&__16.initialize._definition
)))

;; Function-Specs producer_comsumer_example::FifoQueue::Instance::produce_start
(declare-fun req%producer_comsumer_example!FifoQueue.impl&%16.produce_start. (Dcr Type
  producer_comsumer_example!FifoQueue.Instance. producer_comsumer_example!FifoQueue.head.
  producer_comsumer_example!FifoQueue.producer.
 ) Bool
)
(declare-const %%global_location_label%%14 Bool)
(declare-const %%global_location_label%%15 Bool)
(declare-const %%global_location_label%%16 Bool)
(declare-const %%global_location_label%%17 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (self! producer_comsumer_example!FifoQueue.Instance.)
   (param_token_head! producer_comsumer_example!FifoQueue.head.) (pre%param_token_producer!
    producer_comsumer_example!FifoQueue.producer.
   )
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.impl&%16.produce_start. T&. T& self! param_token_head!
     pre%param_token_producer!
    ) (and
     (=>
      %%global_location_label%%14
      (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.head.
          T&. T&
         ) $ NAT (Poly%producer_comsumer_example!FifoQueue.head. param_token_head!)
        )
       ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
         self!
     ))))
     (=>
      %%global_location_label%%15
      (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
          T&. T&
         ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
          pre%param_token_producer!
        ))
       ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
         self!
     ))))
     (=>
      %%global_location_label%%16
      (is-producer_comsumer_example!ProducerState./Idle (%Poly%producer_comsumer_example!ProducerState.
        (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
          T&. T&
         ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
          pre%param_token_producer!
     )))))
     (=>
      %%global_location_label%%17
      (let
       ((tail$ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
           (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
             T&. T&
            ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
             pre%param_token_producer!
       ))))))
       (let
        ((head$ (%I (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.head.
             T&. T&
            ) $ NAT (Poly%producer_comsumer_example!FifoQueue.head. param_token_head!)
        ))))
        (=>
         (and
          (<= 0 tail$)
          (< tail$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
             (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
               self!
         ))))))
         (let
          ((next_tail$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$)
             (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                  self!
          ))))))))
          (not (= next_tail$ head$))
   )))))))
   :pattern ((req%producer_comsumer_example!FifoQueue.impl&%16.produce_start. T&. T& self!
     param_token_head! pre%param_token_producer!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.impl&__16.produce_start._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.impl&__16.produce_start._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.impl&%16.produce_start. (Dcr Type
  producer_comsumer_example!FifoQueue.Instance. producer_comsumer_example!FifoQueue.head.
  producer_comsumer_example!FifoQueue.producer. producer_comsumer_example!FifoQueue.producer.
  Poly
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (self! producer_comsumer_example!FifoQueue.Instance.)
   (param_token_head! producer_comsumer_example!FifoQueue.head.) (pre%param_token_producer!
    producer_comsumer_example!FifoQueue.producer.
   ) (param_token_producer! producer_comsumer_example!FifoQueue.producer.) (param_token_0_storage!
    Poly
   )
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.impl&%16.produce_start. T&. T& self! param_token_head!
     pre%param_token_producer! param_token_producer! param_token_0_storage!
    ) (and
     (has_type param_token_0_storage! (TYPE%vstd!cell.PointsTo. T&. T&))
     (has_type (Poly%producer_comsumer_example!FifoQueue.producer. param_token_producer!)
      (TYPE%producer_comsumer_example!FifoQueue.producer. T&. T&)
     )
     (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
         T&. T&
        ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
         param_token_producer!
       ))
      ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
        self!
     )))
     (let
      ((tail$ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
          (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
            T&. T&
           ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
            pre%param_token_producer!
      ))))))
      (let
       ((head$ (%I (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.head.
            T&. T&
           ) $ NAT (Poly%producer_comsumer_example!FifoQueue.head. param_token_head!)
       ))))
       (and
        (<= 0 tail$)
        (< tail$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
           (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
             self!
     ))))))))
     (let
      ((tail$ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
          (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
            T&. T&
           ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
            pre%param_token_producer!
      ))))))
      (let
       ((head$ (%I (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.head.
            T&. T&
           ) $ NAT (Poly%producer_comsumer_example!FifoQueue.head. param_token_head!)
       ))))
       (let
        ((next_tail$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$)
           (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
              (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                self!
        ))))))))
        (let
         ((perm$ param_token_0_storage!))
         (and
          (= (vstd!cell.impl&%2.id.? T&. T& perm$) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
             $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.?
               T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance. self!)
              )
             ) (I tail$)
          )))
          (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& perm$))
     )))))
     (= (%Poly%producer_comsumer_example!ProducerState. (vstd!tokens.ValueToken.value.? $
        (TYPE%producer_comsumer_example!FifoQueue.producer. T&. T&) $ TYPE%producer_comsumer_example!ProducerState.
        (Poly%producer_comsumer_example!FifoQueue.producer. param_token_producer!)
       )
      ) (let
       ((tail$ (producer_comsumer_example!ProducerState./Idle/0 (%Poly%producer_comsumer_example!ProducerState.
           (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
             T&. T&
            ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
             pre%param_token_producer!
       ))))))
       (let
        ((head$ (%I (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.head.
             T&. T&
            ) $ NAT (Poly%producer_comsumer_example!FifoQueue.head. param_token_head!)
        ))))
        (let
         ((next_tail$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$)
            (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
               (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                 self!
         ))))))))
         (producer_comsumer_example!ProducerState./Producing (%I (I tail$)))
   ))))))
   :pattern ((ens%producer_comsumer_example!FifoQueue.impl&%16.produce_start. T&. T& self!
     param_token_head! pre%param_token_producer! param_token_producer! param_token_0_storage!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.impl&__16.produce_start._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.impl&__16.produce_start._definition
)))

;; Function-Specs producer_comsumer_example::FifoQueue::Instance::produce_end
(declare-fun req%producer_comsumer_example!FifoQueue.impl&%16.produce_end. (Dcr Type
  producer_comsumer_example!FifoQueue.Instance. Poly Poly producer_comsumer_example!FifoQueue.tail.
  producer_comsumer_example!FifoQueue.producer.
 ) Bool
)
(declare-const %%global_location_label%%18 Bool)
(declare-const %%global_location_label%%19 Bool)
(declare-const %%global_location_label%%20 Bool)
(declare-const %%global_location_label%%21 Bool)
(declare-const %%global_location_label%%22 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (self! producer_comsumer_example!FifoQueue.Instance.)
   (perm! Poly) (param_token_0_storage! Poly) (pre%param_token_tail! producer_comsumer_example!FifoQueue.tail.)
   (pre%param_token_producer! producer_comsumer_example!FifoQueue.producer.)
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.impl&%16.produce_end. T&. T& self! perm!
     param_token_0_storage! pre%param_token_tail! pre%param_token_producer!
    ) (and
     (=>
      %%global_location_label%%18
      (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.tail.
          T&. T&
         ) $ NAT (Poly%producer_comsumer_example!FifoQueue.tail. pre%param_token_tail!)
        )
       ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
         self!
     ))))
     (=>
      %%global_location_label%%19
      (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
          T&. T&
         ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
          pre%param_token_producer!
        ))
       ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
         self!
     ))))
     (=>
      %%global_location_label%%20
      (is-producer_comsumer_example!ProducerState./Producing (%Poly%producer_comsumer_example!ProducerState.
        (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
          T&. T&
         ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
          pre%param_token_producer!
     )))))
     (=>
      %%global_location_label%%21
      (let
       ((tail$ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
           (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
             T&. T&
            ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
             pre%param_token_producer!
       ))))))
       (=>
        (and
         (<= 0 tail$)
         (< tail$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
            (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
              self!
        ))))))
        (let
         ((next_tail$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$)
            (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
               (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                 self!
         ))))))))
         (and
          (= (vstd!cell.impl&%2.id.? T&. T& perm!) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
             $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.?
               T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance. self!)
              )
             ) (I tail$)
          )))
          (is-vstd!raw_ptr.MemContents./Init (vstd!cell.impl&%2.mem_contents.? T&. T& perm!))
     )))))
     (=>
      %%global_location_label%%22
      (let
       ((tail$ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
           (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
             T&. T&
            ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
             pre%param_token_producer!
       ))))))
       (=>
        (and
         (<= 0 tail$)
         (< tail$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
            (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
              self!
        ))))))
        (let
         ((next_tail$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$)
            (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
               (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                 self!
         ))))))))
         (= param_token_0_storage! perm!)
   ))))))
   :pattern ((req%producer_comsumer_example!FifoQueue.impl&%16.produce_end. T&. T& self!
     perm! param_token_0_storage! pre%param_token_tail! pre%param_token_producer!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.impl&__16.produce_end._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.impl&__16.produce_end._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.impl&%16.produce_end. (Dcr Type
  producer_comsumer_example!FifoQueue.Instance. Poly Poly producer_comsumer_example!FifoQueue.tail.
  producer_comsumer_example!FifoQueue.tail. producer_comsumer_example!FifoQueue.producer.
  producer_comsumer_example!FifoQueue.producer.
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (self! producer_comsumer_example!FifoQueue.Instance.)
   (perm! Poly) (param_token_0_storage! Poly) (pre%param_token_tail! producer_comsumer_example!FifoQueue.tail.)
   (param_token_tail! producer_comsumer_example!FifoQueue.tail.) (pre%param_token_producer!
    producer_comsumer_example!FifoQueue.producer.
   ) (param_token_producer! producer_comsumer_example!FifoQueue.producer.)
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.impl&%16.produce_end. T&. T& self! perm!
     param_token_0_storage! pre%param_token_tail! param_token_tail! pre%param_token_producer!
     param_token_producer!
    ) (and
     (has_type (Poly%producer_comsumer_example!FifoQueue.tail. param_token_tail!) (TYPE%producer_comsumer_example!FifoQueue.tail.
       T&. T&
     ))
     (has_type (Poly%producer_comsumer_example!FifoQueue.producer. param_token_producer!)
      (TYPE%producer_comsumer_example!FifoQueue.producer. T&. T&)
     )
     (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.tail.
         T&. T&
        ) $ NAT (Poly%producer_comsumer_example!FifoQueue.tail. param_token_tail!)
       )
      ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
        self!
     )))
     (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
         T&. T&
        ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
         param_token_producer!
       ))
      ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
        self!
     )))
     (let
      ((tail$ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
          (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
            T&. T&
           ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
            pre%param_token_producer!
      ))))))
      (and
       (<= 0 tail$)
       (< tail$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
          (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
            self!
     )))))))
     (= (%I (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.tail.
         T&. T&
        ) $ NAT (Poly%producer_comsumer_example!FifoQueue.tail. param_token_tail!)
       )
      ) (let
       ((tail$ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
           (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
             T&. T&
            ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
             pre%param_token_producer!
       ))))))
       (let
        ((next_tail$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$)
           (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
              (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                self!
        ))))))))
        next_tail$
     )))
     (= (%Poly%producer_comsumer_example!ProducerState. (vstd!tokens.ValueToken.value.? $
        (TYPE%producer_comsumer_example!FifoQueue.producer. T&. T&) $ TYPE%producer_comsumer_example!ProducerState.
        (Poly%producer_comsumer_example!FifoQueue.producer. param_token_producer!)
       )
      ) (let
       ((tail$ (producer_comsumer_example!ProducerState./Producing/0 (%Poly%producer_comsumer_example!ProducerState.
           (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.producer.
             T&. T&
            ) $ TYPE%producer_comsumer_example!ProducerState. (Poly%producer_comsumer_example!FifoQueue.producer.
             pre%param_token_producer!
       ))))))
       (let
        ((next_tail$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I tail$)
           (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
              (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                self!
        ))))))))
        (producer_comsumer_example!ProducerState./Idle (%I (I next_tail$)))
   )))))
   :pattern ((ens%producer_comsumer_example!FifoQueue.impl&%16.produce_end. T&. T& self!
     perm! param_token_0_storage! pre%param_token_tail! param_token_tail! pre%param_token_producer!
     param_token_producer!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.impl&__16.produce_end._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.impl&__16.produce_end._definition
)))

;; Function-Specs producer_comsumer_example::FifoQueue::Instance::consume_start
(declare-fun req%producer_comsumer_example!FifoQueue.impl&%16.consume_start. (Dcr Type
  producer_comsumer_example!FifoQueue.Instance. producer_comsumer_example!FifoQueue.tail.
  producer_comsumer_example!FifoQueue.consumer.
 ) Bool
)
(declare-const %%global_location_label%%23 Bool)
(declare-const %%global_location_label%%24 Bool)
(declare-const %%global_location_label%%25 Bool)
(declare-const %%global_location_label%%26 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (self! producer_comsumer_example!FifoQueue.Instance.)
   (param_token_tail! producer_comsumer_example!FifoQueue.tail.) (pre%param_token_consumer!
    producer_comsumer_example!FifoQueue.consumer.
   )
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.impl&%16.consume_start. T&. T& self! param_token_tail!
     pre%param_token_consumer!
    ) (and
     (=>
      %%global_location_label%%23
      (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.tail.
          T&. T&
         ) $ NAT (Poly%producer_comsumer_example!FifoQueue.tail. param_token_tail!)
        )
       ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
         self!
     ))))
     (=>
      %%global_location_label%%24
      (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
          T&. T&
         ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
          pre%param_token_consumer!
        ))
       ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
         self!
     ))))
     (=>
      %%global_location_label%%25
      (is-producer_comsumer_example!ConsumerState./Idle (%Poly%producer_comsumer_example!ConsumerState.
        (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
          T&. T&
         ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
          pre%param_token_consumer!
     )))))
     (=>
      %%global_location_label%%26
      (let
       ((head$ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
           (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
             T&. T&
            ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
             pre%param_token_consumer!
       ))))))
       (let
        ((tail$ (%I (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.tail.
             T&. T&
            ) $ NAT (Poly%producer_comsumer_example!FifoQueue.tail. param_token_tail!)
        ))))
        (=>
         (and
          (<= 0 head$)
          (< head$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
             (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
               self!
         ))))))
         (not (= head$ tail$))
   ))))))
   :pattern ((req%producer_comsumer_example!FifoQueue.impl&%16.consume_start. T&. T& self!
     param_token_tail! pre%param_token_consumer!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.impl&__16.consume_start._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.impl&__16.consume_start._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.impl&%16.consume_start. (Dcr Type
  producer_comsumer_example!FifoQueue.Instance. producer_comsumer_example!FifoQueue.tail.
  producer_comsumer_example!FifoQueue.consumer. producer_comsumer_example!FifoQueue.consumer.
  tuple%2.
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (self! producer_comsumer_example!FifoQueue.Instance.)
   (param_token_tail! producer_comsumer_example!FifoQueue.tail.) (pre%param_token_consumer!
    producer_comsumer_example!FifoQueue.consumer.
   ) (param_token_consumer! producer_comsumer_example!FifoQueue.consumer.) (tmp_tuple!
    tuple%2.
   )
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.impl&%16.consume_start. T&. T& self! param_token_tail!
     pre%param_token_consumer! param_token_consumer! tmp_tuple!
    ) (and
     (has_type (Poly%tuple%2. tmp_tuple!) (TYPE%tuple%2. (GHOST $) (TYPE%vstd!map.Map. $
        NAT $ (TYPE%vstd!cell.PointsTo. T&. T&)
       ) (TRACKED $) (TYPE%vstd!cell.PointsTo. T&. T&)
     ))
     (has_type (Poly%producer_comsumer_example!FifoQueue.consumer. param_token_consumer!)
      (TYPE%producer_comsumer_example!FifoQueue.consumer. T&. T&)
     )
     (let
      ((original_field_storage$ (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp_tuple!)))))
      (let
       ((param_token_0_storage$ (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp_tuple!)))))
       (let
        ((original_field_storage$1 original_field_storage$))
        (let
         ((param_token_0_storage$1 param_token_0_storage$))
         (and
          (and
           (and
            (and
             (and
              (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
                  T&. T&
                 ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
                  param_token_consumer!
                ))
               ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                 self!
              )))
              (let
               ((head$ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
                   (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
                     T&. T&
                    ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
                     pre%param_token_consumer!
               ))))))
               (let
                ((tail$ (%I (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.tail.
                     T&. T&
                    ) $ NAT (Poly%producer_comsumer_example!FifoQueue.tail. param_token_tail!)
                ))))
                (and
                 (<= 0 head$)
                 (< head$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
                    (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                      self!
             )))))))))
             (let
              ((head$ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
                  (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
                    T&. T&
                   ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
                    pre%param_token_consumer!
              ))))))
              (let
               ((tail$ (%I (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.tail.
                    T&. T&
                   ) $ NAT (Poly%producer_comsumer_example!FifoQueue.tail. param_token_tail!)
               ))))
               (let
                ((perm$ (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) original_field_storage$1
                   (I head$)
                )))
                (= param_token_0_storage$1 perm$)
            ))))
            (let
             ((head$ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
                 (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
                   T&. T&
                  ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
                   pre%param_token_consumer!
             ))))))
             (let
              ((tail$ (%I (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.tail.
                   T&. T&
                  ) $ NAT (Poly%producer_comsumer_example!FifoQueue.tail. param_token_tail!)
              ))))
              (let
               ((perm$ (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) original_field_storage$1
                  (I head$)
               )))
               (= (vstd!cell.impl&%2.id.? T&. T& perm$) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
                  $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.?
                    T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance. self!)
                   )
                  ) (I head$)
           )))))))
           (let
            ((head$ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
                (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
                  T&. T&
                 ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
                  pre%param_token_consumer!
            ))))))
            (let
             ((tail$ (%I (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.tail.
                  T&. T&
                 ) $ NAT (Poly%producer_comsumer_example!FifoQueue.tail. param_token_tail!)
             ))))
             (let
              ((perm$ (vstd!map.impl&%0.index.? $ NAT $ (TYPE%vstd!cell.PointsTo. T&. T&) original_field_storage$1
                 (I head$)
              )))
              (is-vstd!raw_ptr.MemContents./Init (vstd!cell.impl&%2.mem_contents.? T&. T& perm$))
          ))))
          (= (%Poly%producer_comsumer_example!ConsumerState. (vstd!tokens.ValueToken.value.? $
             (TYPE%producer_comsumer_example!FifoQueue.consumer. T&. T&) $ TYPE%producer_comsumer_example!ConsumerState.
             (Poly%producer_comsumer_example!FifoQueue.consumer. param_token_consumer!)
            )
           ) (let
            ((head$ (producer_comsumer_example!ConsumerState./Idle/0 (%Poly%producer_comsumer_example!ConsumerState.
                (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
                  T&. T&
                 ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
                  pre%param_token_consumer!
            ))))))
            (let
             ((tail$ (%I (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.tail.
                  T&. T&
                 ) $ NAT (Poly%producer_comsumer_example!FifoQueue.tail. param_token_tail!)
             ))))
             (producer_comsumer_example!ConsumerState./Consuming (%I (I head$)))
   ))))))))))
   :pattern ((ens%producer_comsumer_example!FifoQueue.impl&%16.consume_start. T&. T& self!
     param_token_tail! pre%param_token_consumer! param_token_consumer! tmp_tuple!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.impl&__16.consume_start._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.impl&__16.consume_start._definition
)))

;; Function-Specs producer_comsumer_example::FifoQueue::Instance::consume_end
(declare-fun req%producer_comsumer_example!FifoQueue.impl&%16.consume_end. (Dcr Type
  producer_comsumer_example!FifoQueue.Instance. Poly Poly producer_comsumer_example!FifoQueue.head.
  producer_comsumer_example!FifoQueue.consumer.
 ) Bool
)
(declare-const %%global_location_label%%27 Bool)
(declare-const %%global_location_label%%28 Bool)
(declare-const %%global_location_label%%29 Bool)
(declare-const %%global_location_label%%30 Bool)
(declare-const %%global_location_label%%31 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (self! producer_comsumer_example!FifoQueue.Instance.)
   (perm! Poly) (param_token_0_storage! Poly) (pre%param_token_head! producer_comsumer_example!FifoQueue.head.)
   (pre%param_token_consumer! producer_comsumer_example!FifoQueue.consumer.)
  ) (!
   (= (req%producer_comsumer_example!FifoQueue.impl&%16.consume_end. T&. T& self! perm!
     param_token_0_storage! pre%param_token_head! pre%param_token_consumer!
    ) (and
     (=>
      %%global_location_label%%27
      (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.head.
          T&. T&
         ) $ NAT (Poly%producer_comsumer_example!FifoQueue.head. pre%param_token_head!)
        )
       ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
         self!
     ))))
     (=>
      %%global_location_label%%28
      (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
          T&. T&
         ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
          pre%param_token_consumer!
        ))
       ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
         self!
     ))))
     (=>
      %%global_location_label%%29
      (is-producer_comsumer_example!ConsumerState./Consuming (%Poly%producer_comsumer_example!ConsumerState.
        (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
          T&. T&
         ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
          pre%param_token_consumer!
     )))))
     (=>
      %%global_location_label%%30
      (let
       ((head$ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
           (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
             T&. T&
            ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
             pre%param_token_consumer!
       ))))))
       (=>
        (and
         (<= 0 head$)
         (< head$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
            (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
              self!
        ))))))
        (let
         ((next_head$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I head$)
            (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
               (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                 self!
         ))))))))
         (and
          (= (vstd!cell.impl&%2.id.? T&. T& perm!) (%Poly%vstd!cell.CellId. (vstd!seq.Seq.index.?
             $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>. (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.?
               T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance. self!)
              )
             ) (I head$)
          )))
          (is-vstd!raw_ptr.MemContents./Uninit (vstd!cell.impl&%2.mem_contents.? T&. T& perm!))
     )))))
     (=>
      %%global_location_label%%31
      (let
       ((head$ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
           (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
             T&. T&
            ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
             pre%param_token_consumer!
       ))))))
       (=>
        (and
         (<= 0 head$)
         (< head$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
            (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
              self!
        ))))))
        (let
         ((next_head$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I head$)
            (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
               (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                 self!
         ))))))))
         (= param_token_0_storage! perm!)
   ))))))
   :pattern ((req%producer_comsumer_example!FifoQueue.impl&%16.consume_end. T&. T& self!
     perm! param_token_0_storage! pre%param_token_head! pre%param_token_consumer!
   ))
   :qid internal_req__producer_comsumer_example!FifoQueue.impl&__16.consume_end._definition
   :skolemid skolem_internal_req__producer_comsumer_example!FifoQueue.impl&__16.consume_end._definition
)))
(declare-fun ens%producer_comsumer_example!FifoQueue.impl&%16.consume_end. (Dcr Type
  producer_comsumer_example!FifoQueue.Instance. Poly Poly producer_comsumer_example!FifoQueue.head.
  producer_comsumer_example!FifoQueue.head. producer_comsumer_example!FifoQueue.consumer.
  producer_comsumer_example!FifoQueue.consumer.
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (self! producer_comsumer_example!FifoQueue.Instance.)
   (perm! Poly) (param_token_0_storage! Poly) (pre%param_token_head! producer_comsumer_example!FifoQueue.head.)
   (param_token_head! producer_comsumer_example!FifoQueue.head.) (pre%param_token_consumer!
    producer_comsumer_example!FifoQueue.consumer.
   ) (param_token_consumer! producer_comsumer_example!FifoQueue.consumer.)
  ) (!
   (= (ens%producer_comsumer_example!FifoQueue.impl&%16.consume_end. T&. T& self! perm!
     param_token_0_storage! pre%param_token_head! param_token_head! pre%param_token_consumer!
     param_token_consumer!
    ) (and
     (has_type (Poly%producer_comsumer_example!FifoQueue.head. param_token_head!) (TYPE%producer_comsumer_example!FifoQueue.head.
       T&. T&
     ))
     (has_type (Poly%producer_comsumer_example!FifoQueue.consumer. param_token_consumer!)
      (TYPE%producer_comsumer_example!FifoQueue.consumer. T&. T&)
     )
     (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.head.
         T&. T&
        ) $ NAT (Poly%producer_comsumer_example!FifoQueue.head. param_token_head!)
       )
      ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
        self!
     )))
     (= (%Poly%vstd!tokens.InstanceId. (vstd!tokens.ValueToken.instance_id.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
         T&. T&
        ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
         param_token_consumer!
       ))
      ) (producer_comsumer_example!FifoQueue.impl&%16.id.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
        self!
     )))
     (let
      ((head$ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
          (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
            T&. T&
           ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
            pre%param_token_consumer!
      ))))))
      (and
       (<= 0 head$)
       (< head$ (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
          (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
            self!
     )))))))
     (= (%I (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.head.
         T&. T&
        ) $ NAT (Poly%producer_comsumer_example!FifoQueue.head. param_token_head!)
       )
      ) (let
       ((head$ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
           (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
             T&. T&
            ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
             pre%param_token_consumer!
       ))))))
       (let
        ((next_head$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I head$)
           (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
              (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                self!
        ))))))))
        next_head$
     )))
     (= (%Poly%producer_comsumer_example!ConsumerState. (vstd!tokens.ValueToken.value.? $
        (TYPE%producer_comsumer_example!FifoQueue.consumer. T&. T&) $ TYPE%producer_comsumer_example!ConsumerState.
        (Poly%producer_comsumer_example!FifoQueue.consumer. param_token_consumer!)
       )
      ) (let
       ((head$ (producer_comsumer_example!ConsumerState./Consuming/0 (%Poly%producer_comsumer_example!ConsumerState.
           (vstd!tokens.ValueToken.value.? $ (TYPE%producer_comsumer_example!FifoQueue.consumer.
             T&. T&
            ) $ TYPE%producer_comsumer_example!ConsumerState. (Poly%producer_comsumer_example!FifoQueue.consumer.
             pre%param_token_consumer!
       ))))))
       (let
        ((next_head$ (producer_comsumer_example!FifoQueue.impl&%19.inc_wrap.? T&. T& (I head$)
           (I (vstd!seq.Seq.len.? $ TYPE%vstd!cell.CellId. (Poly%vstd!seq.Seq<vstd!cell.CellId.>.
              (producer_comsumer_example!FifoQueue.impl&%16.backing_cells.? T&. T& (Poly%producer_comsumer_example!FifoQueue.Instance.
                self!
        ))))))))
        (producer_comsumer_example!ConsumerState./Idle (%I (I next_head$)))
   )))))
   :pattern ((ens%producer_comsumer_example!FifoQueue.impl&%16.consume_end. T&. T& self!
     perm! param_token_0_storage! pre%param_token_head! param_token_head! pre%param_token_consumer!
     param_token_consumer!
   ))
   :qid internal_ens__producer_comsumer_example!FifoQueue.impl&__16.consume_end._definition
   :skolemid skolem_internal_ens__producer_comsumer_example!FifoQueue.impl&__16.consume_end._definition
)))
