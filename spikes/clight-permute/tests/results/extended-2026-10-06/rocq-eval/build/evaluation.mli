
val xorb : bool -> bool -> bool

val negb : bool -> bool

type nat =
| O
| S of nat

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type signed_int =
| Pos of uint
| Neg of uint

val revapp : uint -> uint -> uint

val rev : uint -> uint

module Little :
 sig
  val double : uint -> uint

  val succ_double : uint -> uint
 end

val add : nat -> nat -> nat

val bool_dec : bool -> bool -> bool

val eqb : bool -> bool -> bool

module Nat :
 sig
  val eqb : nat -> nat -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val repeat : 'a1 -> nat -> 'a1 list

val rev0 : 'a1 list -> 'a1 list

val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> n

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val ldiff : positive -> positive -> n

  val coq_lxor : positive -> positive -> n

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> n

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val div2 : positive -> positive

  val coq_lor : positive -> positive -> positive

  val size : positive -> positive

  val shiftl_nat : positive -> nat -> positive

  val shiftr_nat : positive -> nat -> positive

  val testbit : positive -> n -> bool

  val to_little_uint : positive -> uint

  val to_uint : positive -> uint

  val eq_dec : positive -> positive -> bool
 end

module N :
 sig
  val succ_double : n -> n

  val double : n -> n

  val succ_pos : n -> positive

  val sub : n -> n -> n

  val compare : n -> n -> comparison

  val leb : n -> n -> bool

  val pos_div_eucl : positive -> n -> n * n

  val coq_lor : n -> n -> n

  val coq_land : n -> n -> n

  val ldiff : n -> n -> n

  val coq_lxor : n -> n -> n
 end

module Coq_N :
 sig
  val testbit : n -> n -> bool

  val eq_dec : n -> n -> bool
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val max : z -> z -> z

  val min : z -> z -> z

  val pos_div_eucl : positive -> z -> z * z

  val div_eucl : z -> z -> z * z

  val even : z -> bool

  val div2 : z -> z

  val shiftl : z -> z -> z
 end

module Coq_Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val pow_pos : z -> positive -> z

  val pow : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val max : z -> z -> z

  val min : z -> z -> z

  val to_nat : z -> nat

  val of_nat : nat -> z

  val of_N : n -> z

  val to_pos : z -> positive

  val pos_div_eucl : positive -> z -> z * z

  val div_eucl : z -> z -> z * z

  val div : z -> z -> z

  val modulo : z -> z -> z

  val quotrem : z -> z -> z * z

  val quot : z -> z -> z

  val rem : z -> z -> z

  val even : z -> bool

  val div2 : z -> z

  val shiftl : z -> z -> z

  val shiftr : z -> z -> z

  val coq_lor : z -> z -> z

  val coq_land : z -> z -> z

  val coq_lxor : z -> z -> z

  val pred : z -> z

  val to_int : z -> signed_int

  val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val odd : z -> bool

  val log2 : z -> z

  val testbit : z -> z -> bool

  val eq_dec : z -> z -> bool
 end

val z_lt_dec : z -> z -> bool

val z_le_dec : z -> z -> bool

val z_le_gt_dec : z -> z -> bool

val zdivide_dec : z -> z -> bool

val shift_nat : nat -> positive -> positive

val shift_pos : positive -> positive -> positive

val two_power_nat : nat -> z

val two_power_pos : positive -> z

val two_p : z -> z

module NilEmpty :
 sig
  val string_of_uint : uint -> char list
 end

module NilZero :
 sig
  val string_of_uint : uint -> char list

  val string_of_int : signed_int -> char list
 end

val peq : positive -> positive -> bool

val zeq : z -> z -> bool

val zlt : z -> z -> bool

val zle : z -> z -> bool

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

val proj_sumbool : bool -> bool

module PTree :
 sig
  type 'a tree' =
  | Node001 of 'a tree'
  | Node010 of 'a
  | Node011 of 'a * 'a tree'
  | Node100 of 'a tree'
  | Node101 of 'a tree' * 'a tree'
  | Node110 of 'a tree' * 'a
  | Node111 of 'a tree' * 'a * 'a tree'

  type 'a tree =
  | Empty
  | Nodes of 'a tree'

  type 'a t = 'a tree

  val empty : 'a1 t

  val get' : positive -> 'a1 tree' -> 'a1 option

  val get : positive -> 'a1 tree -> 'a1 option

  val set0 : positive -> 'a1 -> 'a1 tree'

  val set' : positive -> 'a1 -> 'a1 tree' -> 'a1 tree'

  val set : positive -> 'a1 -> 'a1 tree -> 'a1 tree

  val map1' : ('a1 -> 'a2) -> 'a1 tree' -> 'a2 tree'

  val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module PMap :
 sig
  type 'a t = 'a * 'a PTree.t

  val init : 'a1 -> 'a1 * 'a1 PTree.t

  val get : positive -> 'a1 t -> 'a1

  val set : positive -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.tree

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module type INDEXED_TYPE =
 sig
  type t

  val index : t -> positive

  val eq : t -> t -> bool
 end

module IMap :
 functor (X:INDEXED_TYPE) ->
 sig
  type elt = X.t

  val elt_eq : X.t -> X.t -> bool

  type 'x t = 'x PMap.t

  val init : 'a1 -> 'a1 * 'a1 PTree.t

  val get : X.t -> 'a1 t -> 'a1

  val set : X.t -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.tree

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module ZIndexed :
 sig
  type t = z

  val index : z -> positive

  val eq : z -> z -> bool
 end

module ZMap :
 sig
  type elt = ZIndexed.t

  val elt_eq : ZIndexed.t -> ZIndexed.t -> bool

  type 'x t = 'x PMap.t

  val init : 'a1 -> 'a1 * 'a1 PTree.t

  val get : ZIndexed.t -> 'a1 t -> 'a1

  val set : ZIndexed.t -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.tree

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

val p_mod_two_p : positive -> nat -> z

val zshiftin : bool -> z -> z

val zzero_ext : z -> z -> z

val zsign_ext : z -> z -> z

val z_one_bits : nat -> z -> z -> z list

val p_is_power2 : positive -> bool

val z_is_power2 : z -> z option

val zsize : z -> z

type spec_float =
| S754_zero of bool
| S754_infinity of bool
| S754_nan
| S754_finite of bool * positive * z

val emin : z -> z -> z

val fexp : z -> z -> z -> z

val digits2_pos : positive -> positive

val zdigits2 : z -> z

val iter_pos : ('a1 -> 'a1) -> positive -> 'a1 -> 'a1

type location =
| Loc_Exact
| Loc_Inexact of comparison

type shr_record = { shr_m : z; shr_r : bool; shr_s : bool }

val shr_1 : shr_record -> shr_record

val loc_of_shr_record : shr_record -> location

val shr_record_of_loc : z -> location -> shr_record

val shr : shr_record -> z -> z -> shr_record * z

val shr_fexp : z -> z -> z -> z -> location -> shr_record * z

val shl_align : positive -> z -> z -> positive * z

val sFcompare : spec_float -> spec_float -> comparison option

val cond_Zopp : bool -> z -> z

val new_location_even : z -> z -> location

val new_location_odd : z -> z -> location

val new_location : z -> z -> location

val sFdiv_core_binary : z -> z -> z -> z -> z -> z -> (z * z) * location

type radix = z
  (* singleton inductive, whose constructor was Build_radix *)

val radix2 : radix

val iter_nat : ('a1 -> 'a1) -> nat -> 'a1 -> 'a1

val cond_incr : bool -> z -> z

val round_sign_DN : bool -> location -> bool

val round_sign_UP : bool -> location -> bool

val round_N : bool -> location -> bool

type binary_float =
| B754_zero of bool
| B754_infinity of bool
| B754_nan
| B754_finite of bool * positive * z

val sF2B : z -> z -> spec_float -> binary_float

val b2SF : z -> z -> binary_float -> spec_float

val bcompare : z -> z -> binary_float -> binary_float -> comparison option

type mode =
| Mode_NE
| Mode_ZR
| Mode_DN
| Mode_UP
| Mode_NA

val choice_mode : mode -> bool -> z -> location -> z

val overflow_to_inf : mode -> bool -> bool

val binary_overflow : z -> z -> mode -> bool -> spec_float

val binary_fit_aux : z -> z -> mode -> bool -> positive -> z -> spec_float

val binary_round_aux :
  z -> z -> mode -> bool -> z -> z -> location -> spec_float

val bmult : z -> z -> mode -> binary_float -> binary_float -> binary_float

val shl_align_fexp : z -> z -> positive -> z -> positive * z

val binary_round : z -> z -> mode -> bool -> positive -> z -> spec_float

val binary_normalize : z -> z -> mode -> z -> z -> bool -> binary_float

val fplus_naive : bool -> positive -> z -> bool -> positive -> z -> z -> z

val bplus : z -> z -> mode -> binary_float -> binary_float -> binary_float

val bminus : z -> z -> mode -> binary_float -> binary_float -> binary_float

val bdiv : z -> z -> mode -> binary_float -> binary_float -> binary_float

type full_float =
| F754_zero of bool
| F754_infinity of bool
| F754_nan of bool * positive
| F754_finite of bool * positive * z

type binary_float0 =
| B754_zero0 of bool
| B754_infinity0 of bool
| B754_nan0 of bool * positive
| B754_finite0 of bool * positive * z

val b2BSN : z -> z -> binary_float0 -> binary_float

val fF2B : z -> z -> full_float -> binary_float0

val bsign : z -> z -> binary_float0 -> bool

val get_nan_pl : z -> z -> binary_float0 -> positive

val build_nan : z -> z -> binary_float0 -> binary_float0

val bSN2B : z -> z -> binary_float0 -> binary_float -> binary_float0

val bSN2B' : z -> z -> binary_float -> binary_float0

val bcompare0 : z -> z -> binary_float0 -> binary_float0 -> comparison option

val bmult0 :
  z -> z -> (binary_float0 -> binary_float0 -> binary_float0) -> mode ->
  binary_float0 -> binary_float0 -> binary_float0

val binary_normalize0 : z -> z -> mode -> z -> z -> bool -> binary_float0

val bplus0 :
  z -> z -> (binary_float0 -> binary_float0 -> binary_float0) -> mode ->
  binary_float0 -> binary_float0 -> binary_float0

val bminus0 :
  z -> z -> (binary_float0 -> binary_float0 -> binary_float0) -> mode ->
  binary_float0 -> binary_float0 -> binary_float0

val bdiv0 :
  z -> z -> (binary_float0 -> binary_float0 -> binary_float0) -> mode ->
  binary_float0 -> binary_float0 -> binary_float0

val join_bits : z -> z -> bool -> z -> z -> z

val split_bits : z -> z -> z -> (bool * z) * z

val bits_of_binary_float : z -> z -> binary_float0 -> z

val binary_float_of_bits_aux : z -> z -> z -> full_float

val binary_float_of_bits : z -> z -> z -> binary_float0

type binary32 = binary_float0

val b32_of_bits : z -> binary32

val bits_of_b32 : binary32 -> z

type binary64 = binary_float0

val b64_of_bits : z -> binary64

val bits_of_b64 : binary64 -> z

val ptr64 : bool

val big_endian : bool

val default_nan_64 : bool * positive

val default_nan_32 : bool * positive

val choose_nan_64 : (bool * positive) list -> bool * positive

val choose_nan_32 : (bool * positive) list -> bool * positive

val float_of_single_preserves_sNaN : bool

val float_conversion_default_nan : bool

type comparison0 =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

module type WORDSIZE =
 sig
  val wordsize : nat
 end

module Make :
 functor (WS:WORDSIZE) ->
 sig
  val wordsize : nat

  val zwordsize : z

  val modulus : z

  val half_modulus : z

  val max_unsigned : z

  val max_signed : z

  val min_signed : z

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : z -> int -> int

  val sign_ext : z -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> z -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> z -> int -> z -> bool

  val size : int -> z

  val unsigned_bitfield_extract : z -> z -> int -> int

  val signed_bitfield_extract : z -> z -> int -> int

  val bitfield_insert : z -> z -> int -> int -> int
 end

module Wordsize_32 :
 sig
  val wordsize : nat
 end

module Int :
 sig
  val wordsize : nat

  val zwordsize : z

  val modulus : z

  val half_modulus : z

  val max_unsigned : z

  val max_signed : z

  val min_signed : z

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : z -> int -> int

  val sign_ext : z -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> z -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> z -> int -> z -> bool

  val size : int -> z

  val unsigned_bitfield_extract : z -> z -> int -> int

  val signed_bitfield_extract : z -> z -> int -> int

  val bitfield_insert : z -> z -> int -> int -> int
 end

module Wordsize_8 :
 sig
  val wordsize : nat
 end

module Byte :
 sig
  val wordsize : nat

  val zwordsize : z

  val modulus : z

  val half_modulus : z

  val max_unsigned : z

  val max_signed : z

  val min_signed : z

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : z -> int -> int

  val sign_ext : z -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> z -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> z -> int -> z -> bool

  val size : int -> z

  val unsigned_bitfield_extract : z -> z -> int -> int

  val signed_bitfield_extract : z -> z -> int -> int

  val bitfield_insert : z -> z -> int -> int -> int
 end

module Wordsize_64 :
 sig
  val wordsize : nat
 end

module Int64 :
 sig
  val wordsize : nat

  val zwordsize : z

  val modulus : z

  val half_modulus : z

  val max_unsigned : z

  val max_signed : z

  val min_signed : z

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val iwordsize' : Int.int

  val loword : int -> Int.int
 end

module Wordsize_Ptrofs :
 sig
  val wordsize : nat
 end

module Ptrofs :
 sig
  val wordsize : nat

  val modulus : z

  val half_modulus : z

  val max_signed : z

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val ltu : int -> int -> bool

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val cmpu : comparison0 -> int -> int -> bool

  val to_int : int -> Int.int

  val to_int64 : int -> Int64.int

  val of_int : Int.int -> int

  val of_intu : Int.int -> int

  val of_ints : Int.int -> int

  val of_int64 : Int64.int -> int
 end

val beq_dec : z -> z -> binary_float0 -> binary_float0 -> bool

val bofZ : z -> z -> z -> binary_float0

val zofB : z -> z -> binary_float0 -> z option

val zofB_range : z -> z -> binary_float0 -> z -> z -> z option

val bconv :
  z -> z -> z -> z -> (binary_float0 -> binary_float0) -> mode ->
  binary_float0 -> binary_float0

type float = binary64

type float32 = binary32

val cmp_of_comparison : comparison0 -> comparison option -> bool

val quiet_nan_64_payload : positive -> positive

val quiet_nan_64 : (bool * positive) -> float

val default_nan_0 : float

val quiet_nan_32_payload : positive -> positive

val quiet_nan_32 : (bool * positive) -> float32

val default_nan_1 : float32

module Float :
 sig
  val expand_nan_payload : positive -> positive

  val expand_nan : bool -> positive -> binary_float0

  val of_single_nan : float32 -> float

  val reduce_nan_payload : positive -> positive

  val to_single_nan : float -> float32

  val cons_pl : float -> (bool * positive) list -> (bool * positive) list

  val binop_nan : float -> float -> float

  val zero : float

  val eq_dec : float -> float -> bool

  val add : float -> float -> float

  val sub : float -> float -> float

  val mul : float -> float -> float

  val div : float -> float -> float

  val compare : float -> float -> comparison option

  val cmp : comparison0 -> float -> float -> bool

  val of_single : float32 -> float

  val to_single : float -> float32

  val to_int : float -> Int.int option

  val to_intu : float -> Int.int option

  val to_long : float -> Int64.int option

  val to_longu : float -> Int64.int option

  val of_int : Int.int -> float

  val of_intu : Int.int -> float

  val of_long : Int64.int -> float

  val of_longu : Int64.int -> float

  val to_bits : float -> Int64.int

  val of_bits : Int64.int -> float
 end

module Float32 :
 sig
  val cons_pl : float32 -> (bool * positive) list -> (bool * positive) list

  val binop_nan : float32 -> float32 -> float32

  val zero : float32

  val eq_dec : float32 -> float32 -> bool

  val add : float32 -> float32 -> float32

  val sub : float32 -> float32 -> float32

  val mul : float32 -> float32 -> float32

  val div : float32 -> float32 -> float32

  val compare : float32 -> float32 -> comparison option

  val cmp : comparison0 -> float32 -> float32 -> bool

  val to_int : float32 -> Int.int option

  val to_intu : float32 -> Int.int option

  val to_long : float32 -> Int64.int option

  val to_longu : float32 -> Int64.int option

  val of_int : Int.int -> float32

  val of_intu : Int.int -> float32

  val of_long : Int64.int -> float32

  val of_longu : Int64.int -> float32

  val to_bits : float32 -> Int.int

  val of_bits : Int.int -> float32
 end

type ident = positive

val ident_eq : positive -> positive -> bool

type typ =
| Tint
| Tfloat
| Tlong
| Tsingle
| Tany32
| Tany64

type xtype =
| Xbool
| Xint8signed
| Xint8unsigned
| Xint16signed
| Xint16unsigned
| Xint
| Xfloat
| Xlong
| Xsingle
| Xptr
| Xany32
| Xany64
| Xvoid

type calling_convention = { cc_vararg : z option; cc_unproto : bool;
                            cc_structret : bool }

val cc_default : calling_convention

val calling_convention_eq : calling_convention -> calling_convention -> bool

type signature = { sig_args : xtype list; sig_res : xtype;
                   sig_cc : calling_convention }

type memory_chunk =
| Mbool
| Mint8signed
| Mint8unsigned
| Mint16signed
| Mint16unsigned
| Mint32
| Mint64
| Mfloat32
| Mfloat64
| Many32
| Many64

val mptr : memory_chunk

type init_data =
| Init_int8 of Int.int
| Init_int16 of Int.int
| Init_int32 of Int.int
| Init_int64 of Int64.int
| Init_float32 of float32
| Init_float64 of float
| Init_space of z
| Init_addrof of ident * Ptrofs.int

type 'v globvar = { gvar_info : 'v; gvar_init : init_data list;
                    gvar_readonly : bool; gvar_volatile : bool }

type ('f, 'v) globdef =
| Gfun of 'f
| Gvar of 'v globvar

type external_function =
| EF_external of char list * signature
| EF_builtin of char list * signature
| EF_runtime of char list * signature
| EF_vload of memory_chunk
| EF_vstore of memory_chunk
| EF_malloc
| EF_free
| EF_memcpy of z * z
| EF_annot of positive * char list * typ list
| EF_annot_val of positive * char list * typ
| EF_inline_asm of char list * signature * char list list
| EF_debug of positive * ident * typ list

type block = positive

val eq_block : positive -> positive -> bool

type val0 =
| Vundef
| Vint of Int.int
| Vlong of Int64.int
| Vfloat of float
| Vsingle of float32
| Vptr of block * Ptrofs.int

val vzero : val0

val vone : val0

val vtrue : val0

val vfalse : val0

val vptrofs : Ptrofs.int -> val0

module Val :
 sig
  val eq : val0 -> val0 -> bool

  val of_bool : bool -> val0

  val is_bool : val0 -> bool

  val norm_bool : val0 -> val0

  val cmp_different_blocks : comparison0 -> bool option

  val cmpu_bool :
    (block -> z -> bool) -> comparison0 -> val0 -> val0 -> bool option

  val cmplu_bool :
    (block -> z -> bool) -> comparison0 -> val0 -> val0 -> bool option

  val load_result : memory_chunk -> val0 -> val0
 end

val size_chunk : memory_chunk -> z

val size_chunk_nat : memory_chunk -> nat

val align_chunk : memory_chunk -> z

type quantity =
| Q32
| Q64

val quantity_eq : quantity -> quantity -> bool

val size_quantity_nat : quantity -> nat

type memval =
| Undef
| Byte of Byte.int
| Fragment of val0 * quantity * nat

val bytes_of_int : nat -> z -> Byte.int list

val int_of_bytes : Byte.int list -> z

val rev_if_be : Byte.int list -> Byte.int list

val encode_int : nat -> z -> Byte.int list

val decode_int : Byte.int list -> z

val inj_bytes : Byte.int list -> memval list

val proj_bytes : memval list -> Byte.int list option

val inj_value_rec : nat -> val0 -> quantity -> memval list

val inj_value : quantity -> val0 -> memval list

val check_value : nat -> val0 -> quantity -> memval list -> bool

val proj_value : quantity -> memval list -> val0

val encode_val : memory_chunk -> val0 -> memval list

val decode_val : memory_chunk -> memval list -> val0

type permission =
| Freeable
| Writable
| Readable
| Nonempty

type perm_kind =
| Max
| Cur

module Mem :
 sig
  type mem' = { mem_contents : memval ZMap.t PMap.t;
                mem_access : (z -> perm_kind -> permission option) PMap.t;
                nextblock : block }

  val mem_contents : mem' -> memval ZMap.t PMap.t

  val mem_access : mem' -> (z -> perm_kind -> permission option) PMap.t

  val nextblock : mem' -> block

  type mem = mem'

  val perm_order_dec : permission -> permission -> bool

  val perm_order'_dec : permission option -> permission -> bool

  val perm_dec : mem -> block -> z -> perm_kind -> permission -> bool

  val range_perm_dec :
    mem -> block -> z -> z -> perm_kind -> permission -> bool

  val valid_access_dec :
    mem -> memory_chunk -> block -> z -> permission -> bool

  val valid_pointer : mem -> block -> z -> bool

  val weak_valid_pointer : mem -> block -> z -> bool

  val empty : mem

  val alloc : mem -> z -> z -> mem' * block

  val getN : nat -> z -> memval ZMap.t -> memval list

  val load : memory_chunk -> mem -> block -> z -> val0 option

  val loadv : memory_chunk -> mem -> val0 -> val0 option

  val setN : memval list -> z -> memval ZMap.t -> memval ZMap.t

  val store : memory_chunk -> mem -> block -> z -> val0 -> mem option

  val storev : memory_chunk -> mem -> val0 -> val0 -> mem option
 end

module Genv :
 sig
  type ('f, 'v) t = { genv_public : ident list; genv_symb : block PTree.t;
                      genv_defs : ('f, 'v) globdef PTree.t; genv_next : 
                      block }

  val empty_genv : ident list -> ('a1, 'a2) t
 end

type signedness =
| Signed
| Unsigned

type intsize =
| I8
| I16
| I32
| IBool

type floatsize =
| F32
| F64

type attr = { attr_volatile : bool; attr_alignas : n option }

val noattr : attr

type type0 =
| Tvoid
| Tint0 of intsize * signedness * attr
| Tlong0 of signedness * attr
| Tfloat0 of floatsize * attr
| Tpointer of type0 * attr
| Tarray of type0 * z * attr
| Tfunction of type0 list * type0 * calling_convention
| Tstruct of ident * attr
| Tunion of ident * attr

val intsize_eq : intsize -> intsize -> bool

val signedness_eq : signedness -> signedness -> bool

val floatsize_eq : floatsize -> floatsize -> bool

val attr_eq : attr -> attr -> bool

val type_eq : type0 -> type0 -> bool

val change_attributes : (attr -> attr) -> type0 -> type0

val remove_attributes : type0 -> type0

type struct_or_union =
| Struct
| Union

type member =
| Member_plain of ident * type0
| Member_bitfield of ident * intsize * signedness * attr * z * bool

type members = member list

type composite = { co_su : struct_or_union; co_members : members;
                   co_attr : attr; co_sizeof : z; co_alignof : z;
                   co_rank : nat }

type composite_env = composite PTree.t

val typeconv : type0 -> type0

val sizeof : composite_env -> type0 -> z

type mode0 =
| By_value of memory_chunk
| By_reference
| By_copy
| By_nothing

val access_mode : type0 -> mode0

type 'f fundef =
| Internal of 'f
| External of external_function * type0 list * type0 * calling_convention

type unary_operation =
| Onotbool
| Onotint
| Oneg
| Oabsfloat

type binary_operation =
| Oadd
| Osub
| Omul
| Odiv
| Omod
| Oand
| Oor
| Oxor
| Oshl
| Oshr
| Oeq
| One
| Olt
| Ogt
| Ole
| Oge

type classify_cast_cases =
| Cast_case_pointer
| Cast_case_i2i of intsize * signedness
| Cast_case_f2f
| Cast_case_s2s
| Cast_case_f2s
| Cast_case_s2f
| Cast_case_i2f of signedness
| Cast_case_i2s of signedness
| Cast_case_f2i of intsize * signedness
| Cast_case_s2i of intsize * signedness
| Cast_case_l2l
| Cast_case_i2l of signedness
| Cast_case_l2i of intsize * signedness
| Cast_case_l2f of signedness
| Cast_case_l2s of signedness
| Cast_case_f2l of signedness
| Cast_case_s2l of signedness
| Cast_case_i2bool
| Cast_case_l2bool
| Cast_case_f2bool
| Cast_case_s2bool
| Cast_case_struct of ident * ident
| Cast_case_union of ident * ident
| Cast_case_void
| Cast_case_default

val classify_cast : type0 -> type0 -> classify_cast_cases

val cast_int_int : intsize -> signedness -> Int.int -> Int.int

val cast_int_float : signedness -> Int.int -> float

val cast_float_int : signedness -> float -> Int.int option

val cast_int_single : signedness -> Int.int -> float32

val cast_single_int : signedness -> float32 -> Int.int option

val cast_int_long : signedness -> Int.int -> Int64.int

val cast_long_float : signedness -> Int64.int -> float

val cast_long_single : signedness -> Int64.int -> float32

val cast_float_long : signedness -> float -> Int64.int option

val cast_single_long : signedness -> float32 -> Int64.int option

val sem_cast : val0 -> type0 -> type0 -> Mem.mem -> val0 option

type classify_bool_cases =
| Bool_case_i
| Bool_case_l
| Bool_case_f
| Bool_case_s
| Bool_default

val classify_bool : type0 -> classify_bool_cases

val bool_val : val0 -> type0 -> Mem.mem -> bool option

type binarith_cases =
| Bin_case_i of signedness
| Bin_case_l of signedness
| Bin_case_f
| Bin_case_s
| Bin_default

val classify_binarith : type0 -> type0 -> binarith_cases

val binarith_type : binarith_cases -> type0

val sem_binarith :
  (signedness -> Int.int -> Int.int -> val0 option) -> (signedness ->
  Int64.int -> Int64.int -> val0 option) -> (float -> float -> val0 option)
  -> (float32 -> float32 -> val0 option) -> val0 -> type0 -> val0 -> type0 ->
  Mem.mem -> val0 option

type classify_add_cases =
| Add_case_pi of type0 * signedness
| Add_case_pl of type0
| Add_case_ip of signedness * type0
| Add_case_lp of type0
| Add_default

val classify_add : type0 -> type0 -> classify_add_cases

val ptrofs_of_int : signedness -> Int.int -> Ptrofs.int

val sem_add_ptr_int :
  composite_env -> type0 -> signedness -> val0 -> val0 -> val0 option

val sem_add_ptr_long : composite_env -> type0 -> val0 -> val0 -> val0 option

val sem_add :
  composite_env -> val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option

type classify_sub_cases =
| Sub_case_pi of type0 * signedness
| Sub_case_pp of type0
| Sub_case_pl of type0
| Sub_default

val classify_sub : type0 -> type0 -> classify_sub_cases

val sem_sub :
  composite_env -> val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option

val sem_mul : val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option

val sem_div : val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option

val sem_mod : val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option

val sem_and : val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option

val sem_or : val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option

val sem_xor : val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option

type classify_shift_cases =
| Shift_case_ii of signedness
| Shift_case_ll of signedness
| Shift_case_il of signedness
| Shift_case_li of signedness
| Shift_default

val classify_shift : type0 -> type0 -> classify_shift_cases

val sem_shift :
  (signedness -> Int.int -> Int.int -> Int.int) -> (signedness -> Int64.int
  -> Int64.int -> Int64.int) -> val0 -> type0 -> val0 -> type0 -> val0 option

val sem_shl : val0 -> type0 -> val0 -> type0 -> val0 option

val sem_shr : val0 -> type0 -> val0 -> type0 -> val0 option

type classify_cmp_cases =
| Cmp_case_pp
| Cmp_case_pi of signedness
| Cmp_case_ip of signedness
| Cmp_case_pl
| Cmp_case_lp
| Cmp_default

val classify_cmp : type0 -> type0 -> classify_cmp_cases

val cmp_ptr : Mem.mem -> comparison0 -> val0 -> val0 -> val0 option

val sem_cmp :
  comparison0 -> val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option

val sem_binary_operation :
  composite_env -> binary_operation -> val0 -> type0 -> val0 -> type0 ->
  Mem.mem -> val0 option

type expr =
| Econst_int of Int.int * type0
| Econst_float of float * type0
| Econst_single of float32 * type0
| Econst_long of Int64.int * type0
| Evar of ident * type0
| Etempvar of ident * type0
| Ederef of expr * type0
| Eaddrof of expr * type0
| Eunop of unary_operation * expr * type0
| Ebinop of binary_operation * expr * expr * type0
| Ecast of expr * type0
| Efield of expr * ident * type0
| Esizeof of type0 * type0
| Ealignof of type0 * type0

val typeof : expr -> type0

type label = ident

type statement =
| Sskip
| Sassign of expr * expr
| Sset of ident * expr
| Scall of ident option * expr * expr list
| Sbuiltin of ident option * external_function * type0 list * expr list
| Ssequence of statement * statement
| Sifthenelse of expr * statement * statement
| Sloop of statement * statement
| Sbreak
| Scontinue
| Sreturn of expr option
| Sswitch of expr * labeled_statements
| Slabel of label * statement
| Sgoto of label
and labeled_statements =
| LSnil
| LScons of z option * statement * labeled_statements

type function0 = { fn_return : type0; fn_callconv : calling_convention;
                   fn_params : (ident * type0) list;
                   fn_vars : (ident * type0) list;
                   fn_temps : (ident * type0) list; fn_body : statement }

type fundef0 = function0 fundef

type genv = { genv_genv : (fundef0, type0) Genv.t; genv_cenv : composite_env }

type temp_env = val0 PTree.t

val create_undef_temps : (ident * type0) list -> temp_env

type outcome =
| Out_break
| Out_continue
| Out_normal
| Out_return of (val0 * type0) option

val u32 : type0

val i32 : type0

val ptr : type0

val n0 : ident

val data : ident

val permutation : ident

val target : ident

val used : ident

val trace : ident

val out : ident

val i : ident

val j : ident

val top : ident

val pos : ident

val tmp : ident

val depth : ident

val lit : z -> expr

val reg : ident -> expr

val cell : ident -> expr -> expr

val add0 : expr -> expr -> expr

val sub0 : expr -> expr -> expr

val eq0 : expr -> expr -> expr

val ne : expr -> expr -> expr

val lt0 : expr -> expr -> expr

val gt : expr -> expr -> expr

val ge : expr -> expr -> expr

val seq : statement list -> statement

val set1 : ident -> expr -> statement

val put : ident -> expr -> expr -> statement

val ret : z -> statement

val when0 : expr -> statement -> statement

val loop : expr -> statement -> statement

val inc : ident -> statement

val each : ident -> statement -> statement

val check_input : statement

val normalize : statement

val choose_position : statement

val swap_cells : ident -> statement

val exchange : statement

val permute : function0

val expression : genv -> temp_env -> Mem.mem -> expr -> val0 option

val store0 : genv -> temp_env -> Mem.mem -> expr -> expr -> Mem.mem option

type result = (temp_env * Mem.mem) * outcome

val execute : nat -> genv -> temp_env -> Mem.mem -> statement -> result option

val call_temps :
  Int.int -> val0 -> val0 -> val0 -> val0 -> val0 -> val0 -> val0 PTree.tree

val empty_ge : genv

val write_words : Mem.mem -> block -> z -> z list -> Mem.mem option

val read_words : Mem.mem -> block -> z -> nat -> z list option

val observe :
  nat -> z -> Mem.mem -> val0 -> val0 -> val0 -> val0 -> val0 -> val0 ->
  block -> block -> block -> block -> nat -> z list option

val run : nat -> z -> z list -> z list -> z list option

val decimal : z -> char list
