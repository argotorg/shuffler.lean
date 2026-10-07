
(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _ :: l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

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

(** val revapp : uint -> uint -> uint **)

let rec revapp d d' =
  match d with
  | Nil -> d'
  | D0 d0 -> revapp d0 (D0 d')
  | D1 d0 -> revapp d0 (D1 d')
  | D2 d0 -> revapp d0 (D2 d')
  | D3 d0 -> revapp d0 (D3 d')
  | D4 d0 -> revapp d0 (D4 d')
  | D5 d0 -> revapp d0 (D5 d')
  | D6 d0 -> revapp d0 (D6 d')
  | D7 d0 -> revapp d0 (D7 d')
  | D8 d0 -> revapp d0 (D8 d')
  | D9 d0 -> revapp d0 (D9 d')

(** val rev : uint -> uint **)

let rev d =
  revapp d Nil

module Little =
 struct
  (** val double : uint -> uint **)

  let rec double = function
  | Nil -> Nil
  | D0 d0 -> D0 (double d0)
  | D1 d0 -> D2 (double d0)
  | D2 d0 -> D4 (double d0)
  | D3 d0 -> D6 (double d0)
  | D4 d0 -> D8 (double d0)
  | D5 d0 -> D0 (succ_double d0)
  | D6 d0 -> D2 (succ_double d0)
  | D7 d0 -> D4 (succ_double d0)
  | D8 d0 -> D6 (succ_double d0)
  | D9 d0 -> D8 (succ_double d0)

  (** val succ_double : uint -> uint **)

  and succ_double = function
  | Nil -> D1 Nil
  | D0 d0 -> D1 (double d0)
  | D1 d0 -> D3 (double d0)
  | D2 d0 -> D5 (double d0)
  | D3 d0 -> D7 (double d0)
  | D4 d0 -> D9 (double d0)
  | D5 d0 -> D1 (succ_double d0)
  | D6 d0 -> D3 (succ_double d0)
  | D7 d0 -> D5 (succ_double d0)
  | D8 d0 -> D7 (succ_double d0)
  | D9 d0 -> D9 (succ_double d0)
 end

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n1 m =
   match n1 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val bool_dec : bool -> bool -> bool **)

let bool_dec b1 b2 =
  if b1 then if b2 then true else false else if b2 then false else true

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n1 m =
    match n1 with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n' -> (match m with
               | O -> false
               | S m' -> eqb n' m')
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val repeat : 'a1 -> nat -> 'a1 list **)

let rec repeat x = function
| O -> []
| S k -> x :: (repeat x k)

(** val rev0 : 'a1 list -> 'a1 list **)

let rec rev0 = function
| [] -> []
| x :: l' -> app (rev0 l') (x :: [])

(** val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec0 l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _ :: _ -> false)
  | y :: l0 ->
    (match l' with
     | [] -> false
     | a :: l1 -> if eq_dec0 y a then list_eq_dec eq_dec0 l0 l1 else false)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: l0 -> f b (fold_right f a0 l0)

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

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH -> (match q with
             | XO q0 -> XI q0
             | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH -> (match q with
             | XO _ -> N0
             | _ -> Npos XH)

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH -> (match q with
             | XO _ -> Npos XH
             | _ -> N0)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH -> (match q with
             | XO q0 -> XI q0
             | _ -> q)

  (** val size : positive -> positive **)

  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH

  (** val shiftl_nat : positive -> nat -> positive **)

  let rec shiftl_nat p = function
  | O -> p
  | S n2 -> XO (shiftl_nat p n2)

  (** val shiftr_nat : positive -> nat -> positive **)

  let rec shiftr_nat p = function
  | O -> p
  | S n2 -> div2 (shiftr_nat p n2)

  (** val testbit : positive -> n -> bool **)

  let rec testbit p n1 =
    match p with
    | XI p0 -> (match n1 with
                | N0 -> true
                | Npos n2 -> testbit p0 (pred_N n2))
    | XO p0 -> (match n1 with
                | N0 -> false
                | Npos n2 -> testbit p0 (pred_N n2))
    | XH -> (match n1 with
             | N0 -> true
             | Npos _ -> false)

  (** val to_little_uint : positive -> uint **)

  let rec to_little_uint = function
  | XI p0 -> Little.succ_double (to_little_uint p0)
  | XO p0 -> Little.double (to_little_uint p0)
  | XH -> D1 Nil

  (** val to_uint : positive -> uint **)

  let to_uint p =
    rev (to_little_uint p)

  (** val eq_dec : positive -> positive -> bool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> false)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> false)
    | XH -> (match x0 with
             | XH -> true
             | _ -> false)
 end

module N =
 struct
  (** val succ_double : n -> n **)

  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val double : n -> n **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val succ_pos : n -> positive **)

  let succ_pos = function
  | N0 -> XH
  | Npos p -> Pos.succ p

  (** val sub : n -> n -> n **)

  let sub n1 m =
    match n1 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n1
       | Npos m' ->
         (match Pos.sub_mask n' m' with
          | Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val compare : n -> n -> comparison **)

  let compare n1 m =
    match n1 with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Pos.compare n' m')

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val pos_div_eucl : positive -> n -> n * n **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | XH ->
      (match b with
       | N0 -> (N0, (Npos XH))
       | Npos p -> (match p with
                    | XH -> ((Npos XH), N0)
                    | _ -> (N0, (Npos XH))))

  (** val coq_lor : n -> n -> n **)

  let coq_lor n1 m =
    match n1 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n1
                 | Npos q -> Npos (Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n1 m =
    match n1 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Pos.coq_land p q)

  (** val ldiff : n -> n -> n **)

  let ldiff n1 m =
    match n1 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> n1
                 | Npos q -> Pos.ldiff p q)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n1 m =
    match n1 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n1
                 | Npos q -> Pos.coq_lxor p q)
 end

module Coq_N =
 struct
  (** val testbit : n -> n -> bool **)

  let testbit a n1 =
    match a with
    | N0 -> false
    | Npos p -> Coq_Pos.testbit p n1

  (** val eq_dec : n -> n -> bool **)

  let eq_dec n1 m =
    match n1 with
    | N0 -> (match m with
             | N0 -> true
             | Npos _ -> false)
    | Npos p -> (match m with
                 | N0 -> false
                 | Npos p0 -> Coq_Pos.eq_dec p p0)
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n1 =
    add m (opp n1)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> false)

  (** val max : z -> z -> z **)

  let max n1 m =
    match compare n1 m with
    | Lt -> m
    | _ -> n1

  (** val min : z -> z -> z **)

  let min n1 m =
    match compare n1 m with
    | Gt -> m
    | _ -> n1

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XH -> if leb (Zpos (XO XH)) b then (Z0, (Zpos XH)) else ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> z * z **)

  let div_eucl a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ ->
         let (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q, r) = pos_div_eucl a' (Zpos b') in (q, (opp r)))

  (** val even : z -> bool **)

  let even = function
  | Z0 -> true
  | Zpos p -> (match p with
               | XO _ -> true
               | _ -> false)
  | Zneg p -> (match p with
               | XO _ -> true
               | _ -> false)

  (** val div2 : z -> z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | XH -> Z0
               | _ -> Zpos (Pos.div2 p))
  | Zneg p -> Zneg (Pos.div2_up p)

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Pos.iter (mul (Zpos (XO XH))) a p
  | Zneg p -> Pos.iter div2 a p
 end

module Coq_Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n1 =
    add m (opp n1)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val pow_pos : z -> positive -> z **)

  let pow_pos z0 =
    Pos.iter (mul z0) (Zpos XH)

  (** val pow : z -> z -> z **)

  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg _ -> Z0

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> false)

  (** val max : z -> z -> z **)

  let max n1 m =
    match compare n1 m with
    | Lt -> m
    | _ -> n1

  (** val min : z -> z -> z **)

  let min n1 m =
    match compare n1 m with
    | Gt -> m
    | _ -> n1

  (** val to_nat : z -> nat **)

  let to_nat = function
  | Zpos p -> Pos.to_nat p
  | _ -> O

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n2 -> Zpos (Pos.of_succ_nat n2)

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XH -> if leb (Zpos (XO XH)) b then (Z0, (Zpos XH)) else ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> z * z **)

  let div_eucl a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ ->
         let (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q, r) = pos_div_eucl a' (Zpos b') in (q, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let (q, _) = div_eucl a b in q

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let (_, r) = div_eucl a b in r

  (** val quotrem : z -> z -> z * z **)

  let quotrem a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a0 ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in ((of_N q), (of_N r))
       | Zneg b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((opp (of_N q)), (of_N r)))
    | Zneg a0 ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((opp (of_N q)), (opp (of_N r)))
       | Zneg b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((of_N q), (opp (of_N r))))

  (** val quot : z -> z -> z **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : z -> z -> z **)

  let rem a b =
    snd (quotrem a b)

  (** val even : z -> bool **)

  let even = function
  | Z0 -> true
  | Zpos p -> (match p with
               | XO _ -> true
               | _ -> false)
  | Zneg p -> (match p with
               | XO _ -> true
               | _ -> false)

  (** val div2 : z -> z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | XH -> Z0
               | _ -> Zpos (Pos.div2 p))
  | Zneg p -> Zneg (Pos.div2_up p)

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Pos.iter (mul (Zpos (XO XH))) a p
  | Zneg p -> Pos.iter div2 a p

  (** val shiftr : z -> z -> z **)

  let shiftr a n1 =
    shiftl a (opp n1)

  (** val coq_lor : z -> z -> z **)

  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Pos.pred_N a0) (Npos b0)))
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_land (Pos.pred_N a0) (Pos.pred_N b0))))

  (** val coq_land : z -> z -> z **)

  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Pos.pred_N a0))
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lor (Pos.pred_N a0) (Pos.pred_N b0))))

  (** val coq_lxor : z -> z -> z **)

  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Pos.coq_lxor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.coq_lxor (Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Pos.pred_N a0) (Pos.pred_N b0)))

  (** val pred : z -> z **)

  let pred x =
    add x (Zneg XH)

  (** val to_int : z -> signed_int **)

  let to_int = function
  | Z0 -> Pos (D0 Nil)
  | Zpos p -> Pos (Coq_Pos.to_uint p)
  | Zneg p -> Neg (Coq_Pos.to_uint p)

  (** val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n1 f x =
    match n1 with
    | Zpos p -> Coq_Pos.iter f x p
    | _ -> x

  (** val odd : z -> bool **)

  let odd = function
  | Z0 -> false
  | Zpos p -> (match p with
               | XO _ -> false
               | _ -> true)
  | Zneg p -> (match p with
               | XO _ -> false
               | _ -> true)

  (** val log2 : z -> z **)

  let log2 = function
  | Zpos p0 ->
    (match p0 with
     | XI p -> Zpos (Coq_Pos.size p)
     | XO p -> Zpos (Coq_Pos.size p)
     | XH -> Z0)
  | _ -> Z0

  (** val testbit : z -> z -> bool **)

  let testbit a = function
  | Z0 -> odd a
  | Zpos p ->
    (match a with
     | Z0 -> false
     | Zpos a0 -> Coq_Pos.testbit a0 (Npos p)
     | Zneg a0 -> negb (Coq_N.testbit (Coq_Pos.pred_N a0) (Npos p)))
  | Zneg _ -> false

  (** val eq_dec : z -> z -> bool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos p0 -> Coq_Pos.eq_dec p p0
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg p0 -> Coq_Pos.eq_dec p p0
                 | _ -> false)
 end

(** val z_lt_dec : z -> z -> bool **)

let z_lt_dec x y =
  match Coq_Z.compare x y with
  | Lt -> true
  | _ -> false

(** val z_le_dec : z -> z -> bool **)

let z_le_dec x y =
  match Coq_Z.compare x y with
  | Gt -> false
  | _ -> true

(** val z_le_gt_dec : z -> z -> bool **)

let z_le_gt_dec =
  z_le_dec

(** val zdivide_dec : z -> z -> bool **)

let zdivide_dec a b =
  let s = Coq_Z.eq_dec a Z0 in
  if s then Coq_Z.eq_dec b Z0 else Coq_Z.eq_dec (Coq_Z.modulo b a) Z0

(** val shift_nat : nat -> positive -> positive **)

let rec shift_nat n1 z0 =
  match n1 with
  | O -> z0
  | S n2 -> XO (shift_nat n2 z0)

(** val shift_pos : positive -> positive -> positive **)

let shift_pos n1 z0 =
  Coq_Pos.iter (fun x -> XO x) z0 n1

(** val two_power_nat : nat -> z **)

let two_power_nat n1 =
  Zpos (shift_nat n1 XH)

(** val two_power_pos : positive -> z **)

let two_power_pos x =
  Zpos (shift_pos x XH)

(** val two_p : z -> z **)

let two_p = function
| Z0 -> Zpos XH
| Zpos y -> two_power_pos y
| Zneg _ -> Z0

module NilEmpty =
 struct
  (** val string_of_uint : uint -> char list **)

  let rec string_of_uint = function
  | Nil -> []
  | D0 d0 -> '0'::(string_of_uint d0)
  | D1 d0 -> '1'::(string_of_uint d0)
  | D2 d0 -> '2'::(string_of_uint d0)
  | D3 d0 -> '3'::(string_of_uint d0)
  | D4 d0 -> '4'::(string_of_uint d0)
  | D5 d0 -> '5'::(string_of_uint d0)
  | D6 d0 -> '6'::(string_of_uint d0)
  | D7 d0 -> '7'::(string_of_uint d0)
  | D8 d0 -> '8'::(string_of_uint d0)
  | D9 d0 -> '9'::(string_of_uint d0)
 end

module NilZero =
 struct
  (** val string_of_uint : uint -> char list **)

  let string_of_uint d = match d with
  | Nil -> '0'::[]
  | _ -> NilEmpty.string_of_uint d

  (** val string_of_int : signed_int -> char list **)

  let string_of_int = function
  | Pos d0 -> string_of_uint d0
  | Neg d0 -> '-'::(string_of_uint d0)
 end

(** val peq : positive -> positive -> bool **)

let peq =
  Coq_Pos.eq_dec

(** val zeq : z -> z -> bool **)

let zeq =
  Coq_Z.eq_dec

(** val zlt : z -> z -> bool **)

let zlt =
  z_lt_dec

(** val zle : z -> z -> bool **)

let zle =
  z_le_gt_dec

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some y -> Some (f y)
| None -> None

(** val proj_sumbool : bool -> bool **)

let proj_sumbool = function
| true -> true
| false -> false

module PTree =
 struct
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

  (** val empty : 'a1 t **)

  let empty =
    Empty

  (** val get' : positive -> 'a1 tree' -> 'a1 option **)

  let rec get' p m =
    match p with
    | XI q ->
      (match m with
       | Node001 m' -> get' q m'
       | Node011 (_, m') -> get' q m'
       | Node101 (_, m') -> get' q m'
       | Node111 (_, _, m') -> get' q m'
       | _ -> None)
    | XO q ->
      (match m with
       | Node100 m' -> get' q m'
       | Node101 (m', _) -> get' q m'
       | Node110 (m', _) -> get' q m'
       | Node111 (m', _, _) -> get' q m'
       | _ -> None)
    | XH ->
      (match m with
       | Node010 x -> Some x
       | Node011 (x, _) -> Some x
       | Node110 (_, x) -> Some x
       | Node111 (_, x, _) -> Some x
       | _ -> None)

  (** val get : positive -> 'a1 tree -> 'a1 option **)

  let get p = function
  | Empty -> None
  | Nodes m' -> get' p m'

  (** val set0 : positive -> 'a1 -> 'a1 tree' **)

  let rec set0 p x =
    match p with
    | XI q -> Node001 (set0 q x)
    | XO q -> Node100 (set0 q x)
    | XH -> Node010 x

  (** val set' : positive -> 'a1 -> 'a1 tree' -> 'a1 tree' **)

  let rec set' p x m =
    match p with
    | XI q ->
      (match m with
       | Node001 r -> Node001 (set' q x r)
       | Node010 y -> Node011 (y, (set0 q x))
       | Node011 (y, r) -> Node011 (y, (set' q x r))
       | Node100 l -> Node101 (l, (set0 q x))
       | Node101 (l, r) -> Node101 (l, (set' q x r))
       | Node110 (l, y) -> Node111 (l, y, (set0 q x))
       | Node111 (l, y, r) -> Node111 (l, y, (set' q x r)))
    | XO q ->
      (match m with
       | Node001 r -> Node101 ((set0 q x), r)
       | Node010 y -> Node110 ((set0 q x), y)
       | Node011 (y, r) -> Node111 ((set0 q x), y, r)
       | Node100 l -> Node100 (set' q x l)
       | Node101 (l, r) -> Node101 ((set' q x l), r)
       | Node110 (l, y) -> Node110 ((set' q x l), y)
       | Node111 (l, y, r) -> Node111 ((set' q x l), y, r))
    | XH ->
      (match m with
       | Node001 r -> Node011 (x, r)
       | Node010 _ -> Node010 x
       | Node011 (_, r) -> Node011 (x, r)
       | Node100 l -> Node110 (l, x)
       | Node101 (l, r) -> Node111 (l, x, r)
       | Node110 (l, _) -> Node110 (l, x)
       | Node111 (l, _, r) -> Node111 (l, x, r))

  (** val set : positive -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let set p x = function
  | Empty -> Nodes (set0 p x)
  | Nodes m' -> Nodes (set' p x m')

  (** val map1' : ('a1 -> 'a2) -> 'a1 tree' -> 'a2 tree' **)

  let rec map1' f = function
  | Node001 r -> Node001 (map1' f r)
  | Node010 x -> Node010 (f x)
  | Node011 (x, r) -> Node011 ((f x), (map1' f r))
  | Node100 l -> Node100 (map1' f l)
  | Node101 (l, r) -> Node101 ((map1' f l), (map1' f r))
  | Node110 (l, x) -> Node110 ((map1' f l), (f x))
  | Node111 (l, x, r) -> Node111 ((map1' f l), (f x), (map1' f r))

  (** val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map1 f = function
  | Empty -> Empty
  | Nodes m0 -> Nodes (map1' f m0)
 end

module PMap =
 struct
  type 'a t = 'a * 'a PTree.t

  (** val init : 'a1 -> 'a1 * 'a1 PTree.t **)

  let init x =
    (x, PTree.empty)

  (** val get : positive -> 'a1 t -> 'a1 **)

  let get i0 m =
    match PTree.get i0 (snd m) with
    | Some x -> x
    | None -> fst m

  (** val set : positive -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.tree **)

  let set i0 x m =
    ((fst m), (PTree.set i0 x (snd m)))

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    ((f (fst m)), (PTree.map1 f (snd m)))
 end

module type INDEXED_TYPE =
 sig
  type t

  val index : t -> positive

  val eq : t -> t -> bool
 end

module IMap =
 functor (X:INDEXED_TYPE) ->
 struct
  type elt = X.t

  (** val elt_eq : X.t -> X.t -> bool **)

  let elt_eq =
    X.eq

  type 'x t = 'x PMap.t

  (** val init : 'a1 -> 'a1 * 'a1 PTree.t **)

  let init =
    PMap.init

  (** val get : X.t -> 'a1 t -> 'a1 **)

  let get i0 m =
    PMap.get (X.index i0) m

  (** val set : X.t -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.tree **)

  let set i0 v m =
    PMap.set (X.index i0) v m

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map =
    PMap.map
 end

module ZIndexed =
 struct
  type t = z

  (** val index : z -> positive **)

  let index = function
  | Z0 -> XH
  | Zpos p -> XO p
  | Zneg p -> XI p

  (** val eq : z -> z -> bool **)

  let eq =
    zeq
 end

module ZMap = IMap(ZIndexed)

(** val p_mod_two_p : positive -> nat -> z **)

let rec p_mod_two_p p = function
| O -> Z0
| S m ->
  (match p with
   | XI q -> Coq_Z.succ_double (p_mod_two_p q m)
   | XO q -> Coq_Z.double (p_mod_two_p q m)
   | XH -> Zpos XH)

(** val zshiftin : bool -> z -> z **)

let zshiftin b x =
  if b then Coq_Z.succ_double x else Coq_Z.double x

(** val zzero_ext : z -> z -> z **)

let zzero_ext n1 x =
  Coq_Z.iter n1 (fun rec0 x0 ->
    zshiftin (Coq_Z.odd x0) (rec0 (Coq_Z.div2 x0))) (fun _ -> Z0) x

(** val zsign_ext : z -> z -> z **)

let zsign_ext n1 x =
  Coq_Z.iter (Coq_Z.pred n1) (fun rec0 x0 ->
    zshiftin (Coq_Z.odd x0) (rec0 (Coq_Z.div2 x0))) (fun x0 ->
    if (&&) (Coq_Z.odd x0) (proj_sumbool (zlt Z0 n1)) then Zneg XH else Z0) x

(** val z_one_bits : nat -> z -> z -> z list **)

let rec z_one_bits n1 x i0 =
  match n1 with
  | O -> []
  | S m ->
    if Coq_Z.odd x
    then i0 :: (z_one_bits m (Coq_Z.div2 x) (Coq_Z.add i0 (Zpos XH)))
    else z_one_bits m (Coq_Z.div2 x) (Coq_Z.add i0 (Zpos XH))

(** val p_is_power2 : positive -> bool **)

let rec p_is_power2 = function
| XI _ -> false
| XO q -> p_is_power2 q
| XH -> true

(** val z_is_power2 : z -> z option **)

let z_is_power2 x = match x with
| Zpos p -> if p_is_power2 p then Some (Coq_Z.log2 x) else None
| _ -> None

(** val zsize : z -> z **)

let zsize = function
| Zpos p -> Zpos (Coq_Pos.size p)
| _ -> Z0

type spec_float =
| S754_zero of bool
| S754_infinity of bool
| S754_nan
| S754_finite of bool * positive * z

(** val emin : z -> z -> z **)

let emin prec emax =
  Z.sub (Z.sub (Zpos (XI XH)) emax) prec

(** val fexp : z -> z -> z -> z **)

let fexp prec emax e =
  Z.max (Z.sub e prec) (emin prec emax)

(** val digits2_pos : positive -> positive **)

let rec digits2_pos = function
| XI p -> Pos.succ (digits2_pos p)
| XO p -> Pos.succ (digits2_pos p)
| XH -> XH

(** val zdigits2 : z -> z **)

let zdigits2 n1 = match n1 with
| Z0 -> n1
| Zpos p -> Zpos (digits2_pos p)
| Zneg p -> Zpos (digits2_pos p)

(** val iter_pos : ('a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

let rec iter_pos f n1 x =
  match n1 with
  | XI n' -> iter_pos f n' (iter_pos f n' (f x))
  | XO n' -> iter_pos f n' (iter_pos f n' x)
  | XH -> f x

type location =
| Loc_Exact
| Loc_Inexact of comparison

type shr_record = { shr_m : z; shr_r : bool; shr_s : bool }

(** val shr_1 : shr_record -> shr_record **)

let shr_1 mrs =
  let { shr_m = m; shr_r = r; shr_s = s } = mrs in
  let s0 = (||) r s in
  (match m with
   | Z0 -> { shr_m = Z0; shr_r = false; shr_s = s0 }
   | Zpos p0 ->
     (match p0 with
      | XI p -> { shr_m = (Zpos p); shr_r = true; shr_s = s0 }
      | XO p -> { shr_m = (Zpos p); shr_r = false; shr_s = s0 }
      | XH -> { shr_m = Z0; shr_r = true; shr_s = s0 })
   | Zneg p0 ->
     (match p0 with
      | XI p -> { shr_m = (Zneg p); shr_r = true; shr_s = s0 }
      | XO p -> { shr_m = (Zneg p); shr_r = false; shr_s = s0 }
      | XH -> { shr_m = Z0; shr_r = true; shr_s = s0 }))

(** val loc_of_shr_record : shr_record -> location **)

let loc_of_shr_record mrs =
  let { shr_m = _; shr_r = shr_r0; shr_s = shr_s0 } = mrs in
  if shr_r0
  then if shr_s0 then Loc_Inexact Gt else Loc_Inexact Eq
  else if shr_s0 then Loc_Inexact Lt else Loc_Exact

(** val shr_record_of_loc : z -> location -> shr_record **)

let shr_record_of_loc m = function
| Loc_Exact -> { shr_m = m; shr_r = false; shr_s = false }
| Loc_Inexact c ->
  (match c with
   | Eq -> { shr_m = m; shr_r = true; shr_s = false }
   | Lt -> { shr_m = m; shr_r = false; shr_s = true }
   | Gt -> { shr_m = m; shr_r = true; shr_s = true })

(** val shr : shr_record -> z -> z -> shr_record * z **)

let shr mrs e n1 = match n1 with
| Zpos p -> ((iter_pos shr_1 p mrs), (Z.add e n1))
| _ -> (mrs, e)

(** val shr_fexp : z -> z -> z -> z -> location -> shr_record * z **)

let shr_fexp prec emax m e l =
  shr (shr_record_of_loc m l) e
    (Z.sub (fexp prec emax (Z.add (zdigits2 m) e)) e)

(** val shl_align : positive -> z -> z -> positive * z **)

let shl_align mx ex ex' =
  match Z.sub ex' ex with
  | Zneg d -> ((Pos.iter (fun x -> XO x) mx d), ex')
  | _ -> (mx, ex)

(** val sFcompare : spec_float -> spec_float -> comparison option **)

let sFcompare f1 f2 =
  match f1 with
  | S754_zero _ ->
    (match f2 with
     | S754_zero _ -> Some Eq
     | S754_infinity s -> Some (if s then Gt else Lt)
     | S754_nan -> None
     | S754_finite (s, _, _) -> Some (if s then Gt else Lt))
  | S754_infinity s ->
    (match f2 with
     | S754_infinity s0 ->
       Some (if s then if s0 then Eq else Lt else if s0 then Gt else Eq)
     | S754_nan -> None
     | _ -> Some (if s then Lt else Gt))
  | S754_nan -> None
  | S754_finite (s1, m1, e1) ->
    (match f2 with
     | S754_zero _ -> Some (if s1 then Lt else Gt)
     | S754_infinity s -> Some (if s then Gt else Lt)
     | S754_nan -> None
     | S754_finite (s2, m2, e2) ->
       Some
         (if s1
          then if s2
               then (match Z.compare e1 e2 with
                     | Eq -> compOpp (Pos.compare_cont Eq m1 m2)
                     | Lt -> Gt
                     | Gt -> Lt)
               else Lt
          else if s2
               then Gt
               else (match Z.compare e1 e2 with
                     | Eq -> Pos.compare_cont Eq m1 m2
                     | x -> x)))

(** val cond_Zopp : bool -> z -> z **)

let cond_Zopp b m =
  if b then Z.opp m else m

(** val new_location_even : z -> z -> location **)

let new_location_even nb_steps k =
  if Z.eqb k Z0
  then Loc_Exact
  else Loc_Inexact (Z.compare (Z.mul (Zpos (XO XH)) k) nb_steps)

(** val new_location_odd : z -> z -> location **)

let new_location_odd nb_steps k =
  if Z.eqb k Z0
  then Loc_Exact
  else Loc_Inexact
         (match Z.compare (Z.add (Z.mul (Zpos (XO XH)) k) (Zpos XH)) nb_steps with
          | Eq -> Lt
          | x -> x)

(** val new_location : z -> z -> location **)

let new_location nb_steps =
  if Z.even nb_steps
  then new_location_even nb_steps
  else new_location_odd nb_steps

(** val sFdiv_core_binary :
    z -> z -> z -> z -> z -> z -> (z * z) * location **)

let sFdiv_core_binary prec emax m1 e1 m2 e2 =
  let d1 = zdigits2 m1 in
  let d2 = zdigits2 m2 in
  let e' =
    Z.min (fexp prec emax (Z.sub (Z.add d1 e1) (Z.add d2 e2))) (Z.sub e1 e2)
  in
  let s = Z.sub (Z.sub e1 e2) e' in
  let m' = match s with
           | Z0 -> m1
           | Zpos _ -> Z.shiftl m1 s
           | Zneg _ -> Z0 in
  let (q, r) = Z.div_eucl m' m2 in ((q, e'), (new_location m2 r))

type radix = z
  (* singleton inductive, whose constructor was Build_radix *)

(** val radix2 : radix **)

let radix2 =
  Zpos (XO XH)

(** val iter_nat : ('a1 -> 'a1) -> nat -> 'a1 -> 'a1 **)

let rec iter_nat f n1 x =
  match n1 with
  | O -> x
  | S n' -> iter_nat f n' (f x)

(** val cond_incr : bool -> z -> z **)

let cond_incr b m =
  if b then Coq_Z.add m (Zpos XH) else m

(** val round_sign_DN : bool -> location -> bool **)

let round_sign_DN s = function
| Loc_Exact -> false
| Loc_Inexact _ -> s

(** val round_sign_UP : bool -> location -> bool **)

let round_sign_UP s = function
| Loc_Exact -> false
| Loc_Inexact _ -> negb s

(** val round_N : bool -> location -> bool **)

let round_N p = function
| Loc_Exact -> false
| Loc_Inexact c -> (match c with
                    | Eq -> p
                    | Lt -> false
                    | Gt -> true)

type binary_float =
| B754_zero of bool
| B754_infinity of bool
| B754_nan
| B754_finite of bool * positive * z

(** val sF2B : z -> z -> spec_float -> binary_float **)

let sF2B _ _ = function
| S754_zero s -> B754_zero s
| S754_infinity s -> B754_infinity s
| S754_nan -> B754_nan
| S754_finite (s, m, e) -> B754_finite (s, m, e)

(** val b2SF : z -> z -> binary_float -> spec_float **)

let b2SF _ _ = function
| B754_zero s -> S754_zero s
| B754_infinity s -> S754_infinity s
| B754_nan -> S754_nan
| B754_finite (s, m, e) -> S754_finite (s, m, e)

(** val bcompare :
    z -> z -> binary_float -> binary_float -> comparison option **)

let bcompare prec emax f1 f2 =
  sFcompare (b2SF prec emax f1) (b2SF prec emax f2)

type mode =
| Mode_NE
| Mode_ZR
| Mode_DN
| Mode_UP
| Mode_NA

(** val choice_mode : mode -> bool -> z -> location -> z **)

let choice_mode m sx mx lx =
  match m with
  | Mode_NE -> cond_incr (round_N (negb (Coq_Z.even mx)) lx) mx
  | Mode_ZR -> mx
  | Mode_DN -> cond_incr (round_sign_DN sx lx) mx
  | Mode_UP -> cond_incr (round_sign_UP sx lx) mx
  | Mode_NA -> cond_incr (round_N true lx) mx

(** val overflow_to_inf : mode -> bool -> bool **)

let overflow_to_inf m s =
  match m with
  | Mode_ZR -> false
  | Mode_DN -> s
  | Mode_UP -> negb s
  | _ -> true

(** val binary_overflow : z -> z -> mode -> bool -> spec_float **)

let binary_overflow prec emax m s =
  if overflow_to_inf m s
  then S754_infinity s
  else S754_finite (s,
         (Coq_Z.to_pos (Coq_Z.sub (Coq_Z.pow (Zpos (XO XH)) prec) (Zpos XH))),
         (Coq_Z.sub emax prec))

(** val binary_fit_aux :
    z -> z -> mode -> bool -> positive -> z -> spec_float **)

let binary_fit_aux prec emax mode1 sx mx ex =
  if Coq_Z.leb ex (Coq_Z.sub emax prec)
  then S754_finite (sx, mx, ex)
  else binary_overflow prec emax mode1 sx

(** val binary_round_aux :
    z -> z -> mode -> bool -> z -> z -> location -> spec_float **)

let binary_round_aux prec emax mode1 sx mx ex lx =
  let (mrs', e') = shr_fexp prec emax mx ex lx in
  let (mrs'', e'') =
    shr_fexp prec emax
      (choice_mode mode1 sx mrs'.shr_m (loc_of_shr_record mrs')) e' Loc_Exact
  in
  (match mrs''.shr_m with
   | Z0 -> S754_zero sx
   | Zpos m -> binary_fit_aux prec emax mode1 sx m e''
   | Zneg _ -> S754_nan)

(** val bmult :
    z -> z -> mode -> binary_float -> binary_float -> binary_float **)

let bmult prec emax m x y =
  match x with
  | B754_zero sx ->
    (match y with
     | B754_zero sy -> B754_zero (xorb sx sy)
     | B754_finite (sy, _, _) -> B754_zero (xorb sx sy)
     | _ -> B754_nan)
  | B754_infinity sx ->
    (match y with
     | B754_infinity sy -> B754_infinity (xorb sx sy)
     | B754_finite (sy, _, _) -> B754_infinity (xorb sx sy)
     | _ -> B754_nan)
  | B754_nan -> B754_nan
  | B754_finite (sx, mx, ex) ->
    (match y with
     | B754_zero sy -> B754_zero (xorb sx sy)
     | B754_infinity sy -> B754_infinity (xorb sx sy)
     | B754_nan -> B754_nan
     | B754_finite (sy, my, ey) ->
       sF2B prec emax
         (binary_round_aux prec emax m (xorb sx sy) (Zpos
           (Coq_Pos.mul mx my)) (Coq_Z.add ex ey) Loc_Exact))

(** val shl_align_fexp : z -> z -> positive -> z -> positive * z **)

let shl_align_fexp prec emax mx ex =
  shl_align mx ex (fexp prec emax (Coq_Z.add (Zpos (digits2_pos mx)) ex))

(** val binary_round :
    z -> z -> mode -> bool -> positive -> z -> spec_float **)

let binary_round prec emax m sx mx ex =
  let (mz, ez) = shl_align_fexp prec emax mx ex in
  binary_round_aux prec emax m sx (Zpos mz) ez Loc_Exact

(** val binary_normalize :
    z -> z -> mode -> z -> z -> bool -> binary_float **)

let binary_normalize prec emax mode1 m e szero =
  match m with
  | Z0 -> B754_zero szero
  | Zpos m0 -> sF2B prec emax (binary_round prec emax mode1 false m0 e)
  | Zneg m0 -> sF2B prec emax (binary_round prec emax mode1 true m0 e)

(** val fplus_naive :
    bool -> positive -> z -> bool -> positive -> z -> z -> z **)

let fplus_naive sx mx ex sy my ey ez =
  Coq_Z.add (cond_Zopp sx (Zpos (fst (shl_align mx ex ez))))
    (cond_Zopp sy (Zpos (fst (shl_align my ey ez))))

(** val bplus :
    z -> z -> mode -> binary_float -> binary_float -> binary_float **)

let bplus prec emax m x y =
  match x with
  | B754_zero sx ->
    (match y with
     | B754_zero sy ->
       if eqb sx sy
       then x
       else (match m with
             | Mode_DN -> B754_zero true
             | _ -> B754_zero false)
     | B754_nan -> B754_nan
     | _ -> y)
  | B754_infinity sx ->
    (match y with
     | B754_infinity sy -> if eqb sx sy then x else B754_nan
     | B754_nan -> B754_nan
     | _ -> x)
  | B754_nan -> B754_nan
  | B754_finite (sx, mx, ex) ->
    (match y with
     | B754_zero _ -> x
     | B754_infinity _ -> y
     | B754_nan -> B754_nan
     | B754_finite (sy, my, ey) ->
       let ez = Coq_Z.min ex ey in
       binary_normalize prec emax m (fplus_naive sx mx ex sy my ey ez) ez
         (match m with
          | Mode_DN -> true
          | _ -> false))

(** val bminus :
    z -> z -> mode -> binary_float -> binary_float -> binary_float **)

let bminus prec emax m x y =
  match x with
  | B754_zero sx ->
    (match y with
     | B754_zero sy ->
       if eqb sx (negb sy)
       then x
       else (match m with
             | Mode_DN -> B754_zero true
             | _ -> B754_zero false)
     | B754_infinity sy -> B754_infinity (negb sy)
     | B754_nan -> B754_nan
     | B754_finite (sy, my, ey) -> B754_finite ((negb sy), my, ey))
  | B754_infinity sx ->
    (match y with
     | B754_infinity sy -> if eqb sx (negb sy) then x else B754_nan
     | B754_nan -> B754_nan
     | _ -> x)
  | B754_nan -> B754_nan
  | B754_finite (sx, mx, ex) ->
    (match y with
     | B754_zero _ -> x
     | B754_infinity sy -> B754_infinity (negb sy)
     | B754_nan -> B754_nan
     | B754_finite (sy, my, ey) ->
       let ez = Coq_Z.min ex ey in
       binary_normalize prec emax m (fplus_naive sx mx ex (negb sy) my ey ez)
         ez (match m with
             | Mode_DN -> true
             | _ -> false))

(** val bdiv :
    z -> z -> mode -> binary_float -> binary_float -> binary_float **)

let bdiv prec emax m x y =
  match x with
  | B754_zero sx ->
    (match y with
     | B754_infinity sy -> B754_zero (xorb sx sy)
     | B754_finite (sy, _, _) -> B754_zero (xorb sx sy)
     | _ -> B754_nan)
  | B754_infinity sx ->
    (match y with
     | B754_zero sy -> B754_infinity (xorb sx sy)
     | B754_finite (sy, _, _) -> B754_infinity (xorb sx sy)
     | _ -> B754_nan)
  | B754_nan -> B754_nan
  | B754_finite (sx, mx, ex) ->
    (match y with
     | B754_zero sy -> B754_infinity (xorb sx sy)
     | B754_infinity sy -> B754_zero (xorb sx sy)
     | B754_nan -> B754_nan
     | B754_finite (sy, my, ey) ->
       sF2B prec emax
         (let (p, lz) = sFdiv_core_binary prec emax (Zpos mx) ex (Zpos my) ey
          in
          let (mz, ez) = p in
          binary_round_aux prec emax m (xorb sx sy) mz ez lz))

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

(** val b2BSN : z -> z -> binary_float0 -> binary_float **)

let b2BSN _ _ = function
| B754_zero0 s -> B754_zero s
| B754_infinity0 s -> B754_infinity s
| B754_nan0 (_, _) -> B754_nan
| B754_finite0 (s, m, e) -> B754_finite (s, m, e)

(** val fF2B : z -> z -> full_float -> binary_float0 **)

let fF2B _ _ = function
| F754_zero s -> B754_zero0 s
| F754_infinity s -> B754_infinity0 s
| F754_nan (b, pl) -> B754_nan0 (b, pl)
| F754_finite (s, m, e) -> B754_finite0 (s, m, e)

(** val bsign : z -> z -> binary_float0 -> bool **)

let bsign _ _ = function
| B754_zero0 s -> s
| B754_infinity0 s -> s
| B754_nan0 (s, _) -> s
| B754_finite0 (s, _, _) -> s

(** val get_nan_pl : z -> z -> binary_float0 -> positive **)

let get_nan_pl _ _ = function
| B754_nan0 (_, pl) -> pl
| _ -> XH

(** val build_nan : z -> z -> binary_float0 -> binary_float0 **)

let build_nan prec emax x =
  B754_nan0 ((bsign prec emax x), (get_nan_pl prec emax x))

(** val bSN2B : z -> z -> binary_float0 -> binary_float -> binary_float0 **)

let bSN2B prec emax nan = function
| B754_zero s -> B754_zero0 s
| B754_infinity s -> B754_infinity0 s
| B754_nan -> build_nan prec emax nan
| B754_finite (s, m, e) -> B754_finite0 (s, m, e)

(** val bSN2B' : z -> z -> binary_float -> binary_float0 **)

let bSN2B' _ _ = function
| B754_zero s -> B754_zero0 s
| B754_infinity s -> B754_infinity0 s
| B754_nan -> assert false (* absurd case *)
| B754_finite (s, m, e) -> B754_finite0 (s, m, e)

(** val bcompare0 :
    z -> z -> binary_float0 -> binary_float0 -> comparison option **)

let bcompare0 prec emax f1 f2 =
  bcompare prec emax (b2BSN prec emax f1) (b2BSN prec emax f2)

(** val bmult0 :
    z -> z -> (binary_float0 -> binary_float0 -> binary_float0) -> mode ->
    binary_float0 -> binary_float0 -> binary_float0 **)

let bmult0 prec emax mult_nan m x y =
  bSN2B prec emax (mult_nan x y)
    (bmult prec emax m (b2BSN prec emax x) (b2BSN prec emax y))

(** val binary_normalize0 :
    z -> z -> mode -> z -> z -> bool -> binary_float0 **)

let binary_normalize0 prec emax mode1 m e szero =
  bSN2B' prec emax (binary_normalize prec emax mode1 m e szero)

(** val bplus0 :
    z -> z -> (binary_float0 -> binary_float0 -> binary_float0) -> mode ->
    binary_float0 -> binary_float0 -> binary_float0 **)

let bplus0 prec emax plus_nan m x y =
  bSN2B prec emax (plus_nan x y)
    (bplus prec emax m (b2BSN prec emax x) (b2BSN prec emax y))

(** val bminus0 :
    z -> z -> (binary_float0 -> binary_float0 -> binary_float0) -> mode ->
    binary_float0 -> binary_float0 -> binary_float0 **)

let bminus0 prec emax minus_nan m x y =
  bSN2B prec emax (minus_nan x y)
    (bminus prec emax m (b2BSN prec emax x) (b2BSN prec emax y))

(** val bdiv0 :
    z -> z -> (binary_float0 -> binary_float0 -> binary_float0) -> mode ->
    binary_float0 -> binary_float0 -> binary_float0 **)

let bdiv0 prec emax div_nan m x y =
  bSN2B prec emax (div_nan x y)
    (bdiv prec emax m (b2BSN prec emax x) (b2BSN prec emax y))

(** val join_bits : z -> z -> bool -> z -> z -> z **)

let join_bits mw ew s m e =
  Coq_Z.add
    (Coq_Z.shiftl
      (Coq_Z.add (if s then Coq_Z.pow (Zpos (XO XH)) ew else Z0) e) mw)
    m

(** val split_bits : z -> z -> z -> (bool * z) * z **)

let split_bits mw ew x =
  let mm = Coq_Z.pow (Zpos (XO XH)) mw in
  let em = Coq_Z.pow (Zpos (XO XH)) ew in
  (((Coq_Z.leb (Coq_Z.mul mm em) x), (Coq_Z.modulo x mm)),
  (Coq_Z.modulo (Coq_Z.div x mm) em))

(** val bits_of_binary_float : z -> z -> binary_float0 -> z **)

let bits_of_binary_float mw ew =
  let prec = Coq_Z.add mw (Zpos XH) in
  let emax = Coq_Z.pow (Zpos (XO XH)) (Coq_Z.sub ew (Zpos XH)) in
  (fun x ->
  match x with
  | B754_zero0 sx -> join_bits mw ew sx Z0 Z0
  | B754_infinity0 sx ->
    join_bits mw ew sx Z0 (Coq_Z.sub (Coq_Z.pow (Zpos (XO XH)) ew) (Zpos XH))
  | B754_nan0 (sx, plx) ->
    join_bits mw ew sx (Zpos plx)
      (Coq_Z.sub (Coq_Z.pow (Zpos (XO XH)) ew) (Zpos XH))
  | B754_finite0 (sx, mx, ex) ->
    let m = Coq_Z.sub (Zpos mx) (Coq_Z.pow (Zpos (XO XH)) mw) in
    if Coq_Z.leb Z0 m
    then join_bits mw ew sx m
           (Coq_Z.add (Coq_Z.sub ex (emin prec emax)) (Zpos XH))
    else join_bits mw ew sx (Zpos mx) Z0)

(** val binary_float_of_bits_aux : z -> z -> z -> full_float **)

let binary_float_of_bits_aux mw ew =
  let prec = Coq_Z.add mw (Zpos XH) in
  let emax = Coq_Z.pow (Zpos (XO XH)) (Coq_Z.sub ew (Zpos XH)) in
  (fun x ->
  let (p, ex) = split_bits mw ew x in
  let (sx, mx) = p in
  if Coq_Z.eqb ex Z0
  then (match mx with
        | Z0 -> F754_zero sx
        | Zpos px -> F754_finite (sx, px, (emin prec emax))
        | Zneg _ -> F754_nan (false, XH))
  else if Coq_Z.eqb ex (Coq_Z.sub (Coq_Z.pow (Zpos (XO XH)) ew) (Zpos XH))
       then (match mx with
             | Z0 -> F754_infinity sx
             | Zpos plx -> F754_nan (sx, plx)
             | Zneg _ -> F754_nan (false, XH))
       else (match Coq_Z.add mx (Coq_Z.pow (Zpos (XO XH)) mw) with
             | Zpos px ->
               F754_finite (sx, px,
                 (Coq_Z.sub (Coq_Z.add ex (emin prec emax)) (Zpos XH)))
             | _ -> F754_nan (false, XH)))

(** val binary_float_of_bits : z -> z -> z -> binary_float0 **)

let binary_float_of_bits mw ew x =
  let prec = Coq_Z.add mw (Zpos XH) in
  let emax = Coq_Z.pow (Zpos (XO XH)) (Coq_Z.sub ew (Zpos XH)) in
  fF2B prec emax (binary_float_of_bits_aux mw ew x)

type binary32 = binary_float0

(** val b32_of_bits : z -> binary32 **)

let b32_of_bits =
  binary_float_of_bits (Zpos (XI (XI (XI (XO XH))))) (Zpos (XO (XO (XO XH))))

(** val bits_of_b32 : binary32 -> z **)

let bits_of_b32 =
  bits_of_binary_float (Zpos (XI (XI (XI (XO XH))))) (Zpos (XO (XO (XO XH))))

type binary64 = binary_float0

(** val b64_of_bits : z -> binary64 **)

let b64_of_bits =
  binary_float_of_bits (Zpos (XO (XO (XI (XO (XI XH)))))) (Zpos (XI (XI (XO
    XH))))

(** val bits_of_b64 : binary64 -> z **)

let bits_of_b64 =
  bits_of_binary_float (Zpos (XO (XO (XI (XO (XI XH)))))) (Zpos (XI (XI (XO
    XH))))

(** val ptr64 : bool **)

let ptr64 =
  true

(** val big_endian : bool **)

let big_endian =
  false

(** val default_nan_64 : bool * positive **)

let default_nan_64 =
  (true,
    (let rec f = function
     | O -> XH
     | S n2 -> XO (f n2)
     in f (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val default_nan_32 : bool * positive **)

let default_nan_32 =
  (true,
    (let rec f = function
     | O -> XH
     | S n2 -> XO (f n2)
     in f (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))

(** val choose_nan_64 : (bool * positive) list -> bool * positive **)

let choose_nan_64 = function
| [] -> default_nan_64
| n1 :: _ -> n1

(** val choose_nan_32 : (bool * positive) list -> bool * positive **)

let choose_nan_32 = function
| [] -> default_nan_32
| n1 :: _ -> n1

(** val float_of_single_preserves_sNaN : bool **)

let float_of_single_preserves_sNaN =
  false

(** val float_conversion_default_nan : bool **)

let float_conversion_default_nan =
  false

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

module Make =
 functor (WS:WORDSIZE) ->
 struct
  (** val wordsize : nat **)

  let wordsize =
    WS.wordsize

  (** val zwordsize : z **)

  let zwordsize =
    Coq_Z.of_nat wordsize

  (** val modulus : z **)

  let modulus =
    two_power_nat wordsize

  (** val half_modulus : z **)

  let half_modulus =
    Coq_Z.div modulus (Zpos (XO XH))

  (** val max_unsigned : z **)

  let max_unsigned =
    Coq_Z.sub modulus (Zpos XH)

  (** val max_signed : z **)

  let max_signed =
    Coq_Z.sub half_modulus (Zpos XH)

  (** val min_signed : z **)

  let min_signed =
    Coq_Z.opp half_modulus

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : int -> z **)

  let intval i0 =
    i0

  (** val coq_Z_mod_modulus : z -> z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> p_mod_two_p p wordsize
  | Zneg p ->
    let r = p_mod_two_p p wordsize in
    if zeq r Z0 then Z0 else Coq_Z.sub modulus r

  (** val unsigned : int -> z **)

  let unsigned n1 =
    n1

  (** val signed : int -> z **)

  let signed n1 =
    let x = unsigned n1 in
    if zlt x half_modulus then x else Coq_Z.sub x modulus

  (** val repr : z -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val zero : int **)

  let zero =
    repr Z0

  (** val one : int **)

  let one =
    repr (Zpos XH)

  (** val mone : int **)

  let mone =
    repr (Zneg XH)

  (** val iwordsize : int **)

  let iwordsize =
    repr zwordsize

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    zeq

  (** val eq : int -> int -> bool **)

  let eq x y =
    if zeq (unsigned x) (unsigned y) then true else false

  (** val lt : int -> int -> bool **)

  let lt x y =
    if zlt (signed x) (signed y) then true else false

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    if zlt (unsigned x) (unsigned y) then true else false

  (** val neg : int -> int **)

  let neg x =
    repr (Coq_Z.opp (unsigned x))

  (** val add : int -> int -> int **)

  let add x y =
    repr (Coq_Z.add (unsigned x) (unsigned y))

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Coq_Z.sub (unsigned x) (unsigned y))

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Coq_Z.mul (unsigned x) (unsigned y))

  (** val divs : int -> int -> int **)

  let divs x y =
    repr (Coq_Z.quot (signed x) (signed y))

  (** val mods : int -> int -> int **)

  let mods x y =
    repr (Coq_Z.rem (signed x) (signed y))

  (** val divu : int -> int -> int **)

  let divu x y =
    repr (Coq_Z.div (unsigned x) (unsigned y))

  (** val modu : int -> int -> int **)

  let modu x y =
    repr (Coq_Z.modulo (unsigned x) (unsigned y))

  (** val coq_and : int -> int -> int **)

  let coq_and x y =
    repr (Coq_Z.coq_land (unsigned x) (unsigned y))

  (** val coq_or : int -> int -> int **)

  let coq_or x y =
    repr (Coq_Z.coq_lor (unsigned x) (unsigned y))

  (** val xor : int -> int -> int **)

  let xor x y =
    repr (Coq_Z.coq_lxor (unsigned x) (unsigned y))

  (** val not : int -> int **)

  let not x =
    xor x mone

  (** val shl : int -> int -> int **)

  let shl x y =
    repr (Coq_Z.shiftl (unsigned x) (unsigned y))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr (Coq_Z.shiftr (unsigned x) (unsigned y))

  (** val shr : int -> int -> int **)

  let shr x y =
    repr (Coq_Z.shiftr (signed x) (unsigned y))

  (** val rol : int -> int -> int **)

  let rol x y =
    let n1 = Coq_Z.modulo (unsigned y) zwordsize in
    repr
      (Coq_Z.coq_lor (Coq_Z.shiftl (unsigned x) n1)
        (Coq_Z.shiftr (unsigned x) (Coq_Z.sub zwordsize n1)))

  (** val ror : int -> int -> int **)

  let ror x y =
    let n1 = Coq_Z.modulo (unsigned y) zwordsize in
    repr
      (Coq_Z.coq_lor (Coq_Z.shiftr (unsigned x) n1)
        (Coq_Z.shiftl (unsigned x) (Coq_Z.sub zwordsize n1)))

  (** val rolm : int -> int -> int -> int **)

  let rolm x a m =
    coq_and (rol x a) m

  (** val shrx : int -> int -> int **)

  let shrx x y =
    divs x (shl one y)

  (** val mulhu : int -> int -> int **)

  let mulhu x y =
    repr (Coq_Z.div (Coq_Z.mul (unsigned x) (unsigned y)) modulus)

  (** val mulhs : int -> int -> int **)

  let mulhs x y =
    repr (Coq_Z.div (Coq_Z.mul (signed x) (signed y)) modulus)

  (** val negative : int -> int **)

  let negative x =
    if lt x zero then one else zero

  (** val add_carry : int -> int -> int -> int **)

  let add_carry x y cin =
    if zlt (Coq_Z.add (Coq_Z.add (unsigned x) (unsigned y)) (unsigned cin))
         modulus
    then zero
    else one

  (** val add_overflow : int -> int -> int -> int **)

  let add_overflow x y cin =
    let s = Coq_Z.add (Coq_Z.add (signed x) (signed y)) (signed cin) in
    if (&&) (proj_sumbool (zle min_signed s))
         (proj_sumbool (zle s max_signed))
    then zero
    else one

  (** val sub_borrow : int -> int -> int -> int **)

  let sub_borrow x y bin =
    if zlt (Coq_Z.sub (Coq_Z.sub (unsigned x) (unsigned y)) (unsigned bin)) Z0
    then one
    else zero

  (** val sub_overflow : int -> int -> int -> int **)

  let sub_overflow x y bin =
    let s = Coq_Z.sub (Coq_Z.sub (signed x) (signed y)) (signed bin) in
    if (&&) (proj_sumbool (zle min_signed s))
         (proj_sumbool (zle s max_signed))
    then zero
    else one

  (** val shr_carry : int -> int -> int **)

  let shr_carry x y =
    if (&&) (lt x zero) (negb (eq (coq_and x (sub (shl one y) one)) zero))
    then one
    else zero

  (** val zero_ext : z -> int -> int **)

  let zero_ext n1 x =
    repr (zzero_ext n1 (unsigned x))

  (** val sign_ext : z -> int -> int **)

  let sign_ext n1 x =
    repr (zsign_ext n1 (unsigned x))

  (** val one_bits : int -> int list **)

  let one_bits x =
    map repr (z_one_bits wordsize (unsigned x) Z0)

  (** val is_power2 : int -> int option **)

  let is_power2 x =
    match z_is_power2 (unsigned x) with
    | Some i0 -> Some (repr i0)
    | None -> None

  (** val cmp : comparison0 -> int -> int -> bool **)

  let cmp c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> lt x y
    | Cle -> negb (lt y x)
    | Cgt -> lt y x
    | Cge -> negb (lt x y)

  (** val cmpu : comparison0 -> int -> int -> bool **)

  let cmpu c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> ltu x y
    | Cle -> negb (ltu y x)
    | Cgt -> ltu y x
    | Cge -> negb (ltu x y)

  (** val notbool : int -> int **)

  let notbool x =
    if eq x zero then one else zero

  (** val divmodu2 : int -> int -> int -> (int * int) option **)

  let divmodu2 nhi nlo d =
    if eq_dec d zero
    then None
    else let (q, r) =
           Coq_Z.div_eucl
             (Coq_Z.add (Coq_Z.mul (unsigned nhi) modulus) (unsigned nlo))
             (unsigned d)
         in
         if zle q max_unsigned then Some ((repr q), (repr r)) else None

  (** val divmods2 : int -> int -> int -> (int * int) option **)

  let divmods2 nhi nlo d =
    if eq_dec d zero
    then None
    else let (q, r) =
           Coq_Z.quotrem
             (Coq_Z.add (Coq_Z.mul (signed nhi) modulus) (unsigned nlo))
             (signed d)
         in
         if (&&) (proj_sumbool (zle min_signed q))
              (proj_sumbool (zle q max_signed))
         then Some ((repr q), (repr r))
         else None

  (** val testbit : int -> z -> bool **)

  let testbit x i0 =
    Coq_Z.testbit (unsigned x) i0

  (** val int_of_one_bits : int list -> int **)

  let rec int_of_one_bits = function
  | [] -> zero
  | a :: b -> add (shl one a) (int_of_one_bits b)

  (** val no_overlap : int -> z -> int -> z -> bool **)

  let no_overlap ofs1 sz1 ofs2 sz2 =
    let x1 = unsigned ofs1 in
    let x2 = unsigned ofs2 in
    (&&)
      ((&&) (proj_sumbool (zlt (Coq_Z.add x1 sz1) modulus))
        (proj_sumbool (zlt (Coq_Z.add x2 sz2) modulus)))
      ((||) (proj_sumbool (zle (Coq_Z.add x1 sz1) x2))
        (proj_sumbool (zle (Coq_Z.add x2 sz2) x1)))

  (** val size : int -> z **)

  let size x =
    zsize (unsigned x)

  (** val unsigned_bitfield_extract : z -> z -> int -> int **)

  let unsigned_bitfield_extract pos0 width n1 =
    zero_ext width (shru n1 (repr pos0))

  (** val signed_bitfield_extract : z -> z -> int -> int **)

  let signed_bitfield_extract pos0 width n1 =
    sign_ext width (shru n1 (repr pos0))

  (** val bitfield_insert : z -> z -> int -> int -> int **)

  let bitfield_insert pos0 width n1 p =
    let mask0 = shl (repr (Coq_Z.sub (two_p width) (Zpos XH))) (repr pos0) in
    coq_or (shl (zero_ext width p) (repr pos0)) (coq_and n1 (not mask0))
 end

module Wordsize_32 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
 end

module Int = Make(Wordsize_32)

module Wordsize_8 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S O)))))))
 end

module Byte = Make(Wordsize_8)

module Wordsize_64 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 end

module Int64 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    Wordsize_64.wordsize

  (** val zwordsize : z **)

  let zwordsize =
    Coq_Z.of_nat wordsize

  (** val modulus : z **)

  let modulus =
    two_power_nat wordsize

  (** val half_modulus : z **)

  let half_modulus =
    Coq_Z.div modulus (Zpos (XO XH))

  (** val max_unsigned : z **)

  let max_unsigned =
    Coq_Z.sub modulus (Zpos XH)

  (** val max_signed : z **)

  let max_signed =
    Coq_Z.sub half_modulus (Zpos XH)

  (** val min_signed : z **)

  let min_signed =
    Coq_Z.opp half_modulus

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : int -> z **)

  let intval i0 =
    i0

  (** val coq_Z_mod_modulus : z -> z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> p_mod_two_p p wordsize
  | Zneg p ->
    let r = p_mod_two_p p wordsize in
    if zeq r Z0 then Z0 else Coq_Z.sub modulus r

  (** val unsigned : int -> z **)

  let unsigned n1 =
    n1

  (** val signed : int -> z **)

  let signed n1 =
    let x = unsigned n1 in
    if zlt x half_modulus then x else Coq_Z.sub x modulus

  (** val repr : z -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val zero : int **)

  let zero =
    repr Z0

  (** val mone : int **)

  let mone =
    repr (Zneg XH)

  (** val iwordsize : int **)

  let iwordsize =
    repr zwordsize

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    zeq

  (** val eq : int -> int -> bool **)

  let eq x y =
    if zeq (unsigned x) (unsigned y) then true else false

  (** val lt : int -> int -> bool **)

  let lt x y =
    if zlt (signed x) (signed y) then true else false

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    if zlt (unsigned x) (unsigned y) then true else false

  (** val add : int -> int -> int **)

  let add x y =
    repr (Coq_Z.add (unsigned x) (unsigned y))

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Coq_Z.sub (unsigned x) (unsigned y))

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Coq_Z.mul (unsigned x) (unsigned y))

  (** val divs : int -> int -> int **)

  let divs x y =
    repr (Coq_Z.quot (signed x) (signed y))

  (** val mods : int -> int -> int **)

  let mods x y =
    repr (Coq_Z.rem (signed x) (signed y))

  (** val divu : int -> int -> int **)

  let divu x y =
    repr (Coq_Z.div (unsigned x) (unsigned y))

  (** val modu : int -> int -> int **)

  let modu x y =
    repr (Coq_Z.modulo (unsigned x) (unsigned y))

  (** val coq_and : int -> int -> int **)

  let coq_and x y =
    repr (Coq_Z.coq_land (unsigned x) (unsigned y))

  (** val coq_or : int -> int -> int **)

  let coq_or x y =
    repr (Coq_Z.coq_lor (unsigned x) (unsigned y))

  (** val xor : int -> int -> int **)

  let xor x y =
    repr (Coq_Z.coq_lxor (unsigned x) (unsigned y))

  (** val shl : int -> int -> int **)

  let shl x y =
    repr (Coq_Z.shiftl (unsigned x) (unsigned y))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr (Coq_Z.shiftr (unsigned x) (unsigned y))

  (** val shr : int -> int -> int **)

  let shr x y =
    repr (Coq_Z.shiftr (signed x) (unsigned y))

  (** val cmp : comparison0 -> int -> int -> bool **)

  let cmp c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> lt x y
    | Cle -> negb (lt y x)
    | Cgt -> lt y x
    | Cge -> negb (lt x y)

  (** val cmpu : comparison0 -> int -> int -> bool **)

  let cmpu c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> ltu x y
    | Cle -> negb (ltu y x)
    | Cgt -> ltu y x
    | Cge -> negb (ltu x y)

  (** val iwordsize' : Int.int **)

  let iwordsize' =
    Int.repr zwordsize

  (** val loword : int -> Int.int **)

  let loword n1 =
    Int.repr (unsigned n1)
 end

module Wordsize_Ptrofs =
 struct
  (** val wordsize : nat **)

  let wordsize =
    if ptr64
    then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
 end

module Ptrofs =
 struct
  (** val wordsize : nat **)

  let wordsize =
    Wordsize_Ptrofs.wordsize

  (** val modulus : z **)

  let modulus =
    two_power_nat wordsize

  (** val half_modulus : z **)

  let half_modulus =
    Coq_Z.div modulus (Zpos (XO XH))

  (** val max_signed : z **)

  let max_signed =
    Coq_Z.sub half_modulus (Zpos XH)

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : int -> z **)

  let intval i0 =
    i0

  (** val coq_Z_mod_modulus : z -> z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> p_mod_two_p p wordsize
  | Zneg p ->
    let r = p_mod_two_p p wordsize in
    if zeq r Z0 then Z0 else Coq_Z.sub modulus r

  (** val unsigned : int -> z **)

  let unsigned n1 =
    n1

  (** val signed : int -> z **)

  let signed n1 =
    let x = unsigned n1 in
    if zlt x half_modulus then x else Coq_Z.sub x modulus

  (** val repr : z -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val zero : int **)

  let zero =
    repr Z0

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    zeq

  (** val eq : int -> int -> bool **)

  let eq x y =
    if zeq (unsigned x) (unsigned y) then true else false

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    if zlt (unsigned x) (unsigned y) then true else false

  (** val add : int -> int -> int **)

  let add x y =
    repr (Coq_Z.add (unsigned x) (unsigned y))

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Coq_Z.sub (unsigned x) (unsigned y))

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Coq_Z.mul (unsigned x) (unsigned y))

  (** val divs : int -> int -> int **)

  let divs x y =
    repr (Coq_Z.quot (signed x) (signed y))

  (** val cmpu : comparison0 -> int -> int -> bool **)

  let cmpu c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> ltu x y
    | Cle -> negb (ltu y x)
    | Cgt -> ltu y x
    | Cge -> negb (ltu x y)

  (** val to_int : int -> Int.int **)

  let to_int x =
    Int.repr (unsigned x)

  (** val to_int64 : int -> Int64.int **)

  let to_int64 x =
    Int64.repr (unsigned x)

  (** val of_int : Int.int -> int **)

  let of_int x =
    repr (Int.unsigned x)

  (** val of_intu : Int.int -> int **)

  let of_intu =
    of_int

  (** val of_ints : Int.int -> int **)

  let of_ints x =
    repr (Int.signed x)

  (** val of_int64 : Int64.int -> int **)

  let of_int64 x =
    repr (Int64.unsigned x)
 end

(** val beq_dec : z -> z -> binary_float0 -> binary_float0 -> bool **)

let beq_dec _ _ f1 f2 =
  match f1 with
  | B754_zero0 s ->
    (match f2 with
     | B754_zero0 s0 ->
       if s then if s0 then true else false else if s0 then false else true
     | _ -> false)
  | B754_infinity0 s ->
    (match f2 with
     | B754_infinity0 s0 ->
       if s then if s0 then true else false else if s0 then false else true
     | _ -> false)
  | B754_nan0 (s, pl) ->
    (match f2 with
     | B754_nan0 (s0, pl0) ->
       if s
       then if s0 then Coq_Pos.eq_dec pl pl0 else false
       else if s0 then false else Coq_Pos.eq_dec pl pl0
     | _ -> false)
  | B754_finite0 (s, m, e) ->
    (match f2 with
     | B754_finite0 (s0, m0, e0) ->
       if s
       then if s0
            then let s1 = Coq_Pos.eq_dec m m0 in
                 if s1 then Coq_Z.eq_dec e e0 else false
            else false
       else if s0
            then false
            else let s1 = Coq_Pos.eq_dec m m0 in
                 if s1 then Coq_Z.eq_dec e e0 else false
     | _ -> false)

(** val bofZ : z -> z -> z -> binary_float0 **)

let bofZ prec emax n1 =
  binary_normalize0 prec emax Mode_NE n1 Z0 false

(** val zofB : z -> z -> binary_float0 -> z option **)

let zofB _ _ = function
| B754_zero0 _ -> Some Z0
| B754_finite0 (s, m, e0) ->
  (match e0 with
   | Z0 -> Some (cond_Zopp s (Zpos m))
   | Zpos e ->
     Some (Coq_Z.mul (cond_Zopp s (Zpos m)) (Coq_Z.pow_pos radix2 e))
   | Zneg e ->
     Some (cond_Zopp s (Coq_Z.div (Zpos m) (Coq_Z.pow_pos radix2 e))))
| _ -> None

(** val zofB_range : z -> z -> binary_float0 -> z -> z -> z option **)

let zofB_range prec emax f zmin zmax =
  match zofB prec emax f with
  | Some z0 ->
    if (&&) (Coq_Z.leb zmin z0) (Coq_Z.leb z0 zmax) then Some z0 else None
  | None -> None

(** val bconv :
    z -> z -> z -> z -> (binary_float0 -> binary_float0) -> mode ->
    binary_float0 -> binary_float0 **)

let bconv _ _ prec2 emax2 conv_nan md f = match f with
| B754_nan0 (_, _) -> build_nan prec2 emax2 (conv_nan f)
| B754_finite0 (s, m, e) ->
  binary_normalize0 prec2 emax2 md (cond_Zopp s (Zpos m)) e s
| x -> x

type float = binary64

type float32 = binary32

(** val cmp_of_comparison : comparison0 -> comparison option -> bool **)

let cmp_of_comparison c x =
  match c with
  | Ceq ->
    (match x with
     | Some c0 -> (match c0 with
                   | Eq -> true
                   | _ -> false)
     | None -> false)
  | Cne ->
    (match x with
     | Some c0 -> (match c0 with
                   | Eq -> false
                   | _ -> true)
     | None -> true)
  | Clt ->
    (match x with
     | Some c0 -> (match c0 with
                   | Lt -> true
                   | _ -> false)
     | None -> false)
  | Cle ->
    (match x with
     | Some c0 -> (match c0 with
                   | Gt -> false
                   | _ -> true)
     | None -> false)
  | Cgt ->
    (match x with
     | Some c0 -> (match c0 with
                   | Gt -> true
                   | _ -> false)
     | None -> false)
  | Cge ->
    (match x with
     | Some c0 -> (match c0 with
                   | Lt -> false
                   | _ -> true)
     | None -> false)

(** val quiet_nan_64_payload : positive -> positive **)

let quiet_nan_64_payload p =
  Coq_Z.to_pos
    (p_mod_two_p
      (Coq_Pos.coq_lor p
        (iter_nat (fun x -> XO x) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))))))))))))))))))))))))))))) XH))
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val quiet_nan_64 : (bool * positive) -> float **)

let quiet_nan_64 = function
| (s, p) -> B754_nan0 (s, (quiet_nan_64_payload p))

(** val default_nan_0 : float **)

let default_nan_0 =
  quiet_nan_64 default_nan_64

(** val quiet_nan_32_payload : positive -> positive **)

let quiet_nan_32_payload p =
  Coq_Z.to_pos
    (p_mod_two_p
      (Coq_Pos.coq_lor p
        (iter_nat (fun x -> XO x) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S O)))))))))))))))))))))) XH))
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))

(** val quiet_nan_32 : (bool * positive) -> float32 **)

let quiet_nan_32 = function
| (s, p) -> B754_nan0 (s, (quiet_nan_32_payload p))

(** val default_nan_1 : float32 **)

let default_nan_1 =
  quiet_nan_32 default_nan_32

module Float =
 struct
  (** val expand_nan_payload : positive -> positive **)

  let expand_nan_payload p =
    Coq_Pos.shiftl_nat p (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))

  (** val expand_nan : bool -> positive -> binary_float0 **)

  let expand_nan s p =
    B754_nan0 (s, (expand_nan_payload p))

  (** val of_single_nan : float32 -> float **)

  let of_single_nan = function
  | B754_nan0 (s, p) ->
    if float_conversion_default_nan
    then default_nan_0
    else if float_of_single_preserves_sNaN
         then expand_nan s p
         else quiet_nan_64 (s, (expand_nan_payload p))
  | _ -> default_nan_0

  (** val reduce_nan_payload : positive -> positive **)

  let reduce_nan_payload p =
    Coq_Pos.shiftr_nat (quiet_nan_64_payload p) (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))

  (** val to_single_nan : float -> float32 **)

  let to_single_nan = function
  | B754_nan0 (s, p) ->
    if float_conversion_default_nan
    then default_nan_1
    else quiet_nan_32 (s, (reduce_nan_payload p))
  | _ -> default_nan_1

  (** val cons_pl :
      float -> (bool * positive) list -> (bool * positive) list **)

  let cons_pl x l =
    match x with
    | B754_nan0 (s, p) -> (s, p) :: l
    | _ -> l

  (** val binop_nan : float -> float -> float **)

  let binop_nan x y =
    quiet_nan_64 (choose_nan_64 (cons_pl x (cons_pl y [])))

  (** val zero : float **)

  let zero =
    B754_zero0 false

  (** val eq_dec : float -> float -> bool **)

  let eq_dec =
    beq_dec (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO
      (XO (XO (XO (XO XH)))))))))))

  (** val add : float -> float -> float **)

  let add =
    bplus0 (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO
      (XO (XO (XO (XO XH))))))))))) binop_nan Mode_NE

  (** val sub : float -> float -> float **)

  let sub =
    bminus0 (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO
      (XO (XO (XO (XO XH))))))))))) binop_nan Mode_NE

  (** val mul : float -> float -> float **)

  let mul =
    bmult0 (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO
      (XO (XO (XO (XO XH))))))))))) binop_nan Mode_NE

  (** val div : float -> float -> float **)

  let div =
    bdiv0 (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO
      (XO (XO (XO (XO XH))))))))))) binop_nan Mode_NE

  (** val compare : float -> float -> comparison option **)

  let compare f1 f2 =
    bcompare0 (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO
      (XO (XO (XO (XO (XO XH))))))))))) f1 f2

  (** val cmp : comparison0 -> float -> float -> bool **)

  let cmp c f1 f2 =
    cmp_of_comparison c (compare f1 f2)

  (** val of_single : float32 -> float **)

  let of_single =
    bconv (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      XH)))))))) (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO
      (XO (XO (XO (XO (XO XH))))))))))) of_single_nan Mode_NE

  (** val to_single : float -> float32 **)

  let to_single =
    bconv (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO
      (XO (XO (XO (XO XH))))))))))) (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO
      (XO (XO (XO (XO (XO (XO XH)))))))) to_single_nan Mode_NE

  (** val to_int : float -> Int.int option **)

  let to_int f =
    option_map Int.repr
      (zofB_range (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO XH))))))))))) f Int.min_signed Int.max_signed)

  (** val to_intu : float -> Int.int option **)

  let to_intu f =
    option_map Int.repr
      (zofB_range (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO XH))))))))))) f Z0 Int.max_unsigned)

  (** val to_long : float -> Int64.int option **)

  let to_long f =
    option_map Int64.repr
      (zofB_range (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO XH))))))))))) f Int64.min_signed
        Int64.max_signed)

  (** val to_longu : float -> Int64.int option **)

  let to_longu f =
    option_map Int64.repr
      (zofB_range (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO XH))))))))))) f Z0 Int64.max_unsigned)

  (** val of_int : Int.int -> float **)

  let of_int n1 =
    bofZ (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      (XO (XO (XO XH))))))))))) (Int.signed n1)

  (** val of_intu : Int.int -> float **)

  let of_intu n1 =
    bofZ (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      (XO (XO (XO XH))))))))))) (Int.unsigned n1)

  (** val of_long : Int64.int -> float **)

  let of_long n1 =
    bofZ (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      (XO (XO (XO XH))))))))))) (Int64.signed n1)

  (** val of_longu : Int64.int -> float **)

  let of_longu n1 =
    bofZ (Zpos (XI (XO (XI (XO (XI XH)))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      (XO (XO (XO XH))))))))))) (Int64.unsigned n1)

  (** val to_bits : float -> Int64.int **)

  let to_bits f =
    Int64.repr (bits_of_b64 f)

  (** val of_bits : Int64.int -> float **)

  let of_bits b =
    b64_of_bits (Int64.unsigned b)
 end

module Float32 =
 struct
  (** val cons_pl :
      float32 -> (bool * positive) list -> (bool * positive) list **)

  let cons_pl x l =
    match x with
    | B754_nan0 (s, p) -> (s, p) :: l
    | _ -> l

  (** val binop_nan : float32 -> float32 -> float32 **)

  let binop_nan x y =
    quiet_nan_32 (choose_nan_32 (cons_pl x (cons_pl y [])))

  (** val zero : float32 **)

  let zero =
    B754_zero0 false

  (** val eq_dec : float32 -> float32 -> bool **)

  let eq_dec =
    beq_dec (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      XH))))))))

  (** val add : float32 -> float32 -> float32 **)

  let add =
    bplus0 (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      XH)))))))) binop_nan Mode_NE

  (** val sub : float32 -> float32 -> float32 **)

  let sub =
    bminus0 (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      XH)))))))) binop_nan Mode_NE

  (** val mul : float32 -> float32 -> float32 **)

  let mul =
    bmult0 (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      XH)))))))) binop_nan Mode_NE

  (** val div : float32 -> float32 -> float32 **)

  let div =
    bdiv0 (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      XH)))))))) binop_nan Mode_NE

  (** val compare : float32 -> float32 -> comparison option **)

  let compare f1 f2 =
    bcompare0 (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      XH)))))))) f1 f2

  (** val cmp : comparison0 -> float32 -> float32 -> bool **)

  let cmp c f1 f2 =
    cmp_of_comparison c (compare f1 f2)

  (** val to_int : float32 -> Int.int option **)

  let to_int f =
    option_map Int.repr
      (zofB_range (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO
        (XO XH)))))))) f Int.min_signed Int.max_signed)

  (** val to_intu : float32 -> Int.int option **)

  let to_intu f =
    option_map Int.repr
      (zofB_range (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO
        (XO XH)))))))) f Z0 Int.max_unsigned)

  (** val to_long : float32 -> Int64.int option **)

  let to_long f =
    option_map Int64.repr
      (zofB_range (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO
        (XO XH)))))))) f Int64.min_signed Int64.max_signed)

  (** val to_longu : float32 -> Int64.int option **)

  let to_longu f =
    option_map Int64.repr
      (zofB_range (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO
        (XO XH)))))))) f Z0 Int64.max_unsigned)

  (** val of_int : Int.int -> float32 **)

  let of_int n1 =
    bofZ (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      XH)))))))) (Int.signed n1)

  (** val of_intu : Int.int -> float32 **)

  let of_intu n1 =
    bofZ (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      XH)))))))) (Int.unsigned n1)

  (** val of_long : Int64.int -> float32 **)

  let of_long n1 =
    bofZ (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      XH)))))))) (Int64.signed n1)

  (** val of_longu : Int64.int -> float32 **)

  let of_longu n1 =
    bofZ (Zpos (XO (XO (XO (XI XH))))) (Zpos (XO (XO (XO (XO (XO (XO (XO
      XH)))))))) (Int64.unsigned n1)

  (** val to_bits : float32 -> Int.int **)

  let to_bits f =
    Int.repr (bits_of_b32 f)

  (** val of_bits : Int.int -> float32 **)

  let of_bits b =
    b32_of_bits (Int.unsigned b)
 end

type ident = positive

(** val ident_eq : positive -> positive -> bool **)

let ident_eq =
  peq

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

(** val cc_default : calling_convention **)

let cc_default =
  { cc_vararg = None; cc_unproto = false; cc_structret = false }

(** val calling_convention_eq :
    calling_convention -> calling_convention -> bool **)

let calling_convention_eq x y =
  let { cc_vararg = cc_vararg0; cc_unproto = cc_unproto0; cc_structret =
    cc_structret0 } = x
  in
  let { cc_vararg = cc_vararg1; cc_unproto = cc_unproto1; cc_structret =
    cc_structret1 } = y
  in
  if match cc_vararg0 with
     | Some a ->
       (match cc_vararg1 with
        | Some z0 -> Coq_Z.eq_dec a z0
        | None -> false)
     | None -> (match cc_vararg1 with
                | Some _ -> false
                | None -> true)
  then if bool_dec cc_unproto0 cc_unproto1
       then bool_dec cc_structret0 cc_structret1
       else false
  else false

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

(** val mptr : memory_chunk **)

let mptr =
  if ptr64 then Mint64 else Mint32

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

(** val eq_block : positive -> positive -> bool **)

let eq_block =
  peq

type val0 =
| Vundef
| Vint of Int.int
| Vlong of Int64.int
| Vfloat of float
| Vsingle of float32
| Vptr of block * Ptrofs.int

(** val vzero : val0 **)

let vzero =
  Vint Int.zero

(** val vone : val0 **)

let vone =
  Vint Int.one

(** val vtrue : val0 **)

let vtrue =
  Vint Int.one

(** val vfalse : val0 **)

let vfalse =
  Vint Int.zero

(** val vptrofs : Ptrofs.int -> val0 **)

let vptrofs n1 =
  if ptr64 then Vlong (Ptrofs.to_int64 n1) else Vint (Ptrofs.to_int n1)

module Val =
 struct
  (** val eq : val0 -> val0 -> bool **)

  let eq x y =
    match x with
    | Vundef -> (match y with
                 | Vundef -> true
                 | _ -> false)
    | Vint i0 -> (match y with
                  | Vint i1 -> Int.eq_dec i0 i1
                  | _ -> false)
    | Vlong i0 -> (match y with
                   | Vlong i1 -> Int64.eq_dec i0 i1
                   | _ -> false)
    | Vfloat f -> (match y with
                   | Vfloat f0 -> Float.eq_dec f f0
                   | _ -> false)
    | Vsingle f ->
      (match y with
       | Vsingle f0 -> Float32.eq_dec f f0
       | _ -> false)
    | Vptr (b, i0) ->
      (match y with
       | Vptr (b0, i1) -> if eq_block b b0 then Ptrofs.eq_dec i0 i1 else false
       | _ -> false)

  (** val of_bool : bool -> val0 **)

  let of_bool = function
  | true -> vtrue
  | false -> vfalse

  (** val is_bool : val0 -> bool **)

  let is_bool v =
    (||) (proj_sumbool (eq v vtrue)) (proj_sumbool (eq v vfalse))

  (** val norm_bool : val0 -> val0 **)

  let norm_bool v =
    if is_bool v then v else Vundef

  (** val cmp_different_blocks : comparison0 -> bool option **)

  let cmp_different_blocks = function
  | Ceq -> Some false
  | Cne -> Some true
  | _ -> None

  (** val cmpu_bool :
      (block -> z -> bool) -> comparison0 -> val0 -> val0 -> bool option **)

  let cmpu_bool valid_ptr =
    let weak_valid_ptr = fun b ofs ->
      (||) (valid_ptr b ofs) (valid_ptr b (Coq_Z.sub ofs (Zpos XH)))
    in
    (fun c v1 v2 ->
    match v1 with
    | Vint n1 ->
      (match v2 with
       | Vint n2 -> Some (Int.cmpu c n1 n2)
       | Vptr (b2, ofs2) ->
         if ptr64
         then None
         else if (&&) (Int.eq n1 Int.zero)
                   (weak_valid_ptr b2 (Ptrofs.unsigned ofs2))
              then cmp_different_blocks c
              else None
       | _ -> None)
    | Vptr (b1, ofs1) ->
      (match v2 with
       | Vint n2 ->
         if ptr64
         then None
         else if (&&) (Int.eq n2 Int.zero)
                   (weak_valid_ptr b1 (Ptrofs.unsigned ofs1))
              then cmp_different_blocks c
              else None
       | Vptr (b2, ofs2) ->
         if ptr64
         then None
         else if eq_block b1 b2
              then if (&&) (weak_valid_ptr b1 (Ptrofs.unsigned ofs1))
                        (weak_valid_ptr b2 (Ptrofs.unsigned ofs2))
                   then Some (Ptrofs.cmpu c ofs1 ofs2)
                   else None
              else if (&&) (valid_ptr b1 (Ptrofs.unsigned ofs1))
                        (valid_ptr b2 (Ptrofs.unsigned ofs2))
                   then cmp_different_blocks c
                   else None
       | _ -> None)
    | _ -> None)

  (** val cmplu_bool :
      (block -> z -> bool) -> comparison0 -> val0 -> val0 -> bool option **)

  let cmplu_bool valid_ptr =
    let weak_valid_ptr = fun b ofs ->
      (||) (valid_ptr b ofs) (valid_ptr b (Coq_Z.sub ofs (Zpos XH)))
    in
    (fun c v1 v2 ->
    match v1 with
    | Vlong n1 ->
      (match v2 with
       | Vlong n2 -> Some (Int64.cmpu c n1 n2)
       | Vptr (b2, ofs2) ->
         if negb ptr64
         then None
         else if (&&) (Int64.eq n1 Int64.zero)
                   (weak_valid_ptr b2 (Ptrofs.unsigned ofs2))
              then cmp_different_blocks c
              else None
       | _ -> None)
    | Vptr (b1, ofs1) ->
      (match v2 with
       | Vlong n2 ->
         if negb ptr64
         then None
         else if (&&) (Int64.eq n2 Int64.zero)
                   (weak_valid_ptr b1 (Ptrofs.unsigned ofs1))
              then cmp_different_blocks c
              else None
       | Vptr (b2, ofs2) ->
         if negb ptr64
         then None
         else if eq_block b1 b2
              then if (&&) (weak_valid_ptr b1 (Ptrofs.unsigned ofs1))
                        (weak_valid_ptr b2 (Ptrofs.unsigned ofs2))
                   then Some (Ptrofs.cmpu c ofs1 ofs2)
                   else None
              else if (&&) (valid_ptr b1 (Ptrofs.unsigned ofs1))
                        (valid_ptr b2 (Ptrofs.unsigned ofs2))
                   then cmp_different_blocks c
                   else None
       | _ -> None)
    | _ -> None)

  (** val load_result : memory_chunk -> val0 -> val0 **)

  let load_result chunk v =
    match chunk with
    | Mbool ->
      (match v with
       | Vint n1 ->
         norm_bool (Vint (Int.zero_ext (Zpos (XO (XO (XO XH)))) n1))
       | _ -> Vundef)
    | Mint8signed ->
      (match v with
       | Vint n1 -> Vint (Int.sign_ext (Zpos (XO (XO (XO XH)))) n1)
       | _ -> Vundef)
    | Mint8unsigned ->
      (match v with
       | Vint n1 -> Vint (Int.zero_ext (Zpos (XO (XO (XO XH)))) n1)
       | _ -> Vundef)
    | Mint16signed ->
      (match v with
       | Vint n1 -> Vint (Int.sign_ext (Zpos (XO (XO (XO (XO XH))))) n1)
       | _ -> Vundef)
    | Mint16unsigned ->
      (match v with
       | Vint n1 -> Vint (Int.zero_ext (Zpos (XO (XO (XO (XO XH))))) n1)
       | _ -> Vundef)
    | Mint32 ->
      (match v with
       | Vint n1 -> Vint n1
       | Vptr (b, ofs) -> if ptr64 then Vundef else Vptr (b, ofs)
       | _ -> Vundef)
    | Mint64 ->
      (match v with
       | Vlong n1 -> Vlong n1
       | Vptr (b, ofs) -> if ptr64 then Vptr (b, ofs) else Vundef
       | _ -> Vundef)
    | Mfloat32 -> (match v with
                   | Vsingle f -> Vsingle f
                   | _ -> Vundef)
    | Mfloat64 -> (match v with
                   | Vfloat f -> Vfloat f
                   | _ -> Vundef)
    | Many32 ->
      (match v with
       | Vint _ -> v
       | Vsingle _ -> v
       | Vptr (_, _) -> if ptr64 then Vundef else v
       | _ -> Vundef)
    | Many64 -> v
 end

(** val size_chunk : memory_chunk -> z **)

let size_chunk = function
| Mbool -> Zpos XH
| Mint8signed -> Zpos XH
| Mint8unsigned -> Zpos XH
| Mint16signed -> Zpos (XO XH)
| Mint16unsigned -> Zpos (XO XH)
| Mint32 -> Zpos (XO (XO XH))
| Mfloat32 -> Zpos (XO (XO XH))
| Many32 -> Zpos (XO (XO XH))
| _ -> Zpos (XO (XO (XO XH)))

(** val size_chunk_nat : memory_chunk -> nat **)

let size_chunk_nat chunk =
  Coq_Z.to_nat (size_chunk chunk)

(** val align_chunk : memory_chunk -> z **)

let align_chunk = function
| Mbool -> Zpos XH
| Mint8signed -> Zpos XH
| Mint8unsigned -> Zpos XH
| Mint16signed -> Zpos (XO XH)
| Mint16unsigned -> Zpos (XO XH)
| Mint64 -> Zpos (XO (XO (XO XH)))
| _ -> Zpos (XO (XO XH))

type quantity =
| Q32
| Q64

(** val quantity_eq : quantity -> quantity -> bool **)

let quantity_eq q1 q2 =
  match q1 with
  | Q32 -> (match q2 with
            | Q32 -> true
            | Q64 -> false)
  | Q64 -> (match q2 with
            | Q32 -> false
            | Q64 -> true)

(** val size_quantity_nat : quantity -> nat **)

let size_quantity_nat = function
| Q32 -> S (S (S (S O)))
| Q64 -> S (S (S (S (S (S (S (S O)))))))

type memval =
| Undef
| Byte of Byte.int
| Fragment of val0 * quantity * nat

(** val bytes_of_int : nat -> z -> Byte.int list **)

let rec bytes_of_int n1 x =
  match n1 with
  | O -> []
  | S m ->
    (Byte.repr x) :: (bytes_of_int m
                       (Coq_Z.div x (Zpos (XO (XO (XO (XO (XO (XO (XO (XO
                         XH)))))))))))

(** val int_of_bytes : Byte.int list -> z **)

let rec int_of_bytes = function
| [] -> Z0
| b :: l' ->
  Coq_Z.add (Byte.unsigned b)
    (Coq_Z.mul (int_of_bytes l') (Zpos (XO (XO (XO (XO (XO (XO (XO (XO
      XH))))))))))

(** val rev_if_be : Byte.int list -> Byte.int list **)

let rev_if_be l =
  if big_endian then rev0 l else l

(** val encode_int : nat -> z -> Byte.int list **)

let encode_int sz x =
  rev_if_be (bytes_of_int sz x)

(** val decode_int : Byte.int list -> z **)

let decode_int b =
  int_of_bytes (rev_if_be b)

(** val inj_bytes : Byte.int list -> memval list **)

let inj_bytes bl =
  map (fun x -> Byte x) bl

(** val proj_bytes : memval list -> Byte.int list option **)

let rec proj_bytes = function
| [] -> Some []
| m :: vl' ->
  (match m with
   | Byte b ->
     (match proj_bytes vl' with
      | Some bl -> Some (b :: bl)
      | None -> None)
   | _ -> None)

(** val inj_value_rec : nat -> val0 -> quantity -> memval list **)

let rec inj_value_rec n1 v q =
  match n1 with
  | O -> []
  | S m -> (Fragment (v, q, m)) :: (inj_value_rec m v q)

(** val inj_value : quantity -> val0 -> memval list **)

let inj_value q v =
  inj_value_rec (size_quantity_nat q) v q

(** val check_value : nat -> val0 -> quantity -> memval list -> bool **)

let rec check_value n1 v q vl =
  match n1 with
  | O -> (match vl with
          | [] -> true
          | _ :: _ -> false)
  | S m ->
    (match vl with
     | [] -> false
     | m0 :: vl' ->
       (match m0 with
        | Fragment (v', q', m') ->
          (&&)
            ((&&)
              ((&&) (proj_sumbool (Val.eq v v'))
                (proj_sumbool (quantity_eq q q')))
              (Nat.eqb m m'))
            (check_value m v q vl')
        | _ -> false))

(** val proj_value : quantity -> memval list -> val0 **)

let proj_value q vl = match vl with
| [] -> Vundef
| m :: _ ->
  (match m with
   | Fragment (v, _, _) ->
     if check_value (size_quantity_nat q) v q vl then v else Vundef
   | _ -> Vundef)

(** val encode_val : memory_chunk -> val0 -> memval list **)

let encode_val chunk v = match v with
| Vundef ->
  (match chunk with
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> repeat Undef (size_chunk_nat chunk))
| Vint n1 ->
  (match chunk with
   | Mbool -> inj_bytes (encode_int (S O) (Int.unsigned n1))
   | Mint8signed -> inj_bytes (encode_int (S O) (Int.unsigned n1))
   | Mint8unsigned -> inj_bytes (encode_int (S O) (Int.unsigned n1))
   | Mint16signed -> inj_bytes (encode_int (S (S O)) (Int.unsigned n1))
   | Mint16unsigned -> inj_bytes (encode_int (S (S O)) (Int.unsigned n1))
   | Mint32 -> inj_bytes (encode_int (S (S (S (S O)))) (Int.unsigned n1))
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> repeat Undef (size_chunk_nat chunk))
| Vlong n1 ->
  (match chunk with
   | Mint64 ->
     inj_bytes
       (encode_int (S (S (S (S (S (S (S (S O)))))))) (Int64.unsigned n1))
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> repeat Undef (size_chunk_nat chunk))
| Vfloat n1 ->
  (match chunk with
   | Mfloat64 ->
     inj_bytes
       (encode_int (S (S (S (S (S (S (S (S O))))))))
         (Int64.unsigned (Float.to_bits n1)))
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> repeat Undef (size_chunk_nat chunk))
| Vsingle n1 ->
  (match chunk with
   | Mfloat32 ->
     inj_bytes
       (encode_int (S (S (S (S O)))) (Int.unsigned (Float32.to_bits n1)))
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> repeat Undef (size_chunk_nat chunk))
| Vptr (_, _) ->
  (match chunk with
   | Mint32 ->
     if ptr64 then repeat Undef (S (S (S (S O)))) else inj_value Q32 v
   | Mint64 ->
     if ptr64
     then inj_value Q64 v
     else repeat Undef (S (S (S (S (S (S (S (S O))))))))
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> repeat Undef (size_chunk_nat chunk))

(** val decode_val : memory_chunk -> memval list -> val0 **)

let decode_val chunk vl =
  match proj_bytes vl with
  | Some bl ->
    (match chunk with
     | Mbool ->
       Val.norm_bool (Vint
         (Int.zero_ext (Zpos (XO (XO (XO XH)))) (Int.repr (decode_int bl))))
     | Mint8signed ->
       Vint (Int.sign_ext (Zpos (XO (XO (XO XH)))) (Int.repr (decode_int bl)))
     | Mint8unsigned ->
       Vint (Int.zero_ext (Zpos (XO (XO (XO XH)))) (Int.repr (decode_int bl)))
     | Mint16signed ->
       Vint
         (Int.sign_ext (Zpos (XO (XO (XO (XO XH)))))
           (Int.repr (decode_int bl)))
     | Mint16unsigned ->
       Vint
         (Int.zero_ext (Zpos (XO (XO (XO (XO XH)))))
           (Int.repr (decode_int bl)))
     | Mint32 -> Vint (Int.repr (decode_int bl))
     | Mint64 -> Vlong (Int64.repr (decode_int bl))
     | Mfloat32 -> Vsingle (Float32.of_bits (Int.repr (decode_int bl)))
     | Mfloat64 -> Vfloat (Float.of_bits (Int64.repr (decode_int bl)))
     | _ -> Vundef)
  | None ->
    (match chunk with
     | Mint32 ->
       if ptr64 then Vundef else Val.load_result chunk (proj_value Q32 vl)
     | Mint64 ->
       if ptr64 then Val.load_result chunk (proj_value Q64 vl) else Vundef
     | Many32 -> Val.load_result chunk (proj_value Q32 vl)
     | Many64 -> Val.load_result chunk (proj_value Q64 vl)
     | _ -> Vundef)

type permission =
| Freeable
| Writable
| Readable
| Nonempty

type perm_kind =
| Max
| Cur

module Mem =
 struct
  type mem' = { mem_contents : memval ZMap.t PMap.t;
                mem_access : (z -> perm_kind -> permission option) PMap.t;
                nextblock : block }

  (** val mem_contents : mem' -> memval ZMap.t PMap.t **)

  let mem_contents m =
    m.mem_contents

  (** val mem_access :
      mem' -> (z -> perm_kind -> permission option) PMap.t **)

  let mem_access m =
    m.mem_access

  (** val nextblock : mem' -> block **)

  let nextblock m =
    m.nextblock

  type mem = mem'

  (** val perm_order_dec : permission -> permission -> bool **)

  let perm_order_dec p1 p2 =
    match p1 with
    | Freeable -> true
    | Writable -> (match p2 with
                   | Freeable -> false
                   | _ -> true)
    | Readable ->
      (match p2 with
       | Freeable -> false
       | Writable -> false
       | _ -> true)
    | Nonempty -> (match p2 with
                   | Nonempty -> true
                   | _ -> false)

  (** val perm_order'_dec : permission option -> permission -> bool **)

  let perm_order'_dec op p =
    match op with
    | Some p0 -> perm_order_dec p0 p
    | None -> false

  (** val perm_dec : mem -> block -> z -> perm_kind -> permission -> bool **)

  let perm_dec m b ofs k p =
    perm_order'_dec (PMap.get b m.mem_access ofs k) p

  (** val range_perm_dec :
      mem -> block -> z -> z -> perm_kind -> permission -> bool **)

  let rec range_perm_dec m b lo hi k p =
    let s = zlt lo hi in
    if s
    then let s0 = perm_dec m b lo k p in
         if s0
         then let y = Coq_Z.add lo (Zpos XH) in range_perm_dec m b y hi k p
         else false
    else true

  (** val valid_access_dec :
      mem -> memory_chunk -> block -> z -> permission -> bool **)

  let valid_access_dec m chunk b ofs p =
    let s = range_perm_dec m b ofs (Coq_Z.add ofs (size_chunk chunk)) Cur p in
    if s then zdivide_dec (align_chunk chunk) ofs else false

  (** val valid_pointer : mem -> block -> z -> bool **)

  let valid_pointer m b ofs =
    proj_sumbool (perm_dec m b ofs Cur Nonempty)

  (** val weak_valid_pointer : mem -> block -> z -> bool **)

  let weak_valid_pointer m b ofs =
    (||) (valid_pointer m b ofs) (valid_pointer m b (Coq_Z.sub ofs (Zpos XH)))

  (** val empty : mem **)

  let empty =
    { mem_contents = (PMap.init (ZMap.init Undef)); mem_access =
      (PMap.init (fun _ _ -> None)); nextblock = XH }

  (** val alloc : mem -> z -> z -> mem' * block **)

  let alloc m lo hi =
    ({ mem_contents =
      (PMap.set m.nextblock (ZMap.init Undef) m.mem_contents); mem_access =
      (PMap.set m.nextblock (fun ofs _ ->
        if (&&) (proj_sumbool (zle lo ofs)) (proj_sumbool (zlt ofs hi))
        then Some Freeable
        else None) m.mem_access);
      nextblock = (Coq_Pos.succ m.nextblock) }, m.nextblock)

  (** val getN : nat -> z -> memval ZMap.t -> memval list **)

  let rec getN n1 p c =
    match n1 with
    | O -> []
    | S n' -> (ZMap.get p c) :: (getN n' (Coq_Z.add p (Zpos XH)) c)

  (** val load : memory_chunk -> mem -> block -> z -> val0 option **)

  let load chunk m b ofs =
    if valid_access_dec m chunk b ofs Readable
    then Some
           (decode_val chunk
             (getN (size_chunk_nat chunk) ofs (PMap.get b m.mem_contents)))
    else None

  (** val loadv : memory_chunk -> mem -> val0 -> val0 option **)

  let loadv chunk m = function
  | Vptr (b, ofs) -> load chunk m b (Ptrofs.unsigned ofs)
  | _ -> None

  (** val setN : memval list -> z -> memval ZMap.t -> memval ZMap.t **)

  let rec setN vl p c =
    match vl with
    | [] -> c
    | v :: vl' -> setN vl' (Coq_Z.add p (Zpos XH)) (ZMap.set p v c)

  (** val store : memory_chunk -> mem -> block -> z -> val0 -> mem option **)

  let store chunk m b ofs v =
    if valid_access_dec m chunk b ofs Writable
    then Some { mem_contents =
           (PMap.set b
             (setN (encode_val chunk v) ofs (PMap.get b m.mem_contents))
             m.mem_contents);
           mem_access = m.mem_access; nextblock = m.nextblock }
    else None

  (** val storev : memory_chunk -> mem -> val0 -> val0 -> mem option **)

  let storev chunk m addr v =
    match addr with
    | Vptr (b, ofs) -> store chunk m b (Ptrofs.unsigned ofs) v
    | _ -> None
 end

module Genv =
 struct
  type ('f, 'v) t = { genv_public : ident list; genv_symb : block PTree.t;
                      genv_defs : ('f, 'v) globdef PTree.t; genv_next : 
                      block }

  (** val empty_genv : ident list -> ('a1, 'a2) t **)

  let empty_genv pub =
    { genv_public = pub; genv_symb = PTree.empty; genv_defs = PTree.empty;
      genv_next = XH }
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

(** val noattr : attr **)

let noattr =
  { attr_volatile = false; attr_alignas = None }

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

(** val intsize_eq : intsize -> intsize -> bool **)

let intsize_eq s1 s2 =
  match s1 with
  | I8 -> (match s2 with
           | I8 -> true
           | _ -> false)
  | I16 -> (match s2 with
            | I16 -> true
            | _ -> false)
  | I32 -> (match s2 with
            | I32 -> true
            | _ -> false)
  | IBool -> (match s2 with
              | IBool -> true
              | _ -> false)

(** val signedness_eq : signedness -> signedness -> bool **)

let signedness_eq s1 s2 =
  match s1 with
  | Signed -> (match s2 with
               | Signed -> true
               | Unsigned -> false)
  | Unsigned -> (match s2 with
                 | Signed -> false
                 | Unsigned -> true)

(** val floatsize_eq : floatsize -> floatsize -> bool **)

let floatsize_eq s1 s2 =
  match s1 with
  | F32 -> (match s2 with
            | F32 -> true
            | F64 -> false)
  | F64 -> (match s2 with
            | F32 -> false
            | F64 -> true)

(** val attr_eq : attr -> attr -> bool **)

let attr_eq a1 a2 =
  let { attr_volatile = attr_volatile0; attr_alignas = attr_alignas0 } = a1 in
  let { attr_volatile = attr_volatile1; attr_alignas = attr_alignas1 } = a2 in
  if bool_dec attr_volatile0 attr_volatile1
  then (match attr_alignas0 with
        | Some a ->
          (match attr_alignas1 with
           | Some n1 -> Coq_N.eq_dec a n1
           | None -> false)
        | None -> (match attr_alignas1 with
                   | Some _ -> false
                   | None -> true))
  else false

(** val type_eq : type0 -> type0 -> bool **)

let rec type_eq ty1 ty2 =
  match ty1 with
  | Tvoid -> (match ty2 with
              | Tvoid -> true
              | _ -> false)
  | Tint0 (i0, s, a) ->
    (match ty2 with
     | Tint0 (i1, s0, a0) ->
       if intsize_eq i0 i1
       then if signedness_eq s s0 then attr_eq a a0 else false
       else false
     | _ -> false)
  | Tlong0 (s, a) ->
    (match ty2 with
     | Tlong0 (s0, a0) -> if signedness_eq s s0 then attr_eq a a0 else false
     | _ -> false)
  | Tfloat0 (f, a) ->
    (match ty2 with
     | Tfloat0 (f0, a0) -> if floatsize_eq f f0 then attr_eq a a0 else false
     | _ -> false)
  | Tpointer (t0, a) ->
    (match ty2 with
     | Tpointer (t1, a0) -> if type_eq t0 t1 then attr_eq a a0 else false
     | _ -> false)
  | Tarray (t0, z0, a) ->
    (match ty2 with
     | Tarray (t1, z1, a0) ->
       if type_eq t0 t1
       then if zeq z0 z1 then attr_eq a a0 else false
       else false
     | _ -> false)
  | Tfunction (l, t0, c) ->
    (match ty2 with
     | Tfunction (l0, t1, c0) ->
       if list_eq_dec type_eq l l0
       then if type_eq t0 t1 then calling_convention_eq c c0 else false
       else false
     | _ -> false)
  | Tstruct (i0, a) ->
    (match ty2 with
     | Tstruct (i1, a0) -> if ident_eq i0 i1 then attr_eq a a0 else false
     | _ -> false)
  | Tunion (i0, a) ->
    (match ty2 with
     | Tunion (i1, a0) -> if ident_eq i0 i1 then attr_eq a a0 else false
     | _ -> false)

(** val change_attributes : (attr -> attr) -> type0 -> type0 **)

let change_attributes f ty = match ty with
| Tint0 (sz, si, a) -> Tint0 (sz, si, (f a))
| Tlong0 (si, a) -> Tlong0 (si, (f a))
| Tfloat0 (sz, a) -> Tfloat0 (sz, (f a))
| Tpointer (elt0, a) -> Tpointer (elt0, (f a))
| Tarray (elt0, sz, a) -> Tarray (elt0, sz, (f a))
| Tstruct (id, a) -> Tstruct (id, (f a))
| Tunion (id, a) -> Tunion (id, (f a))
| _ -> ty

(** val remove_attributes : type0 -> type0 **)

let remove_attributes ty =
  change_attributes (fun _ -> noattr) ty

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

(** val typeconv : type0 -> type0 **)

let typeconv ty = match ty with
| Tint0 (i0, _, _) ->
  (match i0 with
   | I32 -> remove_attributes ty
   | _ -> Tint0 (I32, Signed, noattr))
| Tarray (t0, _, _) -> Tpointer (t0, noattr)
| Tfunction (_, _, _) -> Tpointer (ty, noattr)
| _ -> remove_attributes ty

(** val sizeof : composite_env -> type0 -> z **)

let rec sizeof env = function
| Tint0 (i0, _, _) ->
  (match i0 with
   | I16 -> Zpos (XO XH)
   | I32 -> Zpos (XO (XO XH))
   | _ -> Zpos XH)
| Tlong0 (_, _) -> Zpos (XO (XO (XO XH)))
| Tfloat0 (f, _) ->
  (match f with
   | F32 -> Zpos (XO (XO XH))
   | F64 -> Zpos (XO (XO (XO XH))))
| Tpointer (_, _) ->
  if ptr64 then Zpos (XO (XO (XO XH))) else Zpos (XO (XO XH))
| Tarray (t', n1, _) -> Coq_Z.mul (sizeof env t') (Coq_Z.max Z0 n1)
| Tstruct (id, _) ->
  (match PTree.get id env with
   | Some co -> co.co_sizeof
   | None -> Z0)
| Tunion (id, _) ->
  (match PTree.get id env with
   | Some co -> co.co_sizeof
   | None -> Z0)
| _ -> Zpos XH

type mode0 =
| By_value of memory_chunk
| By_reference
| By_copy
| By_nothing

(** val access_mode : type0 -> mode0 **)

let access_mode = function
| Tvoid -> By_nothing
| Tint0 (i0, s, _) ->
  (match i0 with
   | I8 ->
     (match s with
      | Signed -> By_value Mint8signed
      | Unsigned -> By_value Mint8unsigned)
   | I16 ->
     (match s with
      | Signed -> By_value Mint16signed
      | Unsigned -> By_value Mint16unsigned)
   | I32 -> By_value Mint32
   | IBool -> By_value Mbool)
| Tlong0 (_, _) -> By_value Mint64
| Tfloat0 (f, _) ->
  (match f with
   | F32 -> By_value Mfloat32
   | F64 -> By_value Mfloat64)
| Tpointer (_, _) -> By_value mptr
| Tarray (_, _, _) -> By_reference
| Tfunction (_, _, _) -> By_reference
| _ -> By_copy

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

(** val classify_cast : type0 -> type0 -> classify_cast_cases **)

let classify_cast tfrom = function
| Tvoid -> Cast_case_void
| Tint0 (sz2, si2, _) ->
  (match tfrom with
   | Tvoid -> Cast_case_default
   | Tint0 (_, _, _) ->
     (match sz2 with
      | I32 -> if ptr64 then Cast_case_i2i (sz2, si2) else Cast_case_pointer
      | IBool -> Cast_case_i2bool
      | _ -> Cast_case_i2i (sz2, si2))
   | Tlong0 (_, _) ->
     if intsize_eq sz2 IBool
     then Cast_case_l2bool
     else Cast_case_l2i (sz2, si2)
   | Tfloat0 (f, _) ->
     (match f with
      | F32 ->
        if intsize_eq sz2 IBool
        then Cast_case_s2bool
        else Cast_case_s2i (sz2, si2)
      | F64 ->
        if intsize_eq sz2 IBool
        then Cast_case_f2bool
        else Cast_case_f2i (sz2, si2))
   | Tstruct (_, _) -> Cast_case_default
   | Tunion (_, _) -> Cast_case_default
   | _ ->
     if ptr64
     then if intsize_eq sz2 IBool
          then Cast_case_l2bool
          else Cast_case_l2i (sz2, si2)
     else (match sz2 with
           | I32 -> Cast_case_pointer
           | IBool -> Cast_case_i2bool
           | _ -> Cast_case_i2i (sz2, si2)))
| Tlong0 (si2, _) ->
  (match tfrom with
   | Tvoid -> Cast_case_default
   | Tint0 (_, si1, _) -> Cast_case_i2l si1
   | Tlong0 (_, _) -> if ptr64 then Cast_case_pointer else Cast_case_l2l
   | Tfloat0 (f, _) ->
     (match f with
      | F32 -> Cast_case_s2l si2
      | F64 -> Cast_case_f2l si2)
   | Tstruct (_, _) -> Cast_case_default
   | Tunion (_, _) -> Cast_case_default
   | _ -> if ptr64 then Cast_case_pointer else Cast_case_i2l si2)
| Tfloat0 (f, _) ->
  (match f with
   | F32 ->
     (match tfrom with
      | Tint0 (_, si1, _) -> Cast_case_i2s si1
      | Tlong0 (si1, _) -> Cast_case_l2s si1
      | Tfloat0 (f0, _) ->
        (match f0 with
         | F32 -> Cast_case_s2s
         | F64 -> Cast_case_f2s)
      | _ -> Cast_case_default)
   | F64 ->
     (match tfrom with
      | Tint0 (_, si1, _) -> Cast_case_i2f si1
      | Tlong0 (si1, _) -> Cast_case_l2f si1
      | Tfloat0 (f0, _) ->
        (match f0 with
         | F32 -> Cast_case_s2f
         | F64 -> Cast_case_f2f)
      | _ -> Cast_case_default))
| Tpointer (_, _) ->
  (match tfrom with
   | Tint0 (_, si, _) -> if ptr64 then Cast_case_i2l si else Cast_case_pointer
   | Tlong0 (_, _) ->
     if ptr64 then Cast_case_pointer else Cast_case_l2i (I32, Unsigned)
   | Tpointer (_, _) -> Cast_case_pointer
   | Tarray (_, _, _) -> Cast_case_pointer
   | Tfunction (_, _, _) -> Cast_case_pointer
   | _ -> Cast_case_default)
| Tstruct (id2, _) ->
  (match tfrom with
   | Tstruct (id1, _) -> Cast_case_struct (id1, id2)
   | _ -> Cast_case_default)
| Tunion (id2, _) ->
  (match tfrom with
   | Tunion (id1, _) -> Cast_case_union (id1, id2)
   | _ -> Cast_case_default)
| _ -> Cast_case_default

(** val cast_int_int : intsize -> signedness -> Int.int -> Int.int **)

let cast_int_int sz sg i0 =
  match sz with
  | I8 ->
    (match sg with
     | Signed -> Int.sign_ext (Zpos (XO (XO (XO XH)))) i0
     | Unsigned -> Int.zero_ext (Zpos (XO (XO (XO XH)))) i0)
  | I16 ->
    (match sg with
     | Signed -> Int.sign_ext (Zpos (XO (XO (XO (XO XH))))) i0
     | Unsigned -> Int.zero_ext (Zpos (XO (XO (XO (XO XH))))) i0)
  | I32 -> i0
  | IBool -> if Int.eq i0 Int.zero then Int.zero else Int.one

(** val cast_int_float : signedness -> Int.int -> float **)

let cast_int_float si i0 =
  match si with
  | Signed -> Float.of_int i0
  | Unsigned -> Float.of_intu i0

(** val cast_float_int : signedness -> float -> Int.int option **)

let cast_float_int si f =
  match si with
  | Signed -> Float.to_int f
  | Unsigned -> Float.to_intu f

(** val cast_int_single : signedness -> Int.int -> float32 **)

let cast_int_single si i0 =
  match si with
  | Signed -> Float32.of_int i0
  | Unsigned -> Float32.of_intu i0

(** val cast_single_int : signedness -> float32 -> Int.int option **)

let cast_single_int si f =
  match si with
  | Signed -> Float32.to_int f
  | Unsigned -> Float32.to_intu f

(** val cast_int_long : signedness -> Int.int -> Int64.int **)

let cast_int_long si i0 =
  match si with
  | Signed -> Int64.repr (Int.signed i0)
  | Unsigned -> Int64.repr (Int.unsigned i0)

(** val cast_long_float : signedness -> Int64.int -> float **)

let cast_long_float si i0 =
  match si with
  | Signed -> Float.of_long i0
  | Unsigned -> Float.of_longu i0

(** val cast_long_single : signedness -> Int64.int -> float32 **)

let cast_long_single si i0 =
  match si with
  | Signed -> Float32.of_long i0
  | Unsigned -> Float32.of_longu i0

(** val cast_float_long : signedness -> float -> Int64.int option **)

let cast_float_long si f =
  match si with
  | Signed -> Float.to_long f
  | Unsigned -> Float.to_longu f

(** val cast_single_long : signedness -> float32 -> Int64.int option **)

let cast_single_long si f =
  match si with
  | Signed -> Float32.to_long f
  | Unsigned -> Float32.to_longu f

(** val sem_cast : val0 -> type0 -> type0 -> Mem.mem -> val0 option **)

let sem_cast v t1 t2 m =
  match classify_cast t1 t2 with
  | Cast_case_pointer ->
    (match v with
     | Vint _ -> if ptr64 then None else Some v
     | Vlong _ -> if ptr64 then Some v else None
     | Vptr (_, _) -> Some v
     | _ -> None)
  | Cast_case_i2i (sz2, si2) ->
    (match v with
     | Vint i0 -> Some (Vint (cast_int_int sz2 si2 i0))
     | _ -> None)
  | Cast_case_f2f -> (match v with
                      | Vfloat f -> Some (Vfloat f)
                      | _ -> None)
  | Cast_case_s2s -> (match v with
                      | Vsingle f -> Some (Vsingle f)
                      | _ -> None)
  | Cast_case_f2s ->
    (match v with
     | Vfloat f -> Some (Vsingle (Float.to_single f))
     | _ -> None)
  | Cast_case_s2f ->
    (match v with
     | Vsingle f -> Some (Vfloat (Float.of_single f))
     | _ -> None)
  | Cast_case_i2f si1 ->
    (match v with
     | Vint i0 -> Some (Vfloat (cast_int_float si1 i0))
     | _ -> None)
  | Cast_case_i2s si1 ->
    (match v with
     | Vint i0 -> Some (Vsingle (cast_int_single si1 i0))
     | _ -> None)
  | Cast_case_f2i (sz2, si2) ->
    (match v with
     | Vfloat f ->
       (match cast_float_int si2 f with
        | Some i0 -> Some (Vint (cast_int_int sz2 si2 i0))
        | None -> None)
     | _ -> None)
  | Cast_case_s2i (sz2, si2) ->
    (match v with
     | Vsingle f ->
       (match cast_single_int si2 f with
        | Some i0 -> Some (Vint (cast_int_int sz2 si2 i0))
        | None -> None)
     | _ -> None)
  | Cast_case_l2l -> (match v with
                      | Vlong n1 -> Some (Vlong n1)
                      | _ -> None)
  | Cast_case_i2l si ->
    (match v with
     | Vint n1 -> Some (Vlong (cast_int_long si n1))
     | _ -> None)
  | Cast_case_l2i (sz, si) ->
    (match v with
     | Vlong n1 ->
       Some (Vint (cast_int_int sz si (Int.repr (Int64.unsigned n1))))
     | _ -> None)
  | Cast_case_l2f si1 ->
    (match v with
     | Vlong i0 -> Some (Vfloat (cast_long_float si1 i0))
     | _ -> None)
  | Cast_case_l2s si1 ->
    (match v with
     | Vlong i0 -> Some (Vsingle (cast_long_single si1 i0))
     | _ -> None)
  | Cast_case_f2l si2 ->
    (match v with
     | Vfloat f ->
       (match cast_float_long si2 f with
        | Some i0 -> Some (Vlong i0)
        | None -> None)
     | _ -> None)
  | Cast_case_s2l si2 ->
    (match v with
     | Vsingle f ->
       (match cast_single_long si2 f with
        | Some i0 -> Some (Vlong i0)
        | None -> None)
     | _ -> None)
  | Cast_case_i2bool ->
    (match v with
     | Vint n1 ->
       Some (Vint (if Int.eq n1 Int.zero then Int.zero else Int.one))
     | Vptr (b, ofs) ->
       if ptr64
       then None
       else if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs)
            then Some vone
            else None
     | _ -> None)
  | Cast_case_l2bool ->
    (match v with
     | Vlong n1 ->
       Some (Vint (if Int64.eq n1 Int64.zero then Int.zero else Int.one))
     | Vptr (b, ofs) ->
       if negb ptr64
       then None
       else if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs)
            then Some vone
            else None
     | _ -> None)
  | Cast_case_f2bool ->
    (match v with
     | Vfloat f ->
       Some (Vint (if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
     | _ -> None)
  | Cast_case_s2bool ->
    (match v with
     | Vsingle f ->
       Some (Vint
         (if Float32.cmp Ceq f Float32.zero then Int.zero else Int.one))
     | _ -> None)
  | Cast_case_struct (id1, id2) ->
    (match v with
     | Vptr (_, _) -> if ident_eq id1 id2 then Some v else None
     | _ -> None)
  | Cast_case_union (id1, id2) ->
    (match v with
     | Vptr (_, _) -> if ident_eq id1 id2 then Some v else None
     | _ -> None)
  | Cast_case_void -> Some v
  | Cast_case_default -> None

type classify_bool_cases =
| Bool_case_i
| Bool_case_l
| Bool_case_f
| Bool_case_s
| Bool_default

(** val classify_bool : type0 -> classify_bool_cases **)

let classify_bool ty =
  match typeconv ty with
  | Tint0 (_, _, _) -> Bool_case_i
  | Tlong0 (_, _) -> Bool_case_l
  | Tfloat0 (f, _) -> (match f with
                       | F32 -> Bool_case_s
                       | F64 -> Bool_case_f)
  | Tpointer (_, _) -> if ptr64 then Bool_case_l else Bool_case_i
  | _ -> Bool_default

(** val bool_val : val0 -> type0 -> Mem.mem -> bool option **)

let bool_val v t0 m =
  match classify_bool t0 with
  | Bool_case_i ->
    (match v with
     | Vint n1 -> Some (negb (Int.eq n1 Int.zero))
     | Vptr (b, ofs) ->
       if ptr64
       then None
       else if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs)
            then Some true
            else None
     | _ -> None)
  | Bool_case_l ->
    (match v with
     | Vlong n1 -> Some (negb (Int64.eq n1 Int64.zero))
     | Vptr (b, ofs) ->
       if negb ptr64
       then None
       else if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs)
            then Some true
            else None
     | _ -> None)
  | Bool_case_f ->
    (match v with
     | Vfloat f -> Some (negb (Float.cmp Ceq f Float.zero))
     | _ -> None)
  | Bool_case_s ->
    (match v with
     | Vsingle f -> Some (negb (Float32.cmp Ceq f Float32.zero))
     | _ -> None)
  | Bool_default -> None

type binarith_cases =
| Bin_case_i of signedness
| Bin_case_l of signedness
| Bin_case_f
| Bin_case_s
| Bin_default

(** val classify_binarith : type0 -> type0 -> binarith_cases **)

let classify_binarith ty1 ty2 =
  match ty1 with
  | Tint0 (i0, s, _) ->
    (match i0 with
     | I32 ->
       (match s with
        | Signed ->
          (match ty2 with
           | Tint0 (i1, s0, _) ->
             (match i1 with
              | I32 -> Bin_case_i s0
              | _ -> Bin_case_i Signed)
           | Tlong0 (sg, _) -> Bin_case_l sg
           | Tfloat0 (f, _) ->
             (match f with
              | F32 -> Bin_case_s
              | F64 -> Bin_case_f)
           | _ -> Bin_default)
        | Unsigned ->
          (match ty2 with
           | Tint0 (_, _, _) -> Bin_case_i Unsigned
           | Tlong0 (sg, _) -> Bin_case_l sg
           | Tfloat0 (f, _) ->
             (match f with
              | F32 -> Bin_case_s
              | F64 -> Bin_case_f)
           | _ -> Bin_default))
     | _ ->
       (match ty2 with
        | Tint0 (i1, s0, _) ->
          (match i1 with
           | I32 -> Bin_case_i s0
           | _ -> Bin_case_i Signed)
        | Tlong0 (sg, _) -> Bin_case_l sg
        | Tfloat0 (f, _) ->
          (match f with
           | F32 -> Bin_case_s
           | F64 -> Bin_case_f)
        | _ -> Bin_default))
  | Tlong0 (sg, _) ->
    (match sg with
     | Signed ->
       (match ty2 with
        | Tint0 (_, _, _) -> Bin_case_l sg
        | Tlong0 (s, _) -> Bin_case_l s
        | Tfloat0 (f, _) ->
          (match f with
           | F32 -> Bin_case_s
           | F64 -> Bin_case_f)
        | _ -> Bin_default)
     | Unsigned ->
       (match ty2 with
        | Tint0 (_, _, _) -> Bin_case_l sg
        | Tlong0 (_, _) -> Bin_case_l Unsigned
        | Tfloat0 (f, _) ->
          (match f with
           | F32 -> Bin_case_s
           | F64 -> Bin_case_f)
        | _ -> Bin_default))
  | Tfloat0 (f, _) ->
    (match f with
     | F32 ->
       (match ty2 with
        | Tint0 (_, _, _) -> Bin_case_s
        | Tlong0 (_, _) -> Bin_case_s
        | Tfloat0 (f0, _) ->
          (match f0 with
           | F32 -> Bin_case_s
           | F64 -> Bin_case_f)
        | _ -> Bin_default)
     | F64 ->
       (match ty2 with
        | Tint0 (_, _, _) -> Bin_case_f
        | Tlong0 (_, _) -> Bin_case_f
        | Tfloat0 (_, _) -> Bin_case_f
        | _ -> Bin_default))
  | _ -> Bin_default

(** val binarith_type : binarith_cases -> type0 **)

let binarith_type = function
| Bin_case_i sg -> Tint0 (I32, sg, noattr)
| Bin_case_l sg -> Tlong0 (sg, noattr)
| Bin_case_f -> Tfloat0 (F64, noattr)
| Bin_case_s -> Tfloat0 (F32, noattr)
| Bin_default -> Tvoid

(** val sem_binarith :
    (signedness -> Int.int -> Int.int -> val0 option) -> (signedness ->
    Int64.int -> Int64.int -> val0 option) -> (float -> float -> val0 option)
    -> (float32 -> float32 -> val0 option) -> val0 -> type0 -> val0 -> type0
    -> Mem.mem -> val0 option **)

let sem_binarith sem_int sem_long sem_float sem_single v1 t1 v2 t2 m =
  let c = classify_binarith t1 t2 in
  let t0 = binarith_type c in
  (match sem_cast v1 t1 t0 m with
   | Some v1' ->
     (match sem_cast v2 t2 t0 m with
      | Some v2' ->
        (match c with
         | Bin_case_i sg ->
           (match v1' with
            | Vint n1 ->
              (match v2' with
               | Vint n2 -> sem_int sg n1 n2
               | _ -> None)
            | _ -> None)
         | Bin_case_l sg ->
           (match v1' with
            | Vlong n1 ->
              (match v2' with
               | Vlong n2 -> sem_long sg n1 n2
               | _ -> None)
            | _ -> None)
         | Bin_case_f ->
           (match v1' with
            | Vfloat n1 ->
              (match v2' with
               | Vfloat n2 -> sem_float n1 n2
               | _ -> None)
            | _ -> None)
         | Bin_case_s ->
           (match v1' with
            | Vsingle n1 ->
              (match v2' with
               | Vsingle n2 -> sem_single n1 n2
               | _ -> None)
            | _ -> None)
         | Bin_default -> None)
      | None -> None)
   | None -> None)

type classify_add_cases =
| Add_case_pi of type0 * signedness
| Add_case_pl of type0
| Add_case_ip of signedness * type0
| Add_case_lp of type0
| Add_default

(** val classify_add : type0 -> type0 -> classify_add_cases **)

let classify_add ty1 ty2 =
  match typeconv ty1 with
  | Tint0 (_, si, _) ->
    (match typeconv ty2 with
     | Tpointer (ty, _) -> Add_case_ip (si, ty)
     | _ -> Add_default)
  | Tlong0 (_, _) ->
    (match typeconv ty2 with
     | Tpointer (ty, _) -> Add_case_lp ty
     | _ -> Add_default)
  | Tpointer (ty, _) ->
    (match typeconv ty2 with
     | Tint0 (_, si, _) -> Add_case_pi (ty, si)
     | Tlong0 (_, _) -> Add_case_pl ty
     | _ -> Add_default)
  | _ -> Add_default

(** val ptrofs_of_int : signedness -> Int.int -> Ptrofs.int **)

let ptrofs_of_int si n1 =
  match si with
  | Signed -> Ptrofs.of_ints n1
  | Unsigned -> Ptrofs.of_intu n1

(** val sem_add_ptr_int :
    composite_env -> type0 -> signedness -> val0 -> val0 -> val0 option **)

let sem_add_ptr_int cenv ty si v1 v2 =
  match v1 with
  | Vint n1 ->
    (match v2 with
     | Vint n2 ->
       if ptr64
       then None
       else Some (Vint (Int.add n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
     | _ -> None)
  | Vlong n1 ->
    (match v2 with
     | Vint n2 ->
       let n3 = cast_int_long si n2 in
       if ptr64
       then Some (Vlong
              (Int64.add n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n3)))
       else None
     | _ -> None)
  | Vptr (b1, ofs1) ->
    (match v2 with
     | Vint n2 ->
       let n3 = ptrofs_of_int si n2 in
       Some (Vptr (b1,
       (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n3))))
     | _ -> None)
  | _ -> None

(** val sem_add_ptr_long :
    composite_env -> type0 -> val0 -> val0 -> val0 option **)

let sem_add_ptr_long cenv ty v1 v2 =
  match v1 with
  | Vint n1 ->
    (match v2 with
     | Vlong n2 ->
       let n3 = Int.repr (Int64.unsigned n2) in
       if ptr64
       then None
       else Some (Vint (Int.add n1 (Int.mul (Int.repr (sizeof cenv ty)) n3)))
     | _ -> None)
  | Vlong n1 ->
    (match v2 with
     | Vlong n2 ->
       if ptr64
       then Some (Vlong
              (Int64.add n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2)))
       else None
     | _ -> None)
  | Vptr (b1, ofs1) ->
    (match v2 with
     | Vlong n2 ->
       let n3 = Ptrofs.of_int64 n2 in
       Some (Vptr (b1,
       (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n3))))
     | _ -> None)
  | _ -> None

(** val sem_add :
    composite_env -> val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option **)

let sem_add cenv v1 t1 v2 t2 m =
  match classify_add t1 t2 with
  | Add_case_pi (ty, si) -> sem_add_ptr_int cenv ty si v1 v2
  | Add_case_pl ty -> sem_add_ptr_long cenv ty v1 v2
  | Add_case_ip (si, ty) -> sem_add_ptr_int cenv ty si v2 v1
  | Add_case_lp ty -> sem_add_ptr_long cenv ty v2 v1
  | Add_default ->
    sem_binarith (fun _ n1 n2 -> Some (Vint (Int.add n1 n2))) (fun _ n1 n2 ->
      Some (Vlong (Int64.add n1 n2))) (fun n1 n2 -> Some (Vfloat
      (Float.add n1 n2))) (fun n1 n2 -> Some (Vsingle (Float32.add n1 n2)))
      v1 t1 v2 t2 m

type classify_sub_cases =
| Sub_case_pi of type0 * signedness
| Sub_case_pp of type0
| Sub_case_pl of type0
| Sub_default

(** val classify_sub : type0 -> type0 -> classify_sub_cases **)

let classify_sub ty1 ty2 =
  match typeconv ty1 with
  | Tpointer (ty, _) ->
    (match typeconv ty2 with
     | Tint0 (_, si, _) -> Sub_case_pi (ty, si)
     | Tlong0 (_, _) -> Sub_case_pl ty
     | Tpointer (_, _) -> Sub_case_pp ty
     | _ -> Sub_default)
  | _ -> Sub_default

(** val sem_sub :
    composite_env -> val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option **)

let sem_sub cenv v1 t1 v2 t2 m =
  match classify_sub t1 t2 with
  | Sub_case_pi (ty, si) ->
    (match v1 with
     | Vint n1 ->
       (match v2 with
        | Vint n2 ->
          if ptr64
          then None
          else Some (Vint
                 (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
        | _ -> None)
     | Vlong n1 ->
       (match v2 with
        | Vint n2 ->
          let n3 = cast_int_long si n2 in
          if ptr64
          then Some (Vlong
                 (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n3)))
          else None
        | _ -> None)
     | Vptr (b1, ofs1) ->
       (match v2 with
        | Vint n2 ->
          let n3 = ptrofs_of_int si n2 in
          Some (Vptr (b1,
          (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n3))))
        | _ -> None)
     | _ -> None)
  | Sub_case_pp ty ->
    (match v1 with
     | Vptr (b1, ofs1) ->
       (match v2 with
        | Vptr (b2, ofs2) ->
          if eq_block b1 b2
          then let sz = sizeof cenv ty in
               if (&&) (proj_sumbool (zlt Z0 sz))
                    (proj_sumbool (zle sz Ptrofs.max_signed))
               then Some
                      (vptrofs
                        (Ptrofs.divs (Ptrofs.sub ofs1 ofs2) (Ptrofs.repr sz)))
               else None
          else None
        | _ -> None)
     | _ -> None)
  | Sub_case_pl ty ->
    (match v1 with
     | Vint n1 ->
       (match v2 with
        | Vlong n2 ->
          let n3 = Int.repr (Int64.unsigned n2) in
          if ptr64
          then None
          else Some (Vint
                 (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n3)))
        | _ -> None)
     | Vlong n1 ->
       (match v2 with
        | Vlong n2 ->
          if ptr64
          then Some (Vlong
                 (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2)))
          else None
        | _ -> None)
     | Vptr (b1, ofs1) ->
       (match v2 with
        | Vlong n2 ->
          let n3 = Ptrofs.of_int64 n2 in
          Some (Vptr (b1,
          (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n3))))
        | _ -> None)
     | _ -> None)
  | Sub_default ->
    sem_binarith (fun _ n1 n2 -> Some (Vint (Int.sub n1 n2))) (fun _ n1 n2 ->
      Some (Vlong (Int64.sub n1 n2))) (fun n1 n2 -> Some (Vfloat
      (Float.sub n1 n2))) (fun n1 n2 -> Some (Vsingle (Float32.sub n1 n2)))
      v1 t1 v2 t2 m

(** val sem_mul : val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option **)

let sem_mul v1 t1 v2 t2 m =
  sem_binarith (fun _ n1 n2 -> Some (Vint (Int.mul n1 n2))) (fun _ n1 n2 ->
    Some (Vlong (Int64.mul n1 n2))) (fun n1 n2 -> Some (Vfloat
    (Float.mul n1 n2))) (fun n1 n2 -> Some (Vsingle (Float32.mul n1 n2))) v1
    t1 v2 t2 m

(** val sem_div : val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option **)

let sem_div v1 t1 v2 t2 m =
  sem_binarith (fun sg n1 n2 ->
    match sg with
    | Signed ->
      if (||) (Int.eq n2 Int.zero)
           ((&&) (Int.eq n1 (Int.repr Int.min_signed)) (Int.eq n2 Int.mone))
      then None
      else Some (Vint (Int.divs n1 n2))
    | Unsigned ->
      if Int.eq n2 Int.zero then None else Some (Vint (Int.divu n1 n2)))
    (fun sg n1 n2 ->
    match sg with
    | Signed ->
      if (||) (Int64.eq n2 Int64.zero)
           ((&&) (Int64.eq n1 (Int64.repr Int64.min_signed))
             (Int64.eq n2 Int64.mone))
      then None
      else Some (Vlong (Int64.divs n1 n2))
    | Unsigned ->
      if Int64.eq n2 Int64.zero then None else Some (Vlong (Int64.divu n1 n2)))
    (fun n1 n2 -> Some (Vfloat (Float.div n1 n2))) (fun n1 n2 -> Some
    (Vsingle (Float32.div n1 n2))) v1 t1 v2 t2 m

(** val sem_mod : val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option **)

let sem_mod v1 t1 v2 t2 m =
  sem_binarith (fun sg n1 n2 ->
    match sg with
    | Signed ->
      if (||) (Int.eq n2 Int.zero)
           ((&&) (Int.eq n1 (Int.repr Int.min_signed)) (Int.eq n2 Int.mone))
      then None
      else Some (Vint (Int.mods n1 n2))
    | Unsigned ->
      if Int.eq n2 Int.zero then None else Some (Vint (Int.modu n1 n2)))
    (fun sg n1 n2 ->
    match sg with
    | Signed ->
      if (||) (Int64.eq n2 Int64.zero)
           ((&&) (Int64.eq n1 (Int64.repr Int64.min_signed))
             (Int64.eq n2 Int64.mone))
      then None
      else Some (Vlong (Int64.mods n1 n2))
    | Unsigned ->
      if Int64.eq n2 Int64.zero then None else Some (Vlong (Int64.modu n1 n2)))
    (fun _ _ -> None) (fun _ _ -> None) v1 t1 v2 t2 m

(** val sem_and : val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option **)

let sem_and v1 t1 v2 t2 m =
  sem_binarith (fun _ n1 n2 -> Some (Vint (Int.coq_and n1 n2)))
    (fun _ n1 n2 -> Some (Vlong (Int64.coq_and n1 n2))) (fun _ _ -> None)
    (fun _ _ -> None) v1 t1 v2 t2 m

(** val sem_or : val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option **)

let sem_or v1 t1 v2 t2 m =
  sem_binarith (fun _ n1 n2 -> Some (Vint (Int.coq_or n1 n2)))
    (fun _ n1 n2 -> Some (Vlong (Int64.coq_or n1 n2))) (fun _ _ -> None)
    (fun _ _ -> None) v1 t1 v2 t2 m

(** val sem_xor : val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option **)

let sem_xor v1 t1 v2 t2 m =
  sem_binarith (fun _ n1 n2 -> Some (Vint (Int.xor n1 n2))) (fun _ n1 n2 ->
    Some (Vlong (Int64.xor n1 n2))) (fun _ _ -> None) (fun _ _ -> None) v1 t1
    v2 t2 m

type classify_shift_cases =
| Shift_case_ii of signedness
| Shift_case_ll of signedness
| Shift_case_il of signedness
| Shift_case_li of signedness
| Shift_default

(** val classify_shift : type0 -> type0 -> classify_shift_cases **)

let classify_shift ty1 ty2 =
  match typeconv ty1 with
  | Tint0 (i0, s, _) ->
    (match i0 with
     | I32 ->
       (match typeconv ty2 with
        | Tint0 (_, _, _) -> Shift_case_ii s
        | Tlong0 (_, _) -> Shift_case_il s
        | _ -> Shift_default)
     | _ ->
       (match typeconv ty2 with
        | Tint0 (_, _, _) -> Shift_case_ii Signed
        | Tlong0 (_, _) -> Shift_case_il Signed
        | _ -> Shift_default))
  | Tlong0 (s, _) ->
    (match typeconv ty2 with
     | Tint0 (_, _, _) -> Shift_case_li s
     | Tlong0 (_, _) -> Shift_case_ll s
     | _ -> Shift_default)
  | _ -> Shift_default

(** val sem_shift :
    (signedness -> Int.int -> Int.int -> Int.int) -> (signedness -> Int64.int
    -> Int64.int -> Int64.int) -> val0 -> type0 -> val0 -> type0 -> val0
    option **)

let sem_shift sem_int sem_long v1 t1 v2 t2 =
  match classify_shift t1 t2 with
  | Shift_case_ii sg ->
    (match v1 with
     | Vint n1 ->
       (match v2 with
        | Vint n2 ->
          if Int.ltu n2 Int.iwordsize
          then Some (Vint (sem_int sg n1 n2))
          else None
        | _ -> None)
     | _ -> None)
  | Shift_case_ll sg ->
    (match v1 with
     | Vlong n1 ->
       (match v2 with
        | Vlong n2 ->
          if Int64.ltu n2 Int64.iwordsize
          then Some (Vlong (sem_long sg n1 n2))
          else None
        | _ -> None)
     | _ -> None)
  | Shift_case_il sg ->
    (match v1 with
     | Vint n1 ->
       (match v2 with
        | Vlong n2 ->
          if Int64.ltu n2 (Int64.repr (Zpos (XO (XO (XO (XO (XO XH)))))))
          then Some (Vint (sem_int sg n1 (Int64.loword n2)))
          else None
        | _ -> None)
     | _ -> None)
  | Shift_case_li sg ->
    (match v1 with
     | Vlong n1 ->
       (match v2 with
        | Vint n2 ->
          if Int.ltu n2 Int64.iwordsize'
          then Some (Vlong (sem_long sg n1 (Int64.repr (Int.unsigned n2))))
          else None
        | _ -> None)
     | _ -> None)
  | Shift_default -> None

(** val sem_shl : val0 -> type0 -> val0 -> type0 -> val0 option **)

let sem_shl v1 t1 v2 t2 =
  sem_shift (fun _ -> Int.shl) (fun _ -> Int64.shl) v1 t1 v2 t2

(** val sem_shr : val0 -> type0 -> val0 -> type0 -> val0 option **)

let sem_shr v1 t1 v2 t2 =
  sem_shift (fun sg n1 n2 ->
    match sg with
    | Signed -> Int.shr n1 n2
    | Unsigned -> Int.shru n1 n2) (fun sg n1 n2 ->
    match sg with
    | Signed -> Int64.shr n1 n2
    | Unsigned -> Int64.shru n1 n2) v1 t1 v2 t2

type classify_cmp_cases =
| Cmp_case_pp
| Cmp_case_pi of signedness
| Cmp_case_ip of signedness
| Cmp_case_pl
| Cmp_case_lp
| Cmp_default

(** val classify_cmp : type0 -> type0 -> classify_cmp_cases **)

let classify_cmp ty1 ty2 =
  match typeconv ty1 with
  | Tint0 (_, si, _) ->
    (match typeconv ty2 with
     | Tpointer (_, _) -> Cmp_case_ip si
     | _ -> Cmp_default)
  | Tlong0 (_, _) ->
    (match typeconv ty2 with
     | Tpointer (_, _) -> Cmp_case_lp
     | _ -> Cmp_default)
  | Tpointer (_, _) ->
    (match typeconv ty2 with
     | Tint0 (_, si, _) -> Cmp_case_pi si
     | Tlong0 (_, _) -> Cmp_case_pl
     | Tpointer (_, _) -> Cmp_case_pp
     | _ -> Cmp_default)
  | _ -> Cmp_default

(** val cmp_ptr : Mem.mem -> comparison0 -> val0 -> val0 -> val0 option **)

let cmp_ptr m c v1 v2 =
  option_map Val.of_bool
    (if ptr64
     then Val.cmplu_bool (Mem.valid_pointer m) c v1 v2
     else Val.cmpu_bool (Mem.valid_pointer m) c v1 v2)

(** val sem_cmp :
    comparison0 -> val0 -> type0 -> val0 -> type0 -> Mem.mem -> val0 option **)

let sem_cmp c v1 t1 v2 t2 m =
  match classify_cmp t1 t2 with
  | Cmp_case_pp -> cmp_ptr m c v1 v2
  | Cmp_case_pi si ->
    (match v2 with
     | Vint n2 ->
       let v2' = vptrofs (ptrofs_of_int si n2) in cmp_ptr m c v1 v2'
     | Vptr (_, _) -> if ptr64 then None else cmp_ptr m c v1 v2
     | _ -> None)
  | Cmp_case_ip si ->
    (match v1 with
     | Vint n1 ->
       let v1' = vptrofs (ptrofs_of_int si n1) in cmp_ptr m c v1' v2
     | Vptr (_, _) -> if ptr64 then None else cmp_ptr m c v1 v2
     | _ -> None)
  | Cmp_case_pl ->
    (match v2 with
     | Vlong n2 ->
       let v2' = vptrofs (Ptrofs.of_int64 n2) in cmp_ptr m c v1 v2'
     | Vptr (_, _) -> if ptr64 then cmp_ptr m c v1 v2 else None
     | _ -> None)
  | Cmp_case_lp ->
    (match v1 with
     | Vlong n1 ->
       let v1' = vptrofs (Ptrofs.of_int64 n1) in cmp_ptr m c v1' v2
     | Vptr (_, _) -> if ptr64 then cmp_ptr m c v1 v2 else None
     | _ -> None)
  | Cmp_default ->
    sem_binarith (fun sg n1 n2 -> Some
      (Val.of_bool
        (match sg with
         | Signed -> Int.cmp c n1 n2
         | Unsigned -> Int.cmpu c n1 n2)))
      (fun sg n1 n2 -> Some
      (Val.of_bool
        (match sg with
         | Signed -> Int64.cmp c n1 n2
         | Unsigned -> Int64.cmpu c n1 n2)))
      (fun n1 n2 -> Some (Val.of_bool (Float.cmp c n1 n2))) (fun n1 n2 ->
      Some (Val.of_bool (Float32.cmp c n1 n2))) v1 t1 v2 t2 m

(** val sem_binary_operation :
    composite_env -> binary_operation -> val0 -> type0 -> val0 -> type0 ->
    Mem.mem -> val0 option **)

let sem_binary_operation cenv op v1 t1 v2 t2 m =
  match op with
  | Oadd -> sem_add cenv v1 t1 v2 t2 m
  | Osub -> sem_sub cenv v1 t1 v2 t2 m
  | Omul -> sem_mul v1 t1 v2 t2 m
  | Odiv -> sem_div v1 t1 v2 t2 m
  | Omod -> sem_mod v1 t1 v2 t2 m
  | Oand -> sem_and v1 t1 v2 t2 m
  | Oor -> sem_or v1 t1 v2 t2 m
  | Oxor -> sem_xor v1 t1 v2 t2 m
  | Oshl -> sem_shl v1 t1 v2 t2
  | Oshr -> sem_shr v1 t1 v2 t2
  | Oeq -> sem_cmp Ceq v1 t1 v2 t2 m
  | One -> sem_cmp Cne v1 t1 v2 t2 m
  | Olt -> sem_cmp Clt v1 t1 v2 t2 m
  | Ogt -> sem_cmp Cgt v1 t1 v2 t2 m
  | Ole -> sem_cmp Cle v1 t1 v2 t2 m
  | Oge -> sem_cmp Cge v1 t1 v2 t2 m

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

(** val typeof : expr -> type0 **)

let typeof = function
| Econst_int (_, ty) -> ty
| Econst_float (_, ty) -> ty
| Econst_single (_, ty) -> ty
| Econst_long (_, ty) -> ty
| Evar (_, ty) -> ty
| Etempvar (_, ty) -> ty
| Ederef (_, ty) -> ty
| Eaddrof (_, ty) -> ty
| Eunop (_, _, ty) -> ty
| Ebinop (_, _, _, ty) -> ty
| Ecast (_, ty) -> ty
| Efield (_, _, ty) -> ty
| Esizeof (_, ty) -> ty
| Ealignof (_, ty) -> ty

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

(** val create_undef_temps : (ident * type0) list -> temp_env **)

let rec create_undef_temps = function
| [] -> PTree.empty
| p :: temps' ->
  let (id, _) = p in PTree.set id Vundef (create_undef_temps temps')

type outcome =
| Out_break
| Out_continue
| Out_normal
| Out_return of (val0 * type0) option

(** val u32 : type0 **)

let u32 =
  Tint0 (I32, Unsigned, noattr)

(** val i32 : type0 **)

let i32 =
  Tint0 (I32, Signed, noattr)

(** val ptr : type0 **)

let ptr =
  Tpointer (u32, noattr)

(** val n0 : ident **)

let n0 =
  XH

(** val data : ident **)

let data =
  XO XH

(** val permutation : ident **)

let permutation =
  XI XH

(** val target : ident **)

let target =
  XO (XO XH)

(** val used : ident **)

let used =
  XI (XO XH)

(** val trace : ident **)

let trace =
  XO (XI XH)

(** val out : ident **)

let out =
  XI (XI XH)

(** val i : ident **)

let i =
  XO (XO (XO XH))

(** val j : ident **)

let j =
  XI (XO (XO XH))

(** val top : ident **)

let top =
  XO (XI (XO XH))

(** val pos : ident **)

let pos =
  XI (XI (XO XH))

(** val tmp : ident **)

let tmp =
  XO (XO (XI XH))

(** val depth : ident **)

let depth =
  XI (XO (XI XH))

(** val lit : z -> expr **)

let lit z0 =
  Econst_int ((Int.repr z0), u32)

(** val reg : ident -> expr **)

let reg v =
  Etempvar (v, u32)

(** val cell : ident -> expr -> expr **)

let cell a index0 =
  Ederef ((Ebinop (Oadd, (Etempvar (a, ptr)), index0, ptr)), u32)

(** val add0 : expr -> expr -> expr **)

let add0 a b =
  Ebinop (Oadd, a, b, u32)

(** val sub0 : expr -> expr -> expr **)

let sub0 a b =
  Ebinop (Osub, a, b, u32)

(** val eq0 : expr -> expr -> expr **)

let eq0 a b =
  Ebinop (Oeq, a, b, i32)

(** val ne : expr -> expr -> expr **)

let ne a b =
  Ebinop (One, a, b, i32)

(** val lt0 : expr -> expr -> expr **)

let lt0 a b =
  Ebinop (Olt, a, b, i32)

(** val gt : expr -> expr -> expr **)

let gt a b =
  Ebinop (Ogt, a, b, i32)

(** val ge : expr -> expr -> expr **)

let ge a b =
  Ebinop (Oge, a, b, i32)

(** val seq : statement list -> statement **)

let seq ss =
  fold_right (fun x x0 -> Ssequence (x, x0)) Sskip ss

(** val set1 : ident -> expr -> statement **)

let set1 v e =
  Sset (v, e)

(** val put : ident -> expr -> expr -> statement **)

let put a index0 value =
  Sassign ((cell a index0), value)

(** val ret : z -> statement **)

let ret z0 =
  Sreturn (Some (lit z0))

(** val when0 : expr -> statement -> statement **)

let when0 c s =
  Sifthenelse (c, s, Sskip)

(** val loop : expr -> statement -> statement **)

let loop c body =
  Sloop ((Ssequence ((Sifthenelse (c, Sskip, Sbreak)), body)), Sskip)

(** val inc : ident -> statement **)

let inc v =
  set1 v (add0 (reg v) (lit (Zpos XH)))

(** val each : ident -> statement -> statement **)

let each v body =
  seq
    ((set1 v (lit Z0)) :: ((loop (lt0 (reg v) (reg n0))
                             (seq (body :: ((inc v) :: [])))) :: []))

(** val check_input : statement **)

let check_input =
  seq
    ((each i (put used (reg i) (lit Z0))) :: ((each i
                                                (seq
                                                  ((set1 j
                                                     (cell permutation
                                                       (reg i))) :: (
                                                  (when0
                                                    (ge (reg j) (reg n0))
                                                    (ret (Zpos (XO XH)))) :: (
                                                  (when0
                                                    (ne (cell used (reg j))
                                                      (lit Z0))
                                                    (ret (Zpos (XO XH)))) :: (
                                                  (put used (reg j)
                                                    (lit (Zpos XH))) :: (
                                                  (put target (reg j)
                                                    (cell data (reg i))) :: []))))))) :: []))

(** val normalize : statement **)

let normalize =
  seq
    ((each i (Sifthenelse ((eq0 (cell data (reg i)) (cell target (reg i))),
       (seq
         ((put permutation (reg i) (reg i)) :: ((put used (reg i)
                                                  (lit (Zpos XH))) :: []))),
       (put used (reg i) (lit Z0))))) :: ((each i
                                            (when0
                                              (ne (cell data (reg i))
                                                (cell target (reg i)))
                                              (seq
                                                ((set1 j (lit Z0)) :: (
                                                (loop (lt0 (reg j) (reg n0))
                                                  (seq
                                                    ((when0
                                                       (eq0
                                                         (cell used (reg j))
                                                         (lit Z0))
                                                       (when0
                                                         (eq0
                                                           (cell data (reg i))
                                                           (cell target
                                                             (reg j)))
                                                         Sbreak)) :: (
                                                    (inc j) :: [])))) :: (
                                                (when0 (eq0 (reg j) (reg n0))
                                                  (ret (Zpos (XO XH)))) :: (
                                                (put permutation (reg i)
                                                  (reg j)) :: ((put used
                                                                 (reg j)
                                                                 (lit (Zpos
                                                                   XH))) :: [])))))))) :: []))

(** val choose_position : statement **)

let choose_position =
  seq
    ((set1 pos (cell permutation (reg top))) :: ((when0
                                                   (eq0 (reg pos) (reg top))
                                                   (seq
                                                     ((loop
                                                        (gt (reg pos)
                                                          (lit Z0))
                                                        (seq
                                                          ((set1 pos
                                                             (sub0 (reg pos)
                                                               (lit (Zpos XH)))) :: (
                                                          (when0
                                                            (ne
                                                              (cell
                                                                permutation
                                                                (reg pos))
                                                              (reg pos))
                                                            Sbreak) :: [])))) :: (
                                                     (when0
                                                       (eq0
                                                         (cell permutation
                                                           (reg pos))
                                                         (reg pos))
                                                       (ret Z0)) :: [])))) :: []))

(** val swap_cells : ident -> statement **)

let swap_cells a =
  seq
    ((set1 tmp (cell a (reg pos))) :: ((put a (reg pos) (cell a (reg top))) :: (
    (put a (reg top) (reg tmp)) :: [])))

(** val exchange : statement **)

let exchange =
  seq
    ((when0 (ne (cell data (reg pos)) (cell data (reg top)))
       (seq
         ((set1 depth (sub0 (reg top) (reg pos))) :: ((when0
                                                        (gt (reg depth)
                                                          (lit (Zpos (XO (XO
                                                            (XO (XO XH)))))))
                                                        (seq
                                                          ((put out
                                                             (lit (Zpos XH))
                                                             (reg pos)) :: (
                                                          (put out
                                                            (lit (Zpos (XO
                                                              XH)))
                                                            (sub0 (reg depth)
                                                              (lit (Zpos (XO
                                                                (XO (XO (XO
                                                                XH)))))))) :: (
                                                          (ret (Zpos XH)) :: []))))) :: (
         (when0 (ge (cell out (lit Z0)) (add0 (reg n0) (reg n0)))
           (ret (Zpos (XO XH)))) :: ((swap_cells data) :: ((put trace
                                                             (cell out
                                                               (lit Z0))
                                                             (reg depth)) :: (
         (put out (lit Z0) (add0 (cell out (lit Z0)) (lit (Zpos XH)))) :: [])))))))) :: (
    (swap_cells permutation) :: []))

(** val permute : function0 **)

let permute =
  { fn_return = u32; fn_callconv = cc_default; fn_params = ((n0,
    u32) :: ((data, ptr) :: ((permutation, ptr) :: ((target, ptr) :: ((used,
    ptr) :: ((trace, ptr) :: ((out, ptr) :: []))))))); fn_vars = [];
    fn_temps = ((i, u32) :: ((j, u32) :: ((top, u32) :: ((pos, u32) :: ((tmp,
    u32) :: ((depth, u32) :: [])))))); fn_body =
    (seq
      ((put out (lit Z0) (lit Z0)) :: ((put out (lit (Zpos XH)) (lit Z0)) :: (
      (put out (lit (Zpos (XO XH))) (lit Z0)) :: ((when0
                                                    (gt (reg n0)
                                                      (lit (Zpos (XO (XO (XO
                                                        (XO (XO (XO (XO (XO
                                                        (XO (XO XH)))))))))))))
                                                    (ret (Zpos (XO XH)))) :: (
      (when0 (eq0 (reg n0) (lit Z0)) (ret Z0)) :: (check_input :: (normalize :: (
      (set1 top (sub0 (reg n0) (lit (Zpos XH)))) :: ((Sloop
      ((seq (choose_position :: (exchange :: []))), Sskip)) :: [])))))))))) }

(** val expression : genv -> temp_env -> Mem.mem -> expr -> val0 option **)

let rec expression ge0 le m = function
| Econst_int (i0, _) -> Some (Vint i0)
| Etempvar (id, _) -> PTree.get id le
| Ederef (address, ty) ->
  (match expression ge0 le m address with
   | Some v ->
     (match v with
      | Vptr (b, ofs) ->
        (match access_mode ty with
         | By_value chunk -> Mem.loadv chunk m (Vptr (b, ofs))
         | _ -> None)
      | _ -> None)
   | None -> None)
| Ebinop (op, a0, b, _) ->
  (match expression ge0 le m a0 with
   | Some x ->
     (match expression ge0 le m b with
      | Some y ->
        sem_binary_operation ge0.genv_cenv op x (typeof a0) y (typeof b) m
      | None -> None)
   | None -> None)
| _ -> None

(** val store0 :
    genv -> temp_env -> Mem.mem -> expr -> expr -> Mem.mem option **)

let store0 ge0 le m lhs rhs =
  match lhs with
  | Ederef (address, ty) ->
    (match expression ge0 le m address with
     | Some v ->
       (match v with
        | Vptr (b, ofs) ->
          (match expression ge0 le m rhs with
           | Some x ->
             (match access_mode ty with
              | By_value chunk ->
                (match sem_cast x (typeof rhs) ty m with
                 | Some y -> Mem.storev chunk m (Vptr (b, ofs)) y
                 | None -> None)
              | _ -> None)
           | None -> None)
        | _ -> None)
     | None -> None)
  | _ -> None

type result = (temp_env * Mem.mem) * outcome

(** val execute :
    nat -> genv -> temp_env -> Mem.mem -> statement -> result option **)

let rec execute fuel ge0 le m s =
  match fuel with
  | O -> None
  | S remaining ->
    (match s with
     | Sskip -> Some ((le, m), Out_normal)
     | Sassign (lhs, rhs) ->
       (match store0 ge0 le m lhs rhs with
        | Some m' -> Some ((le, m'), Out_normal)
        | None -> None)
     | Sset (id, a) ->
       (match expression ge0 le m a with
        | Some x -> Some (((PTree.set id x le), m), Out_normal)
        | None -> None)
     | Ssequence (first, second) ->
       (match execute remaining ge0 le m first with
        | Some r ->
          let (p, o) = r in
          let (le', m') = p in
          (match o with
           | Out_normal -> execute remaining ge0 le' m' second
           | x -> Some ((le', m'), x))
        | None -> None)
     | Sifthenelse (condition, yes, no) ->
       (match expression ge0 le m condition with
        | Some x ->
          (match bool_val x (typeof condition) m with
           | Some choice ->
             execute remaining ge0 le m (if choice then yes else no)
           | None -> None)
        | None -> None)
     | Sloop (body, s0) ->
       (match s0 with
        | Sskip ->
          (match execute remaining ge0 le m body with
           | Some r ->
             let (p, o) = r in
             let (le', m') = p in
             (match o with
              | Out_break -> Some ((le', m'), Out_normal)
              | Out_continue -> None
              | Out_normal ->
                execute remaining ge0 le' m' (Sloop (body, Sskip))
              | Out_return value -> Some ((le', m'), (Out_return value)))
           | None -> None)
        | _ -> None)
     | Sbreak -> Some ((le, m), Out_break)
     | Sreturn o ->
       (match o with
        | Some a ->
          (match expression ge0 le m a with
           | Some x -> Some ((le, m), (Out_return (Some (x, (typeof a)))))
           | None -> None)
        | None -> Some ((le, m), (Out_return None)))
     | _ -> None)

(** val call_temps :
    Int.int -> val0 -> val0 -> val0 -> val0 -> val0 -> val0 -> val0 PTree.tree **)

let call_temps size0 data_arg perm_arg target_arg used_arg trace_arg out_arg =
  PTree.set out out_arg
    (PTree.set trace trace_arg
      (PTree.set used used_arg
        (PTree.set target target_arg
          (PTree.set permutation perm_arg
            (PTree.set data data_arg
              (PTree.set n0 (Vint size0)
                (create_undef_temps permute.fn_temps)))))))

(** val empty_ge : genv **)

let empty_ge =
  { genv_genv = (Genv.empty_genv []); genv_cenv = PTree.empty }

(** val write_words : Mem.mem -> block -> z -> z list -> Mem.mem option **)

let rec write_words m b offset = function
| [] -> Some m
| x :: rest ->
  (match Mem.store Mint32 m b offset (Vint (Int.repr x)) with
   | Some next ->
     write_words next b (Coq_Z.add offset (Zpos (XO (XO XH)))) rest
   | None -> None)

(** val read_words : Mem.mem -> block -> z -> nat -> z list option **)

let rec read_words m b offset = function
| O -> Some []
| S remaining ->
  (match Mem.load Mint32 m b offset with
   | Some v ->
     (match v with
      | Vint x ->
        (match read_words m b (Coq_Z.add offset (Zpos (XO (XO XH)))) remaining with
         | Some rest -> Some ((Int.unsigned x) :: rest)
         | None -> None)
      | _ -> None)
   | None -> None)

(** val observe :
    nat -> z -> Mem.mem -> val0 -> val0 -> val0 -> val0 -> val0 -> val0 ->
    block -> block -> block -> block -> nat -> z list option **)

let observe fuel size0 m da pa ta ua tr oa bd bp bt bo count =
  match execute fuel empty_ge (call_temps (Int.repr size0) da pa ta ua tr oa)
          m permute.fn_body with
  | Some r ->
    let (p, o) = r in
    let (_, final) = p in
    (match o with
     | Out_return o0 ->
       (match o0 with
        | Some p0 ->
          let (v, ty) = p0 in
          (match v with
           | Vint status ->
             if type_eq ty u32
             then (match read_words final bo Z0 (S (S (S O))) with
                   | Some l ->
                     (match l with
                      | [] -> None
                      | written :: l0 ->
                        (match l0 with
                         | [] -> None
                         | blocked :: l1 ->
                           (match l1 with
                            | [] -> None
                            | excess :: l2 ->
                              (match l2 with
                               | [] ->
                                 (match read_words final bd Z0 count with
                                  | Some xs ->
                                    (match read_words final bp Z0 count with
                                     | Some ps ->
                                       if Coq_Z.leb written
                                            (Coq_Z.mul (Zpos (XO XH))
                                              (Coq_Z.of_nat count))
                                       then (match read_words final bt Z0
                                                     (Coq_Z.to_nat written) with
                                             | Some swaps ->
                                               Some
                                                 ((Int.unsigned status) :: (written :: (blocked :: (excess :: 
                                                 (app xs (app ps swaps))))))
                                             | None -> None)
                                       else None
                                     | None -> None)
                                  | None -> None)
                               | _ :: _ -> None))))
                   | None -> None)
             else None
           | _ -> None)
        | None -> None)
     | _ -> None)
  | None -> None

(** val run : nat -> z -> z list -> z list -> z list option **)

let run fuel size0 xs ps =
  if (||) (Coq_Z.eqb size0 Z0)
       (Coq_Z.ltb (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO XH)))))))))))
         size0)
  then let (m, bo) = Mem.alloc Mem.empty Z0 (Zpos (XO (XO (XI XH)))) in
       observe fuel size0 m vzero vzero vzero vzero vzero (Vptr (bo,
         Ptrofs.zero)) bo bo bo bo O
  else let count = length xs in
       if (&&) (Coq_Z.eqb size0 (Coq_Z.of_nat count))
            (Nat.eqb count (length ps))
       then let bytes = Coq_Z.mul (Zpos (XO (XO XH))) size0 in
            let (m1, bd) = Mem.alloc Mem.empty Z0 bytes in
            let (m2, bp) = Mem.alloc m1 Z0 bytes in
            let (m3, bt) = Mem.alloc m2 Z0 bytes in
            let (m4, bu) = Mem.alloc m3 Z0 bytes in
            let (m5, br) = Mem.alloc m4 Z0 (Coq_Z.mul (Zpos (XO XH)) bytes) in
            let (m6, bo) = Mem.alloc m5 Z0 (Zpos (XO (XO (XI XH)))) in
            (match write_words m6 bd Z0 xs with
             | Some m7 ->
               (match write_words m7 bp Z0 ps with
                | Some m8 ->
                  observe fuel size0 m8 (Vptr (bd, Ptrofs.zero)) (Vptr (bp,
                    Ptrofs.zero)) (Vptr (bt, Ptrofs.zero)) (Vptr (bu,
                    Ptrofs.zero)) (Vptr (br, Ptrofs.zero)) (Vptr (bo,
                    Ptrofs.zero)) bd bp br bo count
                | None -> None)
             | None -> None)
       else None

(** val decimal : z -> char list **)

let decimal z0 =
  NilZero.string_of_int (Coq_Z.to_int z0)
