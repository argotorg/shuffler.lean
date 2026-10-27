(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith.
Require Import Integers AST Ctypes Cop Clight.
Import ListNotations.
Open Scope Z_scope.
Open Scope positive_scope.

(* Construct Clight directly. There is no C parser or compiler pass. *)
Definition u32 := Tint I32 Unsigned noattr.
Definition i32 := Tint I32 Signed noattr.
Definition ptr := Tpointer u32 noattr.

Definition n : ident := 1.
Definition data : ident := 2.
Definition permutation : ident := 3.
Definition target : ident := 4.
Definition used : ident := 5.
Definition trace : ident := 6.
Definition out : ident := 7.
Definition i : ident := 8.
Definition j : ident := 9.
Definition top : ident := 10.
Definition pos : ident := 11.
Definition tmp : ident := 12.
Definition depth : ident := 13.

Definition lit (z : Z) := Econst_int (Int.repr z) u32.
Definition reg (v : ident) := Etempvar v u32.
Definition cell (a : ident) (index : expr) :=
  Ederef (Ebinop Oadd (Etempvar a ptr) index ptr) u32.
Definition add (a b : expr) := Ebinop Oadd a b u32.
Definition sub (a b : expr) := Ebinop Osub a b u32.
Definition eq (a b : expr) := Ebinop Oeq a b i32.
Definition ne (a b : expr) := Ebinop One a b i32.
Definition lt (a b : expr) := Ebinop Olt a b i32.
Definition gt (a b : expr) := Ebinop Ogt a b i32.
Definition ge (a b : expr) := Ebinop Oge a b i32.
Definition seq (ss : list statement) := fold_right Ssequence Sskip ss.
Definition set (v : ident) (e : expr) := Sset v e.
Definition put (a : ident) (index value : expr) := Sassign (cell a index) value.
Definition ret (z : Z) := Sreturn (Some (lit z)).
Definition when (c : expr) (s : statement) := Sifthenelse c s Sskip.
Definition loop (c : expr) (body : statement) :=
  Sloop (Ssequence (Sifthenelse c Sskip Sbreak) body) Sskip.
Definition inc (v : ident) := set v (add (reg v) (lit 1)).
Definition each (v : ident) (body : statement) :=
  seq [set v (lit 0); loop (lt (reg v) (reg n)) (seq [body; inc v])].

(* The check precedes each use of an input destination as an index. *)
Definition check_input := seq [
  each i (put used (reg i) (lit 0));
  each i (seq [
    set j (cell permutation (reg i));
    when (ge (reg j) (reg n)) (ret 2);
    when (ne (cell used (reg j)) (lit 0)) (ret 2);
    put used (reg j) (lit 1);
    put target (reg j) (cell data (reg i))
  ])
].

(* Fix equal values already at a desired position. Pair the other source
   positions with free equal target positions, both in increasing order. *)
Definition normalize := seq [
  each i (Sifthenelse (eq (cell data (reg i)) (cell target (reg i)))
    (seq [put permutation (reg i) (reg i); put used (reg i) (lit 1)])
    (put used (reg i) (lit 0)));
  each i (when (ne (cell data (reg i)) (cell target (reg i))) (seq [
    set j (lit 0);
    loop (lt (reg j) (reg n)) (seq [
      when (eq (cell used (reg j)) (lit 0))
        (when (eq (cell data (reg i)) (cell target (reg j))) Sbreak);
      inc j
    ]);
    (* Defensive guard: valid input has a free equal target. *)
    when (eq (reg j) (reg n)) (ret 2);
    put permutation (reg i) (reg j);
    put used (reg j) (lit 1)
  ]))
].

Definition choose_position := seq [
  set pos (cell permutation (reg top));
  when (eq (reg pos) (reg top)) (seq [
    loop (gt (reg pos) (lit 0)) (seq [
      set pos (sub (reg pos) (lit 1));
      when (ne (cell permutation (reg pos)) (reg pos)) Sbreak
    ]);
    when (eq (cell permutation (reg pos)) (reg pos)) (ret 0)
  ])
].

Definition swap_cells (a : ident) := seq [
  set tmp (cell a (reg pos));
  put a (reg pos) (cell a (reg top));
  put a (reg top) (reg tmp)
].

Definition exchange := seq [
  when (ne (cell data (reg pos)) (cell data (reg top))) (seq [
    set depth (sub (reg top) (reg pos));
    when (gt (reg depth) (lit (8 + 8))) (seq [
      put out (lit 1) (reg pos);
      put out (lit 2) (sub (reg depth) (lit 16));
      ret 1
    ]);
    (* The capacity is part of the caller contract. This check also makes
       the store bound explicit in the code. *)
    when (ge (cell out (lit 0)) (add (reg n) (reg n))) (ret 2);
    swap_cells data;
    put trace (cell out (lit 0)) (reg depth);
    put out (lit 0) (add (cell out (lit 0)) (lit 1))
  ]);
  swap_cells permutation
].

Definition permute : function := {|
  fn_return := u32;
  fn_callconv := cc_default;
  fn_params := [(n, u32); (data, ptr); (permutation, ptr); (target, ptr);
                (used, ptr); (trace, ptr); (out, ptr)];
  fn_vars := [];
  fn_temps := [(i, u32); (j, u32); (top, u32); (pos, u32);
               (tmp, u32); (depth, u32)];
  fn_body := seq [
    put out (lit 0) (lit 0);
    put out (lit 1) (lit 0);
    put out (lit 2) (lit 0);
    when (gt (reg n) (lit 1024)) (ret 2);
    when (eq (reg n) (lit 0)) (ret 0);
    check_input;
    normalize;
    set top (sub (reg n) (lit 1));
    Sloop (seq [choose_position; exchange]) Sskip
  ]
|}.
