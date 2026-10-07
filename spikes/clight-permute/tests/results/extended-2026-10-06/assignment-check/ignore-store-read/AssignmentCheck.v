(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List Bool PArith ZArith.
From compcert Require Import AST Ctypes Clight.
Require Import Permute.
Import ListNotations.
Open Scope Z_scope.

(* This checks prior assignment of temporary variables. It does not check
   whether a memory load returns initialized bytes or a valid address. *)
Definition assigned := list ident.
Definition member (id : ident) (ids : assigned) := existsb (Pos.eqb id) ids.

Fixpoint uses (ids : assigned) (a : expr) : bool :=
  match a with
  | Econst_int _ _ => true
  | Etempvar id _ => member id ids
  | Ederef address _ => uses ids address
  | Ebinop _ a b _ => uses ids a && uses ids b
  | _ => false
  end.

Fixpoint temp_reads (a : expr) : list ident :=
  match a with
  | Etempvar id _ => [id]
  | Ederef address _ => temp_reads address
  | Ebinop _ a b _ => temp_reads a ++ temp_reads b
  | _ => []
  end.

Lemma member_spec id ids : member id ids = true <-> In id ids.
Proof.
  unfold member. rewrite existsb_exists. split.
  - intros [x [X Equal]]. apply Pos.eqb_eq in Equal. now subst x.
  - intro H. exists id. split; [exact H|apply Pos.eqb_refl].
Qed.

Theorem uses_covers_reads ids a :
  uses ids a = true -> forall id, In id (temp_reads a) -> In id ids.
Proof.
  induction a; cbn; intros H id R; try discriminate; try contradiction.
  - destruct R as [<-|[]]. apply member_spec. exact H.
  - exact (IHa H id R).
  - apply andb_true_iff in H as [A B]. apply in_app_iff in R as [R|R].
    + exact (IHa1 A id R).
    + exact (IHa2 B id R).
Qed.

(* None inside an exit means that no such control-flow path reaches it.
   Some ids records variables assigned on every path reaching that exit. *)
Record exits := { normal : option assigned; broken : option assigned }.
Definition join (a b : option assigned) : option assigned :=
  match a, b with
  | None, other | other, None => other
  | Some first, Some second => Some (filter (fun id => member id second) first)
  end.

Definition continuing ids := {| normal := Some ids; broken := None |}.
Definition returning := {| normal := None; broken := None |}.

Fixpoint check (ids : assigned) (s : statement) : option exits :=
  match s with
  | Sskip => Some (continuing ids)
  | Sset id value =>
      if uses ids value then Some (continuing (id :: ids)) else None
  | Sassign (Ederef address _) value =>
      if uses ids address then Some (continuing ids) else None
  | Ssequence first second =>
      match check ids first with
      | Some before =>
          match normal before with
          | None => Some before
          | Some next =>
              match check next second with
              | Some after => Some {| normal := normal after;
                  broken := join (broken before) (broken after) |}
              | None => None
              end
          end
      | None => None
      end
  | Sifthenelse condition yes no =>
      if uses ids condition then
        match check ids yes, check ids no with
        | Some a, Some b => Some {| normal := join (normal a) (normal b);
                                    broken := join (broken a) (broken b) |}
        | _, _ => None
        end
      else None
  | Sloop body Sskip =>
      (* Assignment sets only grow. The first iteration has the fewest
         assigned variables. Breaks of a nested loop are consumed there. *)
      match check ids body with
      | Some paths => Some {| normal := broken paths; broken := None |}
      | None => None
      end
  | Sbreak => Some {| normal := None; broken := Some ids |}
  | Sreturn (Some value) => if uses ids value then Some returning else None
  | _ => None
  end.

Definition check_function (fn : function) : bool :=
  match check (map fst (fn_params fn)) (fn_body fn) with
  | Some {| normal := None; broken := None |} => true
  | _ => false
  end.

Theorem permute_passes_assignment_check : check_function permute = true.
Proof. vm_compute. reflexivity. Qed.

Definition test_function body :=
  {| fn_return := fn_return permute; fn_callconv := fn_callconv permute;
     fn_params := fn_params permute; fn_vars := fn_vars permute;
     fn_temps := fn_temps permute; fn_body := body |}.

Definition accepts body := check_function (test_function body).

Example rejects_undefined_self_copy : accepts (seq [set i (reg i); ret 0]) = false.
Proof. reflexivity. Qed.
Example rejects_undefined_prefix_of_permute :
  accepts (Ssequence (set i (reg i)) (fn_body permute)) = false.
Proof. reflexivity. Qed.
Example accepts_parameter_copy_before_permute :
  accepts (Ssequence (set n (reg n)) (fn_body permute)) = true.
Proof. vm_compute. reflexivity. Qed.
Example rejects_undefined_other_copy : accepts (seq [set i (reg j); ret 0]) = false.
Proof. reflexivity. Qed.
Example rejects_undefined_return : accepts (Sreturn (Some (reg i))) = false.
Proof. reflexivity. Qed.
Example rejects_undefined_condition :
  accepts (Sifthenelse (lt (reg i) (lit 1)) (ret 0) (ret 1)) = false.
Proof. reflexivity. Qed.
Example rejects_undefined_address :
  accepts (seq [put data (reg i) (lit 1); ret 0]) = false.
Proof. reflexivity. Qed.
Example rejects_undefined_store :
  accepts (seq [put data (lit 0) (reg i); ret 0]) = false.
Proof. reflexivity. Qed.
Example rejects_one_branch_assignment : accepts (seq [
  when (eq (reg n) (lit 0)) (set i (lit 1)); Sreturn (Some (reg i))]) = false.
Proof. reflexivity. Qed.
Example accepts_both_branch_assignment : accepts (seq [
  Sifthenelse (eq (reg n) (lit 0)) (set i (lit 1)) (set i (lit 2));
  Sreturn (Some (reg i))]) = true.
Proof. reflexivity. Qed.
Example accepts_returning_branch : accepts (seq [
  Sifthenelse (eq (reg n) (lit 0)) (ret 0) (set i (lit 2));
  Sreturn (Some (reg i))]) = true.
Proof. reflexivity. Qed.
Example rejects_undefined_read_in_loop : accepts (seq [
  loop (eq (reg n) (lit 0)) (set i (reg j)); ret 0]) = false.
Proof. reflexivity. Qed.
Example rejects_zero_iteration_assignment : accepts (seq [
  loop (eq (reg n) (lit 0)) (set i (lit 1));
  Sreturn (Some (reg i))]) = false.
Proof. reflexivity. Qed.
Example accepts_assignment_before_break : accepts (seq [
  Sloop (seq [set i (lit 1); Sbreak]) Sskip;
  Sreturn (Some (reg i))]) = true.
Proof. reflexivity. Qed.
Example rejects_one_break_assignment : accepts (seq [
  Sloop (Sifthenelse (eq (reg n) (lit 0)) Sbreak
    (seq [set i (lit 1); Sbreak])) Sskip;
  Sreturn (Some (reg i))]) = false.
Proof. reflexivity. Qed.
Example rejects_inner_break_as_outer_exit : accepts (seq [
  loop (eq (reg n) (lit 0)) (Sloop (seq [set i (lit 1); Sbreak]) Sskip);
  Sreturn (Some (reg i))]) = false.
Proof. reflexivity. Qed.
Example accepts_dead_copy_after_return : accepts (seq [ret 0; set i (reg i)]) = true.
Proof. reflexivity. Qed.
Example accepts_parameter_read : accepts (Sreturn (Some (reg n))) = true.
Proof. reflexivity. Qed.
Example rejects_top_level_break : accepts Sbreak = false.
Proof. reflexivity. Qed.
Example rejects_fallthrough : accepts (set i (lit 1)) = false.
Proof. reflexivity. Qed.

(* Deliberately outside the claim: a load is not checked for initialized
   bytes. Passing this check alone is not a C-definedness proof. *)
Example memory_load_is_a_separate_obligation :
  accepts (seq [set i (cell data (lit 0)); ret 0]) = true.
Proof. reflexivity. Qed.

Print Assumptions uses_covers_reads.
Print Assumptions permute_passes_assignment_check.
