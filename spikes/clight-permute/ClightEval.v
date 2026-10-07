(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Coq Require Import List ZArith.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Cop
  Clight ClightBigstep.

(* A partial interpreter of the actual CompCert AST. None means an unsupported
   form, a failed semantic operation, or a fuel limit. It is not a C result. *)
Fixpoint expression (ge : genv) (le : temp_env) (m : mem) (a : expr)
    : option val :=
  match a with
  | Econst_int i _ => Some (Vint i)
  | Etempvar id _ => PTree.get id le
  | Ederef address ty =>
      match expression ge le m address, access_mode ty with
      | Some (Vptr b ofs), By_value chunk => Mem.loadv chunk m (Vptr b ofs)
      | _, _ => None
      end
  | Ebinop op a b _ =>
      match expression ge le m a, expression ge le m b with
      | Some x, Some y => sem_binary_operation ge op x (typeof a) y (typeof b) m
      | _, _ => None
      end
  | _ => None
  end.

Definition store (ge : genv) (le : temp_env) (m : mem) (lhs rhs : expr)
    : option mem :=
  match lhs with
  | Ederef address ty =>
      match expression ge le m address, expression ge le m rhs, access_mode ty with
      | Some (Vptr b ofs), Some x, By_value chunk =>
          match sem_cast x (typeof rhs) ty m with
          | Some y => Mem.storev chunk m (Vptr b ofs) y
          | None => None
          end
      | _, _, _ => None
      end
  | _ => None
  end.

Definition result := (temp_env * mem * outcome)%type.

Fixpoint execute (fuel : nat) (ge : genv) (le : temp_env) (m : mem)
    (s : statement) : option result :=
  match fuel with
  | O => None
  | S remaining =>
      match s with
      | Sskip => Some (le, m, Out_normal)
      | Sassign lhs rhs =>
          match store ge le m lhs rhs with
          | Some m' => Some (le, m', Out_normal)
          | None => None
          end
      | Sset id a =>
          match expression ge le m a with
          | Some x => Some (PTree.set id x le, m, Out_normal)
          | None => None
          end
      | Ssequence first second =>
          match execute remaining ge le m first with
          | Some (le', m', Out_normal) => execute remaining ge le' m' second
          | other => other
          end
      | Sifthenelse condition yes no =>
          match expression ge le m condition with
          | Some x =>
              match bool_val x (typeof condition) m with
              | Some choice => execute remaining ge le m (if choice then yes else no)
              | None => None
              end
          | None => None
          end
      | Sloop body Sskip =>
          match execute remaining ge le m body with
          | Some (le', m', Out_normal) =>
              execute remaining ge le' m' (Sloop body Sskip)
          | Some (le', m', Out_break) => Some (le', m', Out_normal)
          | Some (le', m', Out_return value) => Some (le', m', Out_return value)
          | _ => None
          end
      | Sbreak => Some (le, m, Out_break)
      | Sreturn None => Some (le, m, Out_return None)
      | Sreturn (Some a) =>
          match expression ge le m a with
          | Some x => Some (le, m, Out_return (Some (x, typeof a)))
          | None => None
          end
      | _ => None
      end
  end.
