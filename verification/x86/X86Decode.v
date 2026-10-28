(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith.
From ASCommon Require Import Common Exec FMon.
From ArchSemX86 Require Import X86Inst.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Control X86Instructions X86Program.
Import ListNotations.
Open Scope Z_scope.

(* This evaluator handles events of the actual Sail decoder. It contains no
   instruction decoding rules. Its answers must agree with the actual ArchSem
   handler before its result can be used as an execution fact. *)
Fixpoint read_only_run {A} (answers : forall event : outcome, option (eff_ret event))
    (program : iMon A) : option A :=
  match program with
  | FMon.Ret value => Some value
  | FMon.Next (inl event) next =>
      match answers event with
      | Some value => read_only_run answers (next value)
      | None => None
      end
  | FMon.Next (inr _) _ => None
  end.

Lemma read_only_run_sound {A} answers (program : iMon A) state value :
  (forall event answer, answers event = Some answer ->
    sequential_model_outcome None event state =
      Exec.make [(state, answer)] []) ->
  read_only_run answers program = Some value ->
  FMon.cinterp (sequential_model_outcome None) program state =
    Exec.make [(state, value)] [].
Proof.
  intro Answers. induction program as [result|[event|choice] next IH].
  - cbn. intro Equal. inversion Equal. reflexivity.
  - cbn [read_only_run]. destruct (answers event) as [answer|] eqn:Answer;
      [|discriminate].
    intro Result. cbn [FMon.cinterp FMon.finterp FMon.fHandler_plus].
    erewrite exec_bind_single by exact (Answers event answer Answer).
    exact (IH answer Result).
  - discriminate.
Qed.

Lemma read_only_run_trace {A} nondet answers (program : iMon A) state value :
  (forall event answer, answers event = Some answer ->
    sequential_model_outcome None event state =
      Exec.make [(state, answer)] []) ->
  read_only_run answers program = Some value ->
  sail_trace nondet program state state value.
Proof.
  intro Answers. induction program as [result|[event|choice] next IH].
  - cbn. intro Equal. inversion Equal. constructor.
  - cbn [read_only_run]. destruct (answers event) as [answer|] eqn:Answer;
      [|discriminate].
    intro Result. econstructor.
    + exact (Answers event answer Answer).
    + exact (IH answer Result).
  - discriminate.
Qed.

Definition register_values := forall reg : Arch.reg, Arch.reg_type reg.

Definition decoder_answers (base : Z) (registers : register_values)
    (event : outcome) : option (eff_ret event) :=
  match event with
  | RegRead reg _ => Some (registers reg)
  | MemRead request =>
      let offset := bv_unsigned request.(MemReq.address) - base in
      if is_ifetch request.(MemReq.access_kind) &&
          (0 <=? offset) &&
          (offset + Z.of_N request.(MemReq.size) <=?
            Z.of_nat (List.length program_bytes)) then
        Some (Ok (bv_of_bytes (8 * request.(MemReq.size))
          (firstn (N.to_nat request.(MemReq.size))
            (skipn (Z.to_nat offset) program_bytes)),
          bv_0 request.(MemReq.num_tag)))
      else None
  | _ => None
  end.

Definition decode_program (base : Z) (registers : register_values) (offset : Z) :=
  read_only_run (decoder_answers base registers)
    (iMon_from_Sail false (Tiny_x86.decode (Z_to_bv 64 (base + offset)))).

Definition decoded_next (base : Z) (registers : register_values) (offset : Z)
    : option Z :=
  match decode_program base registers offset with
  | Some (Some (next, _)) => Some (bv_unsigned next - base)
  | _ => None
  end.

Lemma decoder_lengths_at_fixed_base registers :
  map (fun item => decoded_next 4194304 registers (fst item))
    program_instructions =
  map (fun item => Some (fst item + snd item)) program_instructions.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions read_only_run_sound.
Print Assumptions decoder_lengths_at_fixed_base.
