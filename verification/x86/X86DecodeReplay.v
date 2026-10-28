(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith.
From ASCommon Require Import Common Exec FMon.
From ArchSemX86 Require Import X86Inst.
From SailTinyX86 Require Import Tiny_x86.
From X86 Require Import X86Control X86Instructions X86Program X86Decode.
Import ListNotations.
Open Scope Z_scope.

Definition fetch_schedule := list (Z * N).

(* Read schedules are obtained by running the actual decoder at address zero.
   They describe memory reads, not instruction semantics. *)
Fixpoint collect_fetches {A}
    (answers : forall event : outcome, option (eff_ret event))
    (program : iMon A) : option fetch_schedule :=
  match program with
  | FMon.Ret _ => Some []
  | FMon.Next (inl event) next =>
      match answers event with
      | None => None
      | Some answer =>
          match collect_fetches answers (next answer) with
          | None => None
          | Some tail => Some
              (match event with
               | MemRead request =>
                   (bv_unsigned request.(MemReq.address), request.(MemReq.size)) :: tail
               | _ => tail
               end)
          end
      end
  | FMon.Next (inr _) _ => None
  end.

Definition zero_registers : register_values :=
  fun reg => match reg with R_bitvector_64 _ => bv_0 64 end.

Definition reference_instruction_fetches (offset : Z) : fetch_schedule :=
  default [] (collect_fetches (decoder_answers 0 zero_registers)
    (iMon_from_Sail false (Tiny_x86.decode (Z_to_bv 64 offset)))).

Definition instruction_fetch_table : list (Z * fetch_schedule) := Eval vm_compute in
  map (fun item => (fst item, reference_instruction_fetches (fst item)))
    program_instructions.

Definition instruction_fetches (offset : Z) : fetch_schedule :=
  match find (fun item => Z.eqb (fst item) offset) instruction_fetch_table with
  | Some (_, schedule) => schedule
  | None => []
  end.

Lemma fetch_table_matches_decoder :
  map (fun item => instruction_fetches (fst item)) program_instructions =
  map (fun item => reference_instruction_fetches (fst item)) program_instructions.
Proof. vm_compute. reflexivity. Qed.

Definition fetch_in_code (item : Z * N) : bool :=
  (0 <=? fst item) &&
  (fst item + Z.of_N (snd item) <=? Z.of_nat (List.length program_bytes)).

Lemma all_fetches_in_code :
  forallb (fun item => forallb fetch_in_code (instruction_fetches (fst item)))
    program_instructions = true.
Proof. vm_compute. reflexivity. Qed.

Lemma instruction_fetch_in_code offset size fetched count :
  In (offset, size) program_instructions ->
  In (fetched, count) (instruction_fetches offset) ->
  0 <= fetched /\ fetched + Z.of_N count <= Z.of_nat (List.length program_bytes).
Proof.
  intros At Fetch. pose proof all_fetches_in_code as All.
  apply forallb_forall with (x := (offset, size)) in All; [|exact At].
  change (forallb fetch_in_code (instruction_fetches offset) = true) in All.
  apply forallb_forall with (x := (fetched, count)) in All; [|exact Fetch].
  unfold fetch_in_code in All. apply andb_true_iff in All as [Low High].
  split; now apply Z.leb_le.
Qed.

Definition code_read_value (size : N) (offset : Z) : bv (8 * size) :=
  bv_of_bytes (8 * size)
    (firstn (N.to_nat size) (skipn (Z.to_nat offset) program_bytes)).

(* Replay retains every actual memory request. Its soundness theorem requires
   these requests, including their addresses, to succeed in ArchSem. *)
Fixpoint replay_fetches {A} (registers : register_values) (schedule : fetch_schedule)
    (program : iMon A) : option (A * list iEvent * fetch_schedule) :=
  match program with
  | FMon.Ret value => Some (value, [], schedule)
  | FMon.Next (inl (RegRead reg _)) next =>
      replay_fetches registers schedule (next (registers reg))
  | FMon.Next (inl (MemRead request)) next =>
      match schedule with
      | [] => None
      | (offset, size) :: rest =>
          if N.eqb request.(MemReq.size) size then
            let answer := Ok (code_read_value request.(MemReq.size) offset,
              bv_0 request.(MemReq.num_tag)) in
            match replay_fetches registers rest (next answer) with
            | Some (value, events, remaining) =>
                Some (value, (MemRead request &→ answer) :: events, remaining)
            | None => None
            end
          else None
      end
  | _ => None
  end.

Definition event_succeeds (state : seq_state) (event : iEvent) : Prop :=
  sequential_model_outcome None (fcall event) state =
    Exec.make [(state, fret event)] [].

Lemma replay_fetches_sound {A} nondet registers (program : iMon A)
    schedule state value events remaining :
  (forall reg access,
    sequential_model_outcome None (RegRead reg access) state =
      Exec.make [(state, registers reg)] []) ->
  replay_fetches registers schedule program = Some (value, events, remaining) ->
  Forall (event_succeeds state) events ->
  sail_trace nondet program state state value.
Proof.
  intro Registers. revert schedule value events remaining.
  induction program as [result|[event|choice] next IH];
    intros schedule value events remaining Run Events.
  - cbn in Run. inversion Run; subst. constructor.
  - destruct event; cbn [replay_fetches] in Run; try discriminate.
    + econstructor; [apply Registers|]. eapply IH; eassumption.
    + destruct schedule as [|[offset size] rest]; [discriminate|].
      destruct (N.eqb (MemReq.size mr) size); [|discriminate].
      destruct (replay_fetches registers rest _) as [[[result tail] unused]|]
        eqn:Tail; [|discriminate].
      inversion Run; subst. inversion Events; subst.
      econstructor; [exact H1|]. eapply IH; eassumption.
  - discriminate.
Qed.

Definition replay_decode nondet (pc : bv 64) (registers : register_values) (offset : Z) :=
  replay_fetches registers (instruction_fetches offset)
    (iMon_from_Sail nondet (Tiny_x86.decode pc)).

Definition expected_fetch (pc : bv 64) (offset : Z) (item : Z * N) : iEvent :=
  let request := MemReq.make (Tiny_x86.create_iFetchAccessDescriptor tt)
    (@SailStdpp.Operators_mwords.vector_truncate 64
      (@SailStdpp.Operators_mwords.add_vec_int 64 pc (fst item - offset)) 64)
    tt (snd item) 0 in
  MemRead request &→ Ok (code_read_value (snd item) (fst item), bv_0 0).

Definition replay_decode_summary nondet pc registers offset :=
  match replay_decode nondet pc registers offset with
  | Some (Some (next, _), events, remaining) => Some (next, events, remaining)
  | _ => None
  end.

Lemma relocated_decode_summary nondet pc registers :
  map (fun item => replay_decode_summary nondet pc registers (fst item))
    program_instructions =
  map (fun item => Some
    (@SailStdpp.Operators_mwords.add_vec_int 64 pc (snd item),
      map (expected_fetch pc (fst item)) (instruction_fetches (fst item)), []))
    program_instructions.
Proof.
  destruct nondet; reflexivity.
Qed.

Definition decoded_instruction nondet pc (registers : register_values) (offset : Z) : option ast :=
  match replay_decode nondet pc registers offset with
  | Some (Some (_, instruction), _, _) => Some instruction
  | _ => None
  end.

Lemma equal_maps_at {A B} (f g : A -> B) items item :
  map f items = map g items -> In item items -> f item = g item.
Proof.
  induction items as [|head tail IH]; [contradiction|].
  cbn. intros Equal [Here|There].
  - inversion Equal. now subst.
  - inversion Equal. eapply IH; eassumption.
Qed.

Theorem decode_instruction_trace nondet state pc registers offset size instruction :
  In (offset, size) program_instructions ->
  decoded_instruction nondet pc registers offset = Some instruction ->
  (forall reg, read_reg_seq_state reg state = Some (registers reg)) ->
  Forall (event_succeeds state)
    (map (expected_fetch pc offset) (instruction_fetches offset)) ->
  sail_trace nondet (iMon_from_Sail nondet (Tiny_x86.decode pc)) state state
    (Some (@SailStdpp.Operators_mwords.add_vec_int 64 pc size, instruction)).
Proof.
  intros At Instruction Registers Fetches.
  pose proof (equal_maps_at _ _ _ (offset, size)
    (relocated_decode_summary nondet pc registers) At) as Summary.
  change (replay_decode_summary nondet pc registers offset = Some
    (@SailStdpp.Operators_mwords.add_vec_int 64 pc size,
      map (expected_fetch pc offset) (instruction_fetches offset), [])) in Summary.
  unfold replay_decode_summary in Summary.
  unfold decoded_instruction in Instruction.
  destruct (replay_decode nondet pc registers offset)
    as [[[result events] remaining]|] eqn:Replay; try discriminate.
  destruct result as [[next decoded]|]; try discriminate.
  inversion Summary; inversion Instruction; subst.
  eapply replay_fetches_sound.
  - intros reg access. apply register_read, Registers.
  - exact Replay.
  - exact Fetches.
Qed.

Print Assumptions replay_fetches_sound.
Print Assumptions relocated_decode_summary.
Print Assumptions decode_instruction_trace.
