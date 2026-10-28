(* SPDX-License-Identifier: GPL-3.0-or-later *)
From Stdlib Require Import List ZArith Lia.
From ITree Require Import ITree ITreeFacts.
From Vellvm Require Import Utils Syntax Params ParamsV IPtrInfinite DynamicValues
  LLVMEvents IntMaps Interfaces.Memory Implementations.Memory Handlers.Memory.
Import ListNotations.

Module Impl := Vellvm.Semantics.Implementations.Memory.
Module Handler := Vellvm.Semantics.Handlers.Memory.

#[local] Instance parameters : Params := @ParamsV IPZ IPZTheory.
#[local] Existing Instance MemoryModelPrimitivesV.

Definition bytes (s : Impl.State) :=
  Impl.Memory_stack_memory (Impl.state_memory_stack s).

Definition with_bytes (s : Impl.State) (m : Impl.memory) : Impl.State :=
  Impl.mkState
    (Impl.mkMemoryStack m
      (Impl.Memory_stack_frame_stack (Impl.state_memory_stack s))
      (Impl.Memory_stack_heap (Impl.state_memory_stack s)))
    (Impl.state_provenance s).

Definition put_byte (s : Impl.State) (address : Z) b aid :=
  with_bytes s (IntMaps.IM.add address (b, aid) (bytes s)).

Definition run_memory {A} (c : memM A) (s : Impl.State)
    : itree MCFGEbot (Impl.State * A) :=
  Handler.memM_interp c s.

(* Finite paths through Vellvm's memory effects. There is no rule for UB,
   failure, OOM, or allocation choices. Loads and stores need only these
   three rules. The soundness lemma uses Vellvm's actual memory handler. *)
Inductive memory_steps {A} : memM A -> Impl.State -> Impl.State -> A -> Prop :=
| steps_ret s x : memory_steps (Mret x) s s x
| steps_get k s final x :
    memory_steps (k s) s final x -> memory_steps (Mget k) s final x
| steps_put k initial s final x :
    memory_steps (k tt) s final x -> memory_steps (Mput s k) initial final x.

Lemma memory_steps_sound A (c : memM A) initial final x :
  memory_steps c initial final x -> run_memory c initial = Ret (final, x).
Proof.
  intro Steps; induction Steps; unfold run_memory in *;
    cbn [Handler.memM_interp]; auto.
Qed.

Lemma memory_steps_bind A B (c : memM A) (k : A -> memM B) s middle final x y :
  memory_steps c s middle x -> memory_steps (k x) middle final y ->
  memory_steps (memS_bind c k) s final y.
Proof.
  intros First Last; induction First; cbn [memS_bind];
    [exact Last | apply steps_get | eapply steps_put]; auto.
Qed.

Lemma read_byte_correct s address provenance b aid :
  IntMaps.IM.find address (bytes s) = Some (b, aid) ->
  access_allowed provenance aid = true ->
  run_memory (Impl.Read_byte (address, provenance)) s = Ret (s, b).
Proof.
  intros Found Allowed.
  unfold run_memory, Impl.Read_byte, Impl.read_byte_raw.
  cbn.
  unfold bytes in Found.
  unfold Impl.read_byte_raw_mem.
  rewrite Found; cbn.
  cbn in Allowed. now rewrite Allowed.
Qed.

Lemma write_byte_correct s address provenance old b aid :
  IntMaps.IM.find address (bytes s) = Some (old, aid) ->
  access_allowed provenance aid = true ->
  run_memory (Impl.Write_byte (address, provenance) b) s =
    Ret (put_byte s address b aid, tt).
Proof.
  intros Found Allowed.
  unfold run_memory, Impl.Write_byte, Impl.read_byte_raw.
  cbn.
  unfold bytes in Found.
  unfold Impl.read_byte_raw_mem.
  rewrite Found; cbn.
  cbn in Allowed. rewrite Allowed.
  destruct s as [[m frame heap] next]; reflexivity.
Qed.

Lemma put_byte_here s address b aid :
  IntMaps.IM.find address (bytes (put_byte s address b aid)) = Some (b, aid).
Proof. apply IntMaps.lookup_add_eq. Qed.

Lemma put_byte_elsewhere s address other b aid :
  other <> address ->
  IntMaps.IM.find other (bytes (put_byte s address b aid)) =
    IntMaps.IM.find other (bytes s).
Proof. apply IntMaps.lookup_add_ineq. Qed.

Lemma read_byte_steps s address provenance b aid :
  IntMaps.IM.find address (bytes s) = Some (b, aid) ->
  access_allowed provenance aid = true ->
  memory_steps (Impl.Read_byte (address, provenance)) s s b.
Proof.
  intros Found Allowed.
  unfold Impl.Read_byte, Impl.read_byte_raw; cbn.
  apply steps_get; cbn.
  unfold Impl.read_byte_raw_mem, bytes in *.
  rewrite Found; cbn.
  cbn in Allowed. rewrite Allowed. constructor.
Qed.

Lemma write_byte_steps s address provenance old b aid :
  IntMaps.IM.find address (bytes s) = Some (old, aid) ->
  access_allowed provenance aid = true ->
  memory_steps (Impl.Write_byte (address, provenance) b) s
    (put_byte s address b aid) tt.
Proof.
  intros Found Allowed.
  unfold Impl.Write_byte, Impl.read_byte_raw; cbn.
  apply steps_get; cbn.
  unfold Impl.read_byte_raw_mem, bytes in Found |- *.
  rewrite Found; cbn.
  cbn in Allowed. rewrite Allowed.
  destruct s as [[m frame heap] next].
  repeat constructor.
Qed.

Lemma consecutive_four address provenance :
  Impl.get_consecutive_ptrs (address, provenance) 4%N =
    EOU.raise_ret [(address, provenance); ((address + 1)%Z, provenance);
      ((address + 2)%Z, provenance); ((address + 3)%Z, provenance)].
Proof. destruct address; reflexivity. Qed.

(* Allocation and provenance are checked for each byte. The initial contents
   are separate from permission to write, as in the Clight call contract. *)
Definition byte_at s address provenance b : Prop :=
  exists aid, IntMaps.IM.find address (bytes s) = Some (b, aid) /\
    access_allowed provenance aid = true.

Definition four_bytes_at s address provenance b0 b1 b2 b3 : Prop :=
  byte_at s address provenance b0 /\
  byte_at s (address + 1)%Z provenance b1 /\
  byte_at s (address + 2)%Z provenance b2 /\
  byte_at s (address + 3)%Z provenance b3.

Lemma read_four_steps s address provenance b0 b1 b2 b3 :
  four_bytes_at s address provenance b0 b1 b2 b3 ->
  memory_steps (Impl.read_bytes (address, provenance) 4%N) s s
    [b0; b1; b2; b3].
Proof.
  intros [[aid0 [F0 A0]] [[aid1 [F1 A1]]
    [[aid2 [F2 A2]] [aid3 [F3 A3]]]]].
  unfold Impl.read_bytes. rewrite consecutive_four.
  change (memory_steps
    (memS_bind (Impl.Read_byte (address, provenance)) (fun x0 =>
     memS_bind (Impl.Read_byte ((address + 1)%Z, provenance)) (fun x1 =>
     memS_bind (Impl.Read_byte ((address + 2)%Z, provenance)) (fun x2 =>
     memS_bind (Impl.Read_byte ((address + 3)%Z, provenance)) (fun x3 =>
     Mret [x0; x1; x2; x3]))))) s s [b0; b1; b2; b3]).
  eapply memory_steps_bind; [eapply read_byte_steps; eassumption|].
  eapply memory_steps_bind; [eapply read_byte_steps; eassumption|].
  eapply memory_steps_bind; [eapply read_byte_steps; eassumption|].
  eapply memory_steps_bind; [eapply read_byte_steps; eassumption|].
  constructor.
Qed.

Lemma read_four_correct s address provenance b0 b1 b2 b3 :
  four_bytes_at s address provenance b0 b1 b2 b3 ->
  run_memory (Impl.read_bytes (address, provenance) 4%N) s =
    Ret (s, [b0; b1; b2; b3]).
Proof. intro H; apply memory_steps_sound, read_four_steps, H. Qed.

Definition put_four s address b0 b1 b2 b3 aid0 aid1 aid2 aid3 :=
  put_byte
    (put_byte
      (put_byte (put_byte s address b0 aid0) (address + 1)%Z b1 aid1)
      (address + 2)%Z b2 aid2)
    (address + 3)%Z b3 aid3.

Lemma write_four_steps s address provenance
    old0 old1 old2 old3 b0 b1 b2 b3 aid0 aid1 aid2 aid3 :
  IntMaps.IM.find address (bytes s) = Some (old0, aid0) ->
  IntMaps.IM.find (address + 1)%Z (bytes s) = Some (old1, aid1) ->
  IntMaps.IM.find (address + 2)%Z (bytes s) = Some (old2, aid2) ->
  IntMaps.IM.find (address + 3)%Z (bytes s) = Some (old3, aid3) ->
  access_allowed provenance aid0 = true ->
  access_allowed provenance aid1 = true ->
  access_allowed provenance aid2 = true ->
  access_allowed provenance aid3 = true ->
  memory_steps (Impl.write_bytes (address, provenance) [b0; b1; b2; b3]) s
    (put_four s address b0 b1 b2 b3 aid0 aid1 aid2 aid3) tt.
Proof.
  intros F0 F1 F2 F3 A0 A1 A2 A3.
  unfold Impl.write_bytes. change (N.length [b0; b1; b2; b3]) with 4%N.
  rewrite consecutive_four.
  change (memory_steps
    (memS_bind (Impl.Write_byte (address, provenance) b0) (fun _ =>
     memS_bind (Impl.Write_byte ((address + 1)%Z, provenance) b1) (fun _ =>
     memS_bind (Impl.Write_byte ((address + 2)%Z, provenance) b2) (fun _ =>
     memS_bind (Impl.Write_byte ((address + 3)%Z, provenance) b3) (fun _ =>
     Mret tt))))) s
    (put_four s address b0 b1 b2 b3 aid0 aid1 aid2 aid3) tt).
  eapply memory_steps_bind; [eapply write_byte_steps; eassumption|].
  eapply memory_steps_bind.
  - eapply write_byte_steps; [rewrite put_byte_elsewhere by lia; exact F1|exact A1].
  - eapply memory_steps_bind.
    + eapply write_byte_steps;
        [repeat rewrite put_byte_elsewhere by lia; exact F2|exact A2].
    + eapply memory_steps_bind.
      * eapply write_byte_steps;
          [repeat rewrite put_byte_elsewhere by lia; exact F3|exact A3].
      * constructor.
Qed.

Lemma put_four_contents s address provenance b0 b1 b2 b3 aid0 aid1 aid2 aid3 :
  access_allowed provenance aid0 = true ->
  access_allowed provenance aid1 = true ->
  access_allowed provenance aid2 = true ->
  access_allowed provenance aid3 = true ->
  four_bytes_at (put_four s address b0 b1 b2 b3 aid0 aid1 aid2 aid3)
    address provenance b0 b1 b2 b3.
Proof.
  intros A0 A1 A2 A3. unfold four_bytes_at, byte_at, put_four.
  repeat split.
  - exists aid0. split; [|exact A0].
    repeat rewrite put_byte_elsewhere by lia. apply put_byte_here.
  - exists aid1. split; [|exact A1].
    repeat rewrite put_byte_elsewhere by lia. apply put_byte_here.
  - exists aid2. split; [|exact A2].
    repeat rewrite put_byte_elsewhere by lia. apply put_byte_here.
  - exists aid3. split; [apply put_byte_here|exact A3].
Qed.

Lemma put_four_elsewhere s address other b0 b1 b2 b3 aid0 aid1 aid2 aid3 :
  (other < address \/ address + 4 <= other)%Z ->
  IntMaps.IM.find other
    (bytes (put_four s address b0 b1 b2 b3 aid0 aid1 aid2 aid3)) =
    IntMaps.IM.find other (bytes s).
Proof.
  intro Outside. unfold put_four.
  repeat rewrite put_byte_elsewhere by lia. reflexivity.
Qed.

Lemma write_four_correct s address provenance old0 old1 old2 old3 b0 b1 b2 b3 :
  four_bytes_at s address provenance old0 old1 old2 old3 ->
  exists final,
    run_memory (Impl.write_bytes (address, provenance) [b0; b1; b2; b3]) s =
      Ret (final, tt) /\
    four_bytes_at final address provenance b0 b1 b2 b3 /\
    (forall other, (other < address \/ address + 4 <= other)%Z ->
      IntMaps.IM.find other (bytes final) = IntMaps.IM.find other (bytes s)) /\
    Impl.Memory_stack_frame_stack (Impl.state_memory_stack final) =
      Impl.Memory_stack_frame_stack (Impl.state_memory_stack s) /\
    Impl.Memory_stack_heap (Impl.state_memory_stack final) =
      Impl.Memory_stack_heap (Impl.state_memory_stack s) /\
    Impl.state_provenance final = Impl.state_provenance s.
Proof.
  intros [[aid0 [F0 A0]] [[aid1 [F1 A1]]
    [[aid2 [F2 A2]] [aid3 [F3 A3]]]]].
  exists (put_four s address b0 b1 b2 b3 aid0 aid1 aid2 aid3).
  split.
  - apply memory_steps_sound. eapply write_four_steps; eassumption.
  - split; [apply put_four_contents; assumption|].
    split; [intros; apply put_four_elsewhere; assumption|].
    repeat split; reflexivity.
Qed.
