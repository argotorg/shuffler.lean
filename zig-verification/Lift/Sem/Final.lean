module

public import Lift.Sem.Bridge
public import Lift.Sem.FinalCases

@[expose] public section

/-! The lemmas of the last step of the lift chain (task FINAL-LINK): the proof of a trusted statement `f.Call args objs post`
(or `f.CallB`, or a `Call8` of a statement module) from the row `contract`. The generated text (`Skel/Gen/Final.lean`) uses them
with the frame `[]`:

1. the entry state (`Fn.Entry`, `Fn.EntryB`) gives each conjunct of `l3.rep`: the heap (`holds`), its byte-range permission
   (`permits`), the entry of System V (`Bridge.Fn.Entry.sysV`), the argument registers (`bv64`, `bvw`, `nat64`), the private
   area (`not_covered`) and the stack room (`room`);
2. the row `contract` gives `Reaches` of `l3.post` and `run x = some y`;
3. `ret` gives `Fn.Return` from the exit of System V, the frame of `l3.post` and the statement's `post`.

The lemmas are not about one function. -/

namespace Lift.Sem.Final

open Lift.P2.Total Lift.Trusted Lift.Sem.Bridge

/-- The argument `k` of an entry: the field `x` is in the register `r` when the pair `k` of `args.zip (argRegs s)` is
`(x, r)`. For a list of fields of known length, `rfl` proves `hk`. -/
theorem inReg {args : List Field} {s : MachineState} (h : ArgsIn args s) (k : Nat) {x : Field} {r : UInt64}
    (hk : (args.zip (argRegs s))[k]? = some (x, r)) : x.InReg r :=
  h.2 _ (List.mem_of_getElem? hk)

/-- An argument of 64 bits: the register is the value. -/
theorem bv64 {args : List Field} {s : MachineState} (h : ArgsIn args s) (k : Nat) {v : BitVec 64} {r : UInt64}
    (hk : (args.zip (argRegs s))[k]? = some (⟨.W64, v⟩, r)) : r.toBitVec = v := by
  have := inReg h k hk
  simpa [Field.InReg, Width.bits] using this

/-- An argument of the width `w`: the low `w.bits` bits of the register are the value. -/
theorem bvw (w : Width) {args : List Field} {s : MachineState} (h : ArgsIn args s) (k : Nat) {v : BitVec w.bits}
    {r : UInt64} (hk : (args.zip (argRegs s))[k]? = some (⟨w, v⟩, r)) : r.toBitVec.setWidth w.bits = v :=
  inReg h k hk

/-- An argument `BitVec.ofNat 64 n` with `n < 2 ^ 64`: the register holds `n` as a natural number. -/
theorem nat64 {args : List Field} {s : MachineState} (h : ArgsIn args s) (k : Nat) {n : Nat} {r : UInt64}
    (hk : (args.zip (argRegs s))[k]? = some (⟨.W64, BitVec.ofNat 64 n⟩, r)) (hn : n < 2 ^ 64) : r.toNat = n := by
  have := bv64 h k hk
  rw [UInt64.toNat, this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- The size of an array of words is 8 bytes for each word. -/
theorem size_words (p : BitVec 64) (xs : List (BitVec 64)) (wr : Bool) :
    (⟨p, Encode.encode xs, wr⟩ : Object).size = 8 * xs.length := by
  simp only [Object.size, Encode.encode, List.map_map, Function.comp_def, Width.bytes]
  induction xs with
  | nil => simp
  | cons y ys ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

/-- An array of words that the memory has has fewer than `2 ^ 64` words. -/
theorem length_lt_of_has_words {policy : CpuPolicy} {m : DataMem} {p : BitVec 64} {xs : List (BitVec 64)} {wr : Bool}
    (h : Mem.has policy m ⟨p, Encode.encode xs, wr⟩) : xs.length < 2 ^ 64 := by
  have := h.1
  rw [size_words] at this
  omega

/-- The memory of an entry holds the heap of the objects, with the frame `[]`. -/
theorem holds {f : Fn} {policy : CpuPolicy} {args : List Field} {objs : List Object} {ra : BitVec 64}
    {s : MachineState} (h : f.Entry policy args objs ra s) :
    Heap.Holds policy (objs.map toObj ++ []) s.data.dmem := by
  rw [List.append_nil]
  exact (holds_iff policy objs _).mpr ⟨h.has, h.separate⟩

/-- The policy of an entry of `Fn.CallB` has the byte-range permission of the heap of the objects, with the frame `[]`. -/
theorem permits {f : Fn} {policy : CpuPolicy} {args : List Field} {objs : List Object} {ra : BitVec 64}
    {s : MachineState} (h : f.EntryB policy args objs ra s) : Heap.Permits policy (objs.map toObj ++ []) := by
  rw [List.append_nil]
  exact (permits_iff policy objs).mpr h.2.1

/-- No object of an entry covers a byte of the stack room or of the return word `[rsp - n, rsp + 8)`, with `n = f.room`. The
room is a number `n` with the proof `hn`: the generated text gives the literal of the model text and `rfl`, so that Lean does
not unify `BitVec.ofNat 64 f.room` with the literal. -/
theorem not_covered {f : Fn} {policy : CpuPolicy} {args : List Field} {objs : List Object} {ra : BitVec 64}
    {s : MachineState} (h : f.Entry policy args objs ra s) (n : Nat) (hn : f.room = n) (b : BitVec 64)
    (hb : (b - (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 n)).toNat < n + 8) :
    ¬ Covered (objs.map toObj ++ []) b := by
  subst hn
  rw [List.append_nil]
  rintro ⟨o', ho', hc⟩
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
  obtain ⟨-, -, hsp8⟩ := ret_of_has h.ret
  have hn : f.room ≤ s.data.regs.rsp.toBitVec.toNat := h.room.1
  refine not_covers_of_apart (h.apart o ho) ?_ hb hc
  rw [toNat_sub_ofNat hn]
  change s.data.regs.rsp.toBitVec.toNat + 8 ≤ 2 ^ 64 at hsp8
  omega

/-- No object covers a byte of the stack room below `rsp` (the conjunct of `l3.rep` of a plan with `UpperPlan.hide`,
PIL-HEAP2): the bytes of `SysV.Below` are bytes of `not_covered`. -/
theorem hidden {f : Fn} {policy : CpuPolicy} {args : List Field} {objs : List Object} {ra : BitVec 64}
    {s : MachineState} (h : f.Entry policy args objs ra s) (n : Nat) (hn : f.room = n) :
    ∀ b, SysV.Below s.data.regs.rsp.toBitVec n b → ¬ Covered (objs.map toObj ++ []) b :=
  fun b hb => not_covered h n hn b (by unfold SysV.Below at hb; omega)

/-- The stack room `n = f.room` of an entry (the number `n` as in `not_covered`). -/
theorem room {f : Fn} {policy : CpuPolicy} {args : List Field} {objs : List Object} {ra : BitVec 64}
    {s : MachineState} (h : f.Entry policy args objs ra s) (n : Nat) (hn : f.room = n) : SysV.StackRoom policy s n := by
  subst hn
  obtain ⟨ws, hl, hws⟩ := h.room.2
  exact stackRoom_of_has h.room.1 hl hws

/-- The objects of a heap `objs.map toObj ++ []` that the memory holds. -/
theorem has_of_holds {policy : CpuPolicy} {objs : List Object} {m : DataMem}
    (h : Heap.Holds policy (objs.map toObj ++ []) m) : ∀ o ∈ objs, Mem.has policy m o := by
  rw [List.append_nil] at h
  exact ((holds_iff policy objs m).mp h).1

/-- The return of a call: the exit of System V, the frame (each byte that no writable object owns and that is not in the stack
room `n = f.room` is unchanged, the number `n` as in `not_covered`), and the statement's `post` at the result field of `rax`. -/
theorem ret {f : Fn} {policy : CpuPolicy} {args : List Field} {objs : List Object} {ra : BitVec 64}
    {post : CpuPolicy → Field → DataMem → Prop} {s t : MachineState} (h : f.Entry policy args objs ra s)
    (n : Nat) (hn : f.room = n) (hexit : SysV.Exit s t)
    (hframe : ∀ b, ¬ Heap.Owned (objs.map toObj ++ []) b → ¬ SysV.Below s.data.regs.rsp.toBitVec n b →
      t.data.dmem.get? b = s.data.dmem.get? b)
    (hres : post policy ⟨f.ret, t.data.regs.rax.toBitVec.setWidth f.ret.bits⟩ t.data.dmem) :
    f.Return policy objs post ra s t := by
  subst hn
  obtain ⟨-, hra, -⟩ := ret_of_has h.ret
  refine ⟨pc_of_exit hra hexit, hexit.abi, frame_of_owned h.room.1 fun b ho hb => ?_, hres⟩
  exact hframe b (by rwa [List.append_nil]) hb

/-! ## An argument `BitVec.ofNat 64 n` that the contract does not bound (task FINAL-BOUND)

`nat64` needs `n < 2 ^ 64`. A contract can leave `n` free: `src = [] ∨ n < tgt.length` admits each `n` when `src = []`. Then the
statement is still true when (a) the code does not read the argument, so that the statement for `n` is the statement for
`n % 2 ^ 64`, or (b) the objects bound `n` (`Mem.has` of an array of words bounds its length, `length_lt_of_has_words`). `of_bounded`
proves the statement from its bounded form, with `n < 2 ^ 64` as a hypothesis, and one of the cases. -/

/-- The register value of `BitVec.ofNat 64 n` does not change with `n % 2 ^ 64`. -/
theorem ofNat_mod (n : Nat) : BitVec.ofNat 64 (n % 2 ^ 64) = BitVec.ofNat 64 n := by
  simp [BitVec.ofNat, Fin.ofNat]

/-- `ofNat_mod` with the literal `2 ^ 64`, as `simp` writes it (the rule `Nat.reducePow` runs first). -/
theorem ofNat_mod_lit (n : Nat) : BitVec.ofNat 64 (n % 18446744073709551616) = BitVec.ofNat 64 n :=
  ofNat_mod n

/-- The statement `∀ n, C n → E n → G n` (the contract `C n`, the entry `E n`, the goal `G n`) from its bounded form `hb` (`n < 2 ^ 64`)
and the cases of `n` (`h`): `n < 2 ^ 64` (a bound from the contract or from the objects), or the statement for `n % 2 ^ 64` gives the
statement for `n` (`C` and the entry at `n % 2 ^ 64`, and the goal at `n`: the result does not depend on `n`). The generated text
reverts `n` first, so that the unifier gets `C`, `E` and `G` from the goal. -/
theorem of_bounded {C E G : Nat → Prop} (hb : ∀ m, m < 2 ^ 64 → C m → E m → G m)
    (h : ∀ n, C n → E n →
      n < 2 ^ 64 ∨ (C (n % 2 ^ 64) ∧ (E n → E (n % 2 ^ 64)) ∧ (G (n % 2 ^ 64) → G n))) :
    ∀ n, C n → E n → G n := fun n hC hE =>
  match h n hC hE with
  | .inl hn => hb n hn hC hE
  | .inr ⟨hC', hEE, hGG⟩ => hGG (hb _ (Nat.mod_lt _ (by decide)) hC' (hEE hE))

/-- The goal of a call (`Fn.Call`, `Fn.CallB`) after the entry is introduced depends on the result only through `post`: equal `post`
give the same goal. -/
theorem congr_post {f : Fn} {policy : CpuPolicy} {objs : List Object}
    {post post' : CpuPolicy → Field → DataMem → Prop} {ra : BitVec 64} {s : MachineState} (hp : post = post')
    (h : Reaches (fun s => f.code.step s .done) policy (f.Return policy objs post ra s) s) :
    Reaches (fun s => f.code.step s .done) policy (f.Return policy objs post' ra s) s :=
  hp ▸ h

/-- The sizes of the objects that the memory has: each object has at most `2 ^ 64` bytes. The generated text (`Skel/Gen/Final.lean`)
unfolds the list of the statement's objects and `size_words`, and `omega` bounds the length of an array by it. -/
theorem sizes {policy : CpuPolicy} {m : DataMem} {objs : List Object} (h : ∀ o ∈ objs, Mem.has policy m o) :
    ∀ o ∈ objs, o.size ≤ 2 ^ 64 := fun o ho => by
  have := (h o ho).1
  omega

end Lift.Sem.Final
