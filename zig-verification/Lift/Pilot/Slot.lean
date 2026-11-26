module

public import Lift.Trusted.Encode
public import Std.Tactic.BVDecide

@[expose] public section

/-! The packed `StackSlot` of the shuffler, a `packed struct(u64)` in the Zig source. The fields
are in the order of the declaration, the first at the least significant bits: `payload` in bits 0
to 31, `kind` in 32 to 39, `value_opcode` in 40 to 47, `_padding` in 48 to 63. The L3 type of a
slot, its 64-bit word, the decoding of a word, and the facts of the L2⁺ ↔ L3 proof for the word
(`docs/research/pilot-heap-design-20261118.md`, 5.4). -/

namespace Lift.Pilot

open Lift.Trusted

/-- A packed slot. The fields have the widths of their Zig types. The Zig line numbers are those of
`StackSlot` in the shuffler source (`shuffler.zig`, type `packed struct(u64)` at line 78; the field
`payload: u32` at line 80, `kind: Kind` (`enum(u8)`) at line 81, `value_opcode: u8` at line 83, and
`_padding: u16 = 0` at line 85). The offsets and bit sizes agree with `Lift/LLVM/data/shuffler/types.json`
(type 4). -/
structure Slot where
  /-- `payload: u32`, Zig line 80, bits 0 to 31. -/
  payload : BitVec 32
  /-- `kind: Kind` (`enum(u8)`), Zig line 81, bits 32 to 39. -/
  kind : BitVec 8
  /-- `value_opcode: u8`, Zig line 83, bits 40 to 47. -/
  opcode : BitVec 8
  /-- `_padding: u16`, Zig line 85, bits 48 to 63. -/
  pad : BitVec 16
deriving DecidableEq, Inhabited

/-- The 64-bit word of a slot: `pad` is the top 16 bits and `payload` the low 32 bits. -/
def Slot.word (s : Slot) : BitVec 64 := s.pad ++ s.opcode ++ s.kind ++ s.payload

/-- The slot of a word: the inverse of `Slot.word`. Each field is the bit range of its Zig position. -/
def Slot.ofWord (w : BitVec 64) : Slot :=
  ⟨w.extractLsb' 0 32, w.extractLsb' 32 8, w.extractLsb' 40 8, w.extractLsb' 48 16⟩

/-- A slot is one field of 64 bits, its word. -/
instance : Encode Slot where
  encode s := [⟨.W64, s.word⟩]
  decode
    | [⟨.W64, w⟩] => some (Slot.ofWord w)
    | _ => none

/-! ### Facts of the L2⁺ ↔ L3 proof for the word -/

theorem word_ofWord (w : BitVec 64) : (Slot.ofWord w).word = w := by
  simp only [Slot.ofWord, Slot.word]; bv_decide

theorem ofWord_word (p : BitVec 32) (k o : BitVec 8) (d : BitVec 16) :
    Slot.ofWord (Slot.word ⟨p, k, o, d⟩) = ⟨p, k, o, d⟩ := by
  simp only [Slot.ofWord, Slot.word, Slot.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- `shrq $32; testb %cl,%cl` and `movabsq $0xff0000000000; andq; je` of `SpillSet.add`: the
test of the slot passes when its kind is 0 and its opcode is not 0. -/
theorem isVariable_word (p : BitVec 32) (k o : BitVec 8) (d : BitVec 16) :
    (((Slot.word ⟨p, k, o, d⟩ >>> 32).setWidth 8 = 0 ∧
        Slot.word ⟨p, k, o, d⟩ &&& 0xFF0000000000#64 ≠ 0) ↔ (k = 0 ∧ o ≠ 0)) := by
  simp only [Slot.word]; bv_decide

/-- `movl %esi, %ecx`: the payload is the low 32 bits of the word. -/
theorem payload_word (s : Slot) : s.word.setWidth 32 = s.payload := by
  obtain ⟨p, k, o, d⟩ := s; simp only [Slot.word]; bv_decide

/-- `xorq; shlq $16; jne` of `eql` (closestCopy, mapInPlace, shallowestCopyPosition): two slots
are equal in payload, kind and opcode; the padding is not compared. -/
theorem eql_word (a b : Slot) :
    ((a.word ^^^ b.word) <<< 16 = 0) ↔ (a.payload = b.payload ∧ a.kind = b.kind ∧ a.opcode = b.opcode) := by
  obtain ⟨p, k, o, d⟩ := a; obtain ⟨p', k', o', d'⟩ := b; simp only [Slot.word]; bv_decide

/-- `movzbl 4(%rbx,%r9,8)` of closestCopy: byte 4 of the slot word is `kind`. -/
theorem kind_byte (s : Slot) : s.word.extractLsb' 32 8 = s.kind := by
  obtain ⟨p, k, o, d⟩ := s; simp only [Slot.word]; bv_decide

end Lift.Pilot
