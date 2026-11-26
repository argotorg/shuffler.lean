import Skel.Gen.Model

/-! The head term of a loop head (task MAP-HEAD): the value of a register at the head that is a pure function of the input
registers, constants and the loads of the entry block. Example: `mapInPlace` sets `r15` to the minimum of two loads of the
entry block (`cmovb`), the value `ite (v1 ≤ v0) v1 v0`.

`headTerm` reads the value once and gives its text, or the cause why the value has no term. The text is a `UInt64` over the
input `x.input` (the form of `HeadVal.term`). A load of the entry block is `x.input.heap.load addr w`, `0` when the load
fails: the same form as the sampler text of `HeadVal.load` (`Sampler.headValText`), so the sampler gives a term and a load
the same value. The address of a load is an input register plus constants, as for `HeadVal.load`.

The forms: an input register, a literal, an entry load, `+ - * &&& ||| ^^^`, `~~~`, negation, and `if c then a else b` with
`c` an equation, `≤`, `<` or a negation of these. Any other form (a register that is no input, `rsp`, a stack load, a shift,
a narrow form, a signed compare, a flag) is an error that names it. -/

namespace Skel.Gen

/-- The address is a register other than `rsp`, plus or minus constants. -/
private def regPlusLit : Val → Bool
  | .reg r => r != .rsp
  | .add a (.lit _) | .sub a (.lit _) => regPlusLit a
  | _ => false

mutual
/-- The text of the value `v` at the head, over the inputs `inputs` and the loads of the entry block `entry`. -/
def headTerm (inputs : List Reg64) (entry : List Access) : Val → Except String String
  | .reg r => if inputs.contains r && r != .rsp then .ok s!"x.input.{regLower r}" else .error s!"{regLower r} is no input"
  | .lit n => .ok s!"({n} : UInt64)"
  | .load k =>
    match entry.find? (fun | .load k' .. => k' == k | .store .. => false) with
    | some (.load _ addr w) =>
      if !regPlusLit addr then .error s!"the load {k} is not at a register plus a constant"
      else
        let c : Ctx := ⟨⟨inputs, [], false⟩, "", entry, 0⟩
        let v := if w == .W64 then "v" else "(BitVec.zeroExtend 64 v)"
        .ok s!"(match x.input.heap.load ({(bvText c addr).1}) {widthText w} with | .ok v => UInt64.ofBitVec {v} | _ => 0)"
    | _ => .error s!"the entry block has no load {k}"
  | .add a b => return s!"({← headTerm inputs entry a} + {← headTerm inputs entry b})"
  | .sub a b => return s!"({← headTerm inputs entry a} - {← headTerm inputs entry b})"
  | .mul a b => return s!"({← headTerm inputs entry a} * {← headTerm inputs entry b})"
  | .and a b => return s!"({← headTerm inputs entry a} &&& {← headTerm inputs entry b})"
  | .or a b => return s!"({← headTerm inputs entry a} ||| {← headTerm inputs entry b})"
  | .xor a b => return s!"({← headTerm inputs entry a} ^^^ {← headTerm inputs entry b})"
  | .not a => return s!"(~~~{← headTerm inputs entry a})"
  | .neg a => return s!"(0 - {← headTerm inputs entry a})"
  | .ite c a b => return s!"(if {← headCond inputs entry c} then {← headTerm inputs entry a} else {← headTerm inputs entry b})"
  | _ => .error "a form other than an input, a literal, an entry load, arithmetic and if"

/-- The text of the condition `c` of a head term. -/
def headCond (inputs : List Reg64) (entry : List Access) : Cond → Except String String
  | .eq a b => return s!"{← headTerm inputs entry a} = {← headTerm inputs entry b}"
  | .ule a b => return s!"{← headTerm inputs entry a} ≤ {← headTerm inputs entry b}"
  | .ult a b => return s!"{← headTerm inputs entry a} < {← headTerm inputs entry b}"
  | .not c => return s!"¬ ({← headCond inputs entry c})"
  | _ => .error "a condition other than =, ≤, < and ¬"
end

end Skel.Gen
