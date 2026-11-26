import Skel.Cfg
import Skel.Gen.Types

/-! The instruction sites of a function of the assembly (`docs/one-way-lift-g1-plan-20261118.md`, section 2.3, task G1-03).
The function is the slice of `Skel.Cfg.sliceFunction`. -/

namespace Skel.Gen

/-- The site of an addressed directive of a function that starts at `entry`: `none` for a label, the site of an
instruction, and `shape` for data. -/
private def siteOf (entry : Int64) (a : Kraken.Addressable Directive) : Except GenError (Option Site) :=
  let offset := (a.addr - entry).toBitVec.toNat
  match a.directive with
  | .label _ => pure none
  | .instr i => pure (some ⟨offset, i⟩)
  | .byteArray _ => throw (.shape offset "data in code")

/-- The sites of the function `entry` of `code`: its instructions in order, each with its offset from the entry label.
The function ends before the first end label (`.Lfunc_end<k>`) after its label. An unknown name, or a name with no end
label after it, is `noFunction`. -/
def sites (code : Executable) (entry : String) : Except GenError (List Site) := do
  let addressed := Kraken.Executable.withAddresses code
  match addressed.dropWhile (·.directive.label? != some entry) with
  | [] => throw (.noFunction entry)
  | start :: rest =>
    let fn ← (Skel.Cfg.sliceFunction (addressed.map (·.directive)) entry).mapError fun _ => GenError.noFunction entry
    let found ← ((start :: rest).take fn.length).mapM (siteOf start.addr)
    pure (found.filterMap id)

end Skel.Gen
