module

public import Kraken.X64.Semantics

@[expose] public section

namespace Lift.P1

open Kraken

/-- Exact one-step behavior, for every complete machine state. -/
def L1Spec (asm : _root_.Executable) (step : MachineState → Effects) : Prop :=
  ∀ s, step s = asm.step s Effects.done

/-- Shallow code for an address. The PC is fixed by the table key. -/
abbrev Site := Int64 × (MachineData → Effects)

/-- The first entry for a PC wins. An absent PC has Kraken's unchanged-state behavior. -/
def dispatch : List Site → MachineState → Effects
  | [], s => .done s
  | (pc, code) :: rest, s => if s.pc = pc then code s.data else dispatch rest s

/-- Structural address calculation used only while generating code and proofs. -/
def addresses (pc : Int64) : List (Sized Directive) → List (Addressable Directive)
  | [] => []
  | d :: rest => { d with addr := pc } :: addresses (pc + .ofNat d.size) rest

theorem addresses_eq (pc : Int64) (program : List (Sized Directive)) :
    addresses pc program = Kraken.Executable.withAddresses ⟨pc, program⟩ := by
  induction program generalizing pc with
  | nil => rw [Kraken.Executable.withAddresses]; rfl
  | cons d rest ih =>
    rw [Kraken.Executable.withAddresses]
    simp only [addresses, ih]

theorem withAddresses_eq (asm : _root_.Executable) :
    Kraken.Executable.withAddresses asm = addresses asm.1 asm.2 := by
  exact (addresses_eq asm.1 asm.2).symm

/-- A proof reference for the generated table; not the generated runtime. -/
def reference (labels : Labels) : List (Addressable Directive) → List Site
  | [] => []
  | a :: rest =>
    let ds := ((a :: rest).takeWhile (fun d => d.addr = a.addr)).map (·.toSized)
    (a.addr, fun data => @Directives.interp labels ds data a.addr
      (fun pc data => .done ⟨data, pc⟩) (fun pc data => .done ⟨data, pc⟩)) ::
      reference labels rest

theorem dispatch_reference (labels : Labels) (ds : List (Addressable Directive))
    (s : MachineState) :
    dispatch (reference labels ds) s =
      @Directives.interp labels
        (((ds.dropWhile (fun d => d.addr ≠ s.pc)).takeWhile (fun d => d.addr = s.pc)).map (·.toSized))
        s.data s.pc (fun pc data => .done ⟨data, pc⟩) (fun pc data => .done ⟨data, pc⟩) := by
  induction ds with
  | nil => rfl
  | cons a rest ih =>
    by_cases h : s.pc = a.addr
    · simp [reference, dispatch, h]
    · simpa [reference, dispatch, h, Ne.symm h, List.dropWhile_cons] using ih

/-- This reference covers zero-sized directives, repeated PCs, and wrapped addresses. -/
theorem reference_spec (asm : _root_.Executable) :
    L1Spec asm (dispatch (reference asm.labels (Kraken.Executable.withAddresses asm))) := by
  intro s
  exact dispatch_reference asm.labels (Kraken.Executable.withAddresses asm) s

/-- A generated table is accepted only when it equals the reference table. -/
theorem of_table (asm : _root_.Executable) (table : List Site)
    (h : table = reference asm.labels (Kraken.Executable.withAddresses asm)) : L1Spec asm (dispatch table) := by
  rw [h]
  exact reference_spec asm

/-- Kraken label lookup over an already addressed directive list. -/
def labelsFor (ds : List (Kraken.Addressable Directive)) : Labels :=
  { label l := (ds.findSome?
      (fun d => if d.directive = .label l then some d.addr else none)).getD (-1) }

/-- A structural reference permits site-by-site specialization without one large simplification. -/
def structuralReference (asm : _root_.Executable) : List Site :=
  let ds := addresses asm.1 asm.2
  reference (labelsFor ds) ds

theorem structuralReference_eq (asm : _root_.Executable) :
    structuralReference asm = reference asm.labels (Kraken.Executable.withAddresses asm) := by
  simp only [structuralReference, labelsFor, Executable.labels, withAddresses_eq]

theorem of_structural_table (asm : _root_.Executable) (table : List Site)
    (h : table = structuralReference asm) : L1Spec asm (dispatch table) := by
  apply of_table asm table
  exact h.trans (structuralReference_eq asm)

end Lift.P1
