module

public import Lift.P2.Total.StackResources

@[expose] public section

namespace Lift.P2.Total.PointerChain

/-- The exact bytes of one data access are outside the hidden frame. -/
def PublicRead (privateByte : BitVec 64 → Bool) (address : BitVec 64)
    (width : Width) : Prop :=
  ∀ i < width.bytes, privateByte (address + BitVec.ofNat 64 i) = false

structure Field where
  offset : BitVec 64
  width : Width

/-- Pointer decoding alone does not assume that the read is permitted. -/
def pointerAt (memory : DataMem) (address : BitVec 64) : Option (BitVec 64) :=
  (Mem.loadInt memory address 8).map (BitVec.ofInt 64)

/-- Nonzero nodes reached by successful pointer reads. Cycles are allowed. -/
inductive Reach (memory : DataMem) (seed link : BitVec 64) : BitVec 64 → Prop where
  | head {node : BitVec 64} (loaded : pointerAt memory seed = some node)
      (nonzero : node ≠ 0#64) : Reach memory seed link node
  | next {node child : BitVec 64} (parent : Reach memory seed link node)
      (loaded : pointerAt memory (node + link) = some child)
      (nonzero : child ≠ 0#64) : Reach memory seed link child

/-- The seed and the listed fields are separate from hidden bytes.
No heap read is required to succeed, and no chain length is assumed. -/
structure Guard (privateByte : BitVec 64 → Bool) (memory : DataMem)
    (seed link : BitVec 64) (fields : List Field) : Prop where
  headOutside : PublicRead privateByte seed .W64
  node : ∀ address, Reach memory seed link address →
    ∀ field ∈ fields, PublicRead privateByte (address + field.offset) field.width

theorem PublicRead.of_disjoint (start address : BitVec 64) (bytes : Nat) (width : Width)
    (separate : ByteDisjoint start bytes address width.bytes) :
    PublicRead (byteRange start bytes) address width := by
  exact fun i hi => byteRange_outside start address bytes width.bytes i separate hi

theorem PublicRead.pointer_eq {privateByte : BitVec 64 → Bool}
    {memory other : DataMem} {address : BitVec 64}
    (outside : PublicRead privateByte address .W64)
    (visible : hideRam privateByte other = hideRam privateByte memory) :
    pointerAt other address = pointerAt memory address := by
  unfold pointerAt
  rw [← hideRam_loadInt privateByte other address 8 outside, visible,
    hideRam_loadInt privateByte memory address 8 outside]

theorem PublicRead.readRam {privateByte : BitVec 64 → Bool}
    {address : BitVec 64} {width : Width}
    (outside : PublicRead privateByte address width) (policy : CpuPolicy) (memory : DataMem) :
    readRam policy (hideRam privateByte memory) address width =
      (readRam policy memory address width).mapError
        (fun failure => (failure.1, hideRam privateByte failure.2)) := by
  simp only [Lift.P2.Total.readRam,
    hideRam_loadInt privateByte memory address width.bytes outside]
  split
  · cases Mem.loadInt memory address width.bytes <;> rfl
  · rfl

theorem pointerAt_of_readRam (policy : CpuPolicy) (memory : DataMem)
    (address node : BitVec 64)
    (loaded : readRam policy memory address .W64 = .ok node) :
    pointerAt memory address = some node := by
  unfold Lift.P2.Total.readRam at loaded
  split at loaded
  · cases raw : Mem.loadInt memory address 8 with
    | none => simp [Width.bytes, raw] at loaded
    | some word =>
      simp only [Width.bytes, raw] at loaded
      have same := Except.ok.inj loaded
      simpa only [pointerAt, raw, Option.map_some] using congrArg some same
  · cases loaded

theorem Reach.nonzero {memory : DataMem} {seed link node : BitVec 64}
    (reachable : Reach memory seed link node) : node ≠ 0#64 := by
  cases reachable with
  | head _ nonzero => exact nonzero
  | next _ _ nonzero => exact nonzero

theorem Reach.congr {memory other : DataMem} {seed link : BitVec 64}
    (headEqual : pointerAt other seed = pointerAt memory seed)
    (nextEqual : ∀ node, Reach memory seed link node →
      pointerAt other (node + link) = pointerAt memory (node + link))
    (node : BitVec 64) : Reach other seed link node ↔ Reach memory seed link node := by
  constructor
  · intro reachable
    induction reachable with
    | head loaded nonzero => exact .head (headEqual ▸ loaded) nonzero
    | next parent loaded nonzero ih =>
      exact .next ih ((nextEqual _ ih) ▸ loaded) nonzero
  · intro reachable
    induction reachable with
    | head loaded nonzero => exact .head (headEqual.symm ▸ loaded) nonzero
    | next parent loaded nonzero ih =>
      exact .next ih ((nextEqual _ parent).symm ▸ loaded) nonzero

theorem Guard.reach_congr {privateByte : BitVec 64 → Bool} {memory other : DataMem}
    {seed link : BitVec 64} {fields : List Field}
    (guard : Guard privateByte memory seed link fields)
    (hasLink : Field.mk link .W64 ∈ fields)
    (visible : hideRam privateByte other = hideRam privateByte memory) (node : BitVec 64) :
    Reach other seed link node ↔ Reach memory seed link node := by
  exact Reach.congr (guard.headOutside.pointer_eq visible)
    (fun address reachable => (guard.node address reachable _ hasLink).pointer_eq visible) node

theorem Guard.congr {privateByte : BitVec 64 → Bool} {memory other : DataMem}
    {seed link : BitVec 64} {fields : List Field}
    (guard : Guard privateByte memory seed link fields)
    (hasLink : Field.mk link .W64 ∈ fields)
    (visible : hideRam privateByte other = hideRam privateByte memory) :
    Guard privateByte other seed link fields := by
  refine ⟨guard.headOutside, ?_⟩
  intro address reachable field member
  exact guard.node address ((guard.reach_congr hasLink visible address).mp reachable) field member

theorem Guard.hide {privateByte : BitVec 64 → Bool} {memory : DataMem}
    {seed link : BitVec 64} {fields : List Field}
    (guard : Guard privateByte memory seed link fields)
    (hasLink : Field.mk link .W64 ∈ fields) :
    Guard privateByte (hideRam privateByte memory) seed link fields := by
  exact guard.congr hasLink (hideRam_idempotent privateByte memory)

theorem Guard.store {privateByte : BitVec 64 → Bool} {memory : DataMem}
    {seed link : BitVec 64} {fields : List Field}
    (guard : Guard privateByte memory seed link fields)
    (hasLink : Field.mk link .W64 ∈ fields) (address : BitVec 64) (bytes : Nat) (value : Int)
    (inside : ∀ i < bytes, privateByte (address + BitVec.ofNat 64 i) = true) :
    Guard privateByte (Mem.storeInt memory address bytes value) seed link fields := by
  exact guard.congr hasLink (hideRam_storeInt privateByte memory address bytes value inside)

theorem Reach.from_tail {memory : DataMem} {seed link node child : BitVec 64}
    (parent : Reach memory seed link node) (tail : Reach memory (node + link) link child) :
    Reach memory seed link child := by
  induction tail with
  | head loaded nonzero => exact .next parent loaded nonzero
  | next prior loaded nonzero ih => exact .next ih loaded nonzero

theorem Guard.tail {privateByte : BitVec 64 → Bool} {memory : DataMem}
    {seed link node : BitVec 64} {fields : List Field}
    (guard : Guard privateByte memory seed link fields)
    (hasLink : Field.mk link .W64 ∈ fields) (parent : Reach memory seed link node) :
    Guard privateByte memory (node + link) link fields := by
  refine ⟨guard.node node parent _ hasLink, ?_⟩
  intro address reachable field member
  exact guard.node address (parent.from_tail reachable) field member

theorem Reach.head_readRam (policy : CpuPolicy) (memory : DataMem)
    (seed link node : BitVec 64)
    (loaded : readRam policy memory seed .W64 = .ok node) (nonzero : node ≠ 0#64) :
    Reach memory seed link node := by
  exact .head (pointerAt_of_readRam policy memory seed node loaded) nonzero

theorem Reach.next_readRam {memory : DataMem} {seed link node child : BitVec 64}
    (parent : Reach memory seed link node) (policy : CpuPolicy)
    (loaded : readRam policy memory (node + link) .W64 = .ok child)
    (nonzero : child ≠ 0#64) : Reach memory seed link child := by
  exact .next parent (pointerAt_of_readRam policy memory (node + link) child loaded) nonzero

/-- Decode a projected successful pointer read in the original memory. -/
theorem PublicRead.pointer_of_projected_readRam {privateByte : BitVec 64 → Bool}
    {memory : DataMem} {address node : BitVec 64}
    (outside : PublicRead privateByte address .W64) (policy : CpuPolicy)
    (loaded : Lift.P2.Total.readRam policy (hideRam privateByte memory) address .W64 = .ok node) :
    pointerAt memory address = some node := by
  have decoded := pointerAt_of_readRam policy (hideRam privateByte memory) address node loaded
  rw [outside.pointer_eq (hideRam_idempotent privateByte memory)] at decoded
  exact decoded

theorem Guard.read_seed {privateByte : BitVec 64 → Bool} {memory : DataMem}
    {seed link : BitVec 64} {fields : List Field}
    (guard : Guard privateByte memory seed link fields) (policy : CpuPolicy) :
    Lift.P2.Total.readRam policy (hideRam privateByte memory) seed .W64 =
      (Lift.P2.Total.readRam policy memory seed .W64).mapError
        (fun failure => (failure.1, hideRam privateByte failure.2)) :=
  guard.headOutside.readRam policy memory

theorem Guard.read_field {privateByte : BitVec 64 → Bool} {memory : DataMem}
    {seed link node : BitVec 64} {fields : List Field}
    (guard : Guard privateByte memory seed link fields) (reachable : Reach memory seed link node)
    (field : Field) (member : field ∈ fields) (policy : CpuPolicy) :
    Lift.P2.Total.readRam policy (hideRam privateByte memory) (node + field.offset) field.width =
      (Lift.P2.Total.readRam policy memory (node + field.offset) field.width).mapError
        (fun failure => (failure.1, hideRam privateByte failure.2)) :=
  (guard.node node reachable field member).readRam policy memory

theorem Guard.head_projected {privateByte : BitVec 64 → Bool} {memory : DataMem}
    {seed link node : BitVec 64} {fields : List Field}
    (guard : Guard privateByte memory seed link fields) (policy : CpuPolicy)
    (loaded : Lift.P2.Total.readRam policy (hideRam privateByte memory) seed .W64 = .ok node)
    (nonzero : node ≠ 0#64) : Reach memory seed link node :=
  .head (guard.headOutside.pointer_of_projected_readRam policy loaded) nonzero

theorem Guard.next_projected {privateByte : BitVec 64 → Bool} {memory : DataMem}
    {seed link node child : BitVec 64} {fields : List Field}
    (guard : Guard privateByte memory seed link fields) (reachable : Reach memory seed link node)
    (hasLink : Field.mk link .W64 ∈ fields) (policy : CpuPolicy)
    (loaded : Lift.P2.Total.readRam policy (hideRam privateByte memory) (node + link) .W64 = .ok child)
    (nonzero : child ≠ 0#64) : Reach memory seed link child :=
  .next reachable ((guard.node node reachable _ hasLink).pointer_of_projected_readRam policy loaded) nonzero

/-- One pointer read selects a chain seed. Only the selected slot is public;
its read can fail, and no array extent is required. -/
structure Prefix (privateByte : BitVec 64 → Bool) (memory : DataMem)
    (root link : BitVec 64) (fields : List Field) : Prop where
  rootOutside : PublicRead privateByte root .W64
  afterRoot : ∀ seed, pointerAt memory root = some seed →
    Guard privateByte memory seed link fields

theorem Prefix.congr {privateByte : BitVec 64 → Bool} {memory other : DataMem}
    {root link : BitVec 64} {fields : List Field}
    (front : Prefix privateByte memory root link fields)
    (hasLink : Field.mk link .W64 ∈ fields)
    (visible : hideRam privateByte other = hideRam privateByte memory) :
    Prefix privateByte other root link fields := by
  refine ⟨front.rootOutside, ?_⟩
  intro seed loaded
  have decoded : pointerAt memory root = some seed := by
    rw [← front.rootOutside.pointer_eq visible]
    exact loaded
  exact (front.afterRoot seed decoded).congr hasLink visible

theorem Prefix.hide {privateByte : BitVec 64 → Bool} {memory : DataMem}
    {root link : BitVec 64} {fields : List Field}
    (front : Prefix privateByte memory root link fields)
    (hasLink : Field.mk link .W64 ∈ fields) :
    Prefix privateByte (hideRam privateByte memory) root link fields :=
  front.congr hasLink (hideRam_idempotent privateByte memory)

theorem Prefix.store {privateByte : BitVec 64 → Bool} {memory : DataMem}
    {root link : BitVec 64} {fields : List Field}
    (front : Prefix privateByte memory root link fields)
    (hasLink : Field.mk link .W64 ∈ fields) (address : BitVec 64) (bytes : Nat) (value : Int)
    (inside : ∀ i < bytes, privateByte (address + BitVec.ofNat 64 i) = true) :
    Prefix privateByte (Mem.storeInt memory address bytes value) root link fields :=
  front.congr hasLink (hideRam_storeInt privateByte memory address bytes value inside)

theorem Prefix.read_root {privateByte : BitVec 64 → Bool} {memory : DataMem}
    {root link : BitVec 64} {fields : List Field}
    (front : Prefix privateByte memory root link fields) (policy : CpuPolicy) :
    Lift.P2.Total.readRam policy (hideRam privateByte memory) root .W64 =
      (Lift.P2.Total.readRam policy memory root .W64).mapError
        (fun failure => (failure.1, hideRam privateByte failure.2)) :=
  front.rootOutside.readRam policy memory

theorem Prefix.after_projected {privateByte : BitVec 64 → Bool} {memory : DataMem}
    {root link seed : BitVec 64} {fields : List Field}
    (front : Prefix privateByte memory root link fields) (policy : CpuPolicy)
    (loaded : Lift.P2.Total.readRam policy (hideRam privateByte memory) root .W64 = .ok seed) :
    Guard privateByte memory seed link fields :=
  front.afterRoot seed (front.rootOutside.pointer_of_projected_readRam policy loaded)

end Lift.P2.Total.PointerChain
