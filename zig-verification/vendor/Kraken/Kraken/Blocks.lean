module

/-
The text of a program, as the control-flow rule reads it.
`Program.fromLabel` is the scope suffix at a label: the text from the label's
cell on. `Program.view` parses the text once into the label-free entry segment
and one `(label, body)` pair per label cell. `Program.blocks` lists the entry
block and one block per label cell.
-/
public import Kraken.Specs

@[expose] public section

open Std.WP
open Lean.Order

/-! ### Runs

`wp` on `Program` is the run: a fall-through past the end of the text lands in
`Q`, and a jump exit at label `l` either surfaces in `E l` or, when `l` is a
label of the program, re-enters at that label's cell. The re-entry closure is
a least fixpoint, taken by `Eventually` inside the definition; no statement
mentions it. -/

/-- The suffix of a program at the last cell carrying `label l`; `[]` when the
program has no such cell. Re-entry at the last occurrence keeps a suffix's
scope a restriction of its host's scope. -/
def Program.fromLabel : Program → Label → Program
  | [], _ => []
  | d :: p, l =>
      if Program.fromLabel p l = [] ∧ d = Directive.label l then d :: p
      else Program.fromLabel p l

@[simp] theorem Program.fromLabel_nil (l : Label) : Program.fromLabel [] l = [] := rfl

@[simp] theorem Program.fromLabel_cons (d : Directive) (p : Program) (l : Label) :
    Program.fromLabel (d :: p) l =
      if Program.fromLabel p l = [] ∧ d = Directive.label l then d :: p
      else Program.fromLabel p l := rfl

/-- An instruction cell is invisible to the scope lookup. -/
@[simp] theorem Program.fromLabel_cons_instr (i : Instr) (p : Program) (l : Label) :
    Program.fromLabel (Directive.instr i :: p) l = Program.fromLabel p l := by
  rw [Program.fromLabel_cons, if_neg (by rintro ⟨-, h⟩; cases h)]

theorem Program.fromLabel_suffix (p : Program) (l : Label) :
    Program.fromLabel p l <:+ p := by
  induction p with
  | nil => exact List.suffix_rfl
  | cons d p ih =>
    rw [Program.fromLabel_cons]
    split
    · exact List.suffix_rfl
    · exact ih.trans (List.suffix_cons d p)

/-- A label with a scope suffix is a cell of the program. -/
theorem Program.fromLabel_mem {p : Program} {l : Label}
    (h : Program.fromLabel p l ≠ []) : Directive.label l ∈ p := by
  induction p with
  | nil => exact absurd rfl h
  | cons d p ih =>
    rw [Program.fromLabel_cons] at h
    by_cases hc : Program.fromLabel p l = [] ∧ d = Directive.label l
    · rw [hc.2]
      exact List.mem_cons_self
    · rw [if_neg hc] at h
      exact List.mem_cons_of_mem d (ih h)

def Directive.isLabel : Directive → Bool
  | .label _ => true
  | _ => false

def Program.straight (p : Program) : Program := p.filter (!·.isLabel)

theorem Program.straight_nil : Program.straight [] = [] := rfl

theorem Program.straight_cons_instr (i : Instr) (p : Program) :
    Program.straight (.instr i :: p) = .instr i :: Program.straight p := rfl

theorem Program.straight_cons_label (l : Label) (p : Program) :
    Program.straight (.label l :: p) = Program.straight p := rfl

theorem Program.straight_cons_byteArray (a : ByteArray) (p : Program) :
    Program.straight (.byteArray a :: p) = .byteArray a :: Program.straight p := rfl

theorem Program.labels_straight (p : Program) : Program.labels (Program.straight p) = [] := by
  induction p with
  | nil => rfl
  | cons d p ih =>
    cases d with
    | label l => rw [Program.straight_cons_label]; exact ih
    | instr i => rw [Program.straight_cons_instr, Program.labels_cons_instr]; exact ih
    | byteArray a => rw [Program.straight_cons_byteArray, Program.labels_cons_byteArray]; exact ih

theorem Program.straight_eq_self {p : Program} (h : ∀ d ∈ p, d.isLabel = false) :
    Program.straight p = p :=
  List.filter_eq_self.mpr fun d hd => by simp [h d hd]

theorem Program.straight_eq_self_of_labels {p : Program} (h : Program.labels p = []) :
    Program.straight p = p :=
  Program.straight_eq_self fun d hd => by
    cases d with
    | label l =>
      have : l ∈ Program.labels p := Program.mem_labels.mpr hd
      rw [h] at this
      cases this
    | instr i => rfl
    | byteArray a => rfl

/-! ### Basic blocks

`Program.view` cuts the text at its label cells. A `Program.Block` is a
label-free body, the label that enters it, and the label it falls into. The
entry segment has no entering label, and the last block falls into no label. -/

/-- A nonempty scope suffix starts with its own label cell. -/
theorem Program.fromLabel_head :
    ∀ (p : Program) {l : Label}, Program.fromLabel p l ≠ [] →
      ∃ rest, Program.fromLabel p l = Directive.label l :: rest := by
  intro p
  induction p with
  | nil => intro l h; exact absurd rfl h
  | cons d p ih =>
    intro l h
    rw [Program.fromLabel_cons] at h ⊢
    by_cases hc : Program.fromLabel p l = [] ∧ d = Directive.label l
    · rw [if_pos hc]
      exact ⟨p, by rw [hc.2]⟩
    · rw [if_neg hc] at h ⊢
      exact ih h

/-- A label present in the text has a scope suffix. -/
theorem Program.fromLabel_ne_nil_of_mem {p : Program} {l : Label}
    (h : l ∈ Program.labels p) : Program.fromLabel p l ≠ [] := by
  induction p with
  | nil => cases h
  | cons d p ih =>
    cases d with
    | label l' =>
      rw [Program.fromLabel_cons]
      split
      · exact List.cons_ne_nil _ _
      · rename_i hc
        simp only [Program.labels_cons_label, List.mem_cons] at h
        rcases h with rfl | h
        · by_cases hnil : Program.fromLabel p l = []
          · exact absurd ⟨hnil, rfl⟩ hc
          · exact hnil
        · exact ih h
    | instr i =>
      rw [Program.fromLabel_cons_instr]
      exact ih h
    | byteArray a =>
      rw [Program.fromLabel_cons, if_neg (fun hc => by cases hc.2)]
      exact ih h

private theorem idxOf_eq_of_getElem? {α} [BEq α] [LawfulBEq α] {xs : List α} {a : α}
    (hnd : xs.Nodup) : ∀ {i : Nat}, xs[i]? = some a → xs.idxOf a = i := by
  induction xs with
  | nil => intro i h; simp at h
  | cons x xs ih =>
    intro i h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hne : (x == a) = false := by
        have hmem : a ∈ xs := List.mem_of_getElem? h
        have hxa : x ≠ a := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ hmem)
        simpa using hxa
      simp only [List.idxOf_cons, hne, Bool.false_eq_true, ite_false]
      rw [ih (List.nodup_cons.mp hnd).2 h]

/-! ### The block view

`Program.view` parses the text once: the label-free entry segment, then one
`(label, body)` pair per label cell, with label-free bodies. The block map and
the control-flow rule read this decomposition; `Program.fromLabel_view`
connects it to the scope suffixes the run semantics traverses. -/

/-- The block decomposition of the text. -/
def Program.view : Program → Program × List (Label × Program)
  | [] => ([], [])
  | .label l :: p => ([], (l, (Program.view p).1) :: (Program.view p).2)
  | d :: p => (d :: (Program.view p).1, (Program.view p).2)

/-- The glue of one block: its label cell, then its body. -/
abbrev Program.blockCells (lb : Label × Program) : Program :=
  Directive.label lb.1 :: lb.2

/-- The text is its entry segment followed by its labeled blocks. -/
theorem Program.view_eq (p : Program) :
    p = (Program.view p).1 ++ ((Program.view p).2.flatMap Program.blockCells) := by
  induction p with
  | nil => rfl
  | cons d p ih =>
    cases d with
    | label l =>
      simp only [Program.view, List.flatMap_cons, List.nil_append, List.cons_append,
        Program.blockCells]
      exact congrArg (Directive.label l :: ·) ih
    | instr i =>
      simp only [Program.view, List.cons_append]
      exact congrArg (Directive.instr i :: ·) ih
    | byteArray a =>
      simp only [Program.view, List.cons_append]
      exact congrArg (Directive.byteArray a :: ·) ih

/-- The entry segment and every body are label-free. -/
theorem Program.view_free (p : Program) :
    (∀ d ∈ (Program.view p).1, d.isLabel = false)
    ∧ ∀ lb ∈ (Program.view p).2, ∀ d ∈ lb.2, d.isLabel = false := by
  induction p with
  | nil => exact ⟨by simp [Program.view], by simp [Program.view]⟩
  | cons d p ih =>
    cases d with
    | label l =>
      refine ⟨by simp [Program.view], fun lb hlb => ?_⟩
      rcases List.mem_cons.mp hlb with heq | hmem
      · rw [heq]
        exact ih.1
      · exact ih.2 lb hmem
    | instr i =>
      refine ⟨fun d' hd' => ?_, ih.2⟩
      rcases List.mem_cons.mp hd' with heq | hmem
      · rw [heq]; rfl
      · exact ih.1 d' hmem
    | byteArray a =>
      refine ⟨fun d' hd' => ?_, ih.2⟩
      rcases List.mem_cons.mp hd' with heq | hmem
      · rw [heq]; rfl
      · exact ih.1 d' hmem

/-- The labels are the view's block labels, in order. -/
theorem Program.labels_view (p : Program) :
    Program.labels p = (Program.view p).2.map (·.1) := by
  induction p with
  | nil => rfl
  | cons d p ih =>
    cases d with
    | label l => simp only [Program.labels_cons_label, Program.view, List.map_cons, ih]
    | instr i => exact ih
    | byteArray a => exact ih

/-- The scope suffix at a label, through the view: the blocks from the
label's position. -/
theorem Program.fromLabel_view {p : Program} (hnd : (Program.labels p).Nodup) :
    ∀ {i : Nat} {l : Label} {b : Program}, (Program.view p).2[i]? = some (l, b) →
      Program.fromLabel p l
        = ((Program.view p).2.drop i).flatMap Program.blockCells := by
  induction p with
  | nil => intro i l b hi; simp [Program.view] at hi
  | cons d p ih =>
    intro i l b hi
    cases d with
    | label l' =>
      simp only [Program.view] at hi
      simp only [Program.labels_cons_label] at hnd
      have hnd' := (List.nodup_cons.mp hnd).2
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        have hnil : Program.fromLabel p l' = [] := by
          by_cases hne : Program.fromLabel p l' = []
          · exact hne
          · exact absurd (Program.mem_labels.mpr (Program.fromLabel_mem hne))
              (List.nodup_cons.mp hnd).1
        rw [Program.fromLabel_cons, if_pos ⟨hnil, rfl⟩]
        simp only [Program.view, List.drop_zero, List.flatMap_cons, Program.blockCells,
          List.cons_append]
        exact congrArg (Directive.label l' :: ·) (Program.view_eq p)
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi
        have hmem : l ∈ Program.labels p := by
          rw [Program.labels_view]
          exact List.mem_map.mpr ⟨(l, b), List.mem_of_getElem? hi, rfl⟩
        have hne : Program.fromLabel p l ≠ [] := Program.fromLabel_ne_nil_of_mem hmem
        rw [Program.fromLabel_cons, if_neg (fun hc => hne hc.1)]
        simp only [Program.view, List.drop_succ_cons]
        exact ih hnd' hi
    | instr i' =>
      simp only [Program.view] at hi
      rw [Program.fromLabel_cons_instr]
      simp only [Program.view]
      exact ih hnd hi
    | byteArray a =>
      simp only [Program.view] at hi
      rw [Program.fromLabel_cons, if_neg (fun hc => by cases hc.2)]
      simp only [Program.view]
      exact ih hnd hi

/-- A basic block: its label, its straight-line body, and the label it falls
into, when one follows. -/
structure Program.Block where
  label : Option Label
  idx : Nat
  body : Program
  next : Option Label
  deriving DecidableEq, Repr

def Program.firstLabel : List (Label × Program) → Option Label
  | [] => none
  | (l, _) :: _ => some l

theorem Program.firstLabel_drop (bs : List (Label × Program)) (i : Nat) :
    Program.firstLabel (bs.drop i) = (bs[i]?).map (·.1) := by
  induction bs generalizing i with
  | nil => simp [Program.firstLabel]
  | cons lb bs ih =>
    obtain ⟨l, b⟩ := lb
    cases i with
    | zero => rfl
    | succ j => simp [ih]

def Program.blockAtAux (j : Nat) : List (Label × Program) → Label → Option Program.Block
  | [], _ => none
  | (l', b) :: bs, l =>
    if l' = l then some ⟨some l, j, b, Program.firstLabel bs⟩
    else Program.blockAtAux (j + 1) bs l

def Program.blockAt (p : Program) (l : Label) : Option Program.Block :=
  Program.blockAtAux 1 (Program.view p).2 l

def Program.entryBlock (p : Program) : Program.Block :=
  ⟨none, 0, (Program.view p).1, Program.firstLabel (Program.view p).2⟩

def Program.blockIdx (p : Program) (l : Label) : Nat :=
  (Program.labels p).idxOf l

theorem Program.isSome_blockAtAux (j : Nat) (bs : List (Label × Program)) (l : Label) :
    (Program.blockAtAux j bs l).isSome = (bs.map (·.1)).contains l := by
  induction bs generalizing j with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨l', b⟩ := b
    by_cases h : l' = l
    · simp [Program.blockAtAux, h]
    · simp only [Program.blockAtAux, h, if_false, ih, List.map_cons, List.contains_cons]
      simp [Ne.symm h]

theorem Program.isSome_blockAt (p : Program) (l : Label) :
    (Program.blockAt p l).isSome = ((Program.view p).2.map (·.1)).contains l :=
  Program.isSome_blockAtAux _ _ l

theorem Program.isSome_blockAt_of_mem {p : Program} {l : Label} (h : l ∈ Program.labels p) :
    (Program.blockAt p l).isSome := by
  rw [Program.isSome_blockAt, ← Program.labels_view]
  exact List.contains_iff_mem.mpr h

theorem Program.blockAtAux_spec : ∀ {j : Nat} {bs : List (Label × Program)} {l : Label}
    {blk : Program.Block}, Program.blockAtAux j bs l = some blk →
    blk.label = some l ∧ ∃ i, bs[i]? = some (l, blk.body)
      ∧ blk.next = Program.firstLabel (bs.drop (i + 1)) ∧ blk.idx = j + i := by
  intro j bs
  induction bs generalizing j with
  | nil => intro l blk h; cases h
  | cons lb bs ih =>
    intro l blk h
    obtain ⟨l', b⟩ := lb
    simp only [Program.blockAtAux] at h
    split at h
    · rename_i hc
      obtain rfl := Option.some.inj h
      subst hc
      exact ⟨rfl, 0, rfl, rfl, rfl⟩
    · obtain ⟨hlab, i, hi, hn, hidx⟩ := ih h
      exact ⟨hlab, i + 1, hi, hn, by rw [hidx]; omega⟩

theorem Program.blockAtAux_of_getElem : ∀ {j : Nat} {bs : List (Label × Program)}
    (_ : (bs.map (·.1)).Nodup) {i : Nat} {l : Label} {b : Program},
    bs[i]? = some (l, b) →
    Program.blockAtAux j bs l = some ⟨some l, j + i, b, Program.firstLabel (bs.drop (i + 1))⟩ := by
  intro j bs
  induction bs generalizing j with
  | nil => intro _ i l b h; simp at h
  | cons lb bs ih =>
    intro hnd i l b h
    obtain ⟨l', b'⟩ := lb
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [Program.blockAtAux]
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      have hmem : l ∈ bs.map (·.1) :=
        List.mem_map.mpr ⟨(l, b), List.mem_of_getElem? h, rfl⟩
      have hne : l' ≠ l := fun heq =>
        (List.nodup_cons.mp (by simpa using hnd)).1 (heq ▸ hmem)
      simp only [Program.blockAtAux, if_neg hne]
      rw [ih (List.nodup_cons.mp (by simpa using hnd)).2 h, Nat.add_assoc, Nat.add_comm 1 k]
      rfl

theorem Program.blockAt_mem_labels {p : Program} {l : Label} {blk : Program.Block}
    (h : Program.blockAt p l = some blk) : l ∈ Program.labels p := by
  obtain ⟨-, i, hi, -, -⟩ := Program.blockAtAux_spec h
  rw [Program.labels_view]
  exact List.mem_map.mpr ⟨(l, blk.body), List.mem_of_getElem? hi, rfl⟩

theorem Program.blockIdx_eq {p : Program} (hnd : (Program.labels p).Nodup)
    {i : Nat} {l : Label} {b : Program} (hi : (Program.view p).2[i]? = some (l, b)) :
    Program.blockIdx p l = i := by
  rw [Program.blockIdx]
  refine idxOf_eq_of_getElem? hnd ?_
  rw [Program.labels_view, List.getElem?_map, hi]
  rfl

theorem Program.blockIdx_eq_of_getElem? {p : Program} (hnd : (Program.labels p).Nodup)
    {i : Nat} {l : Label} (hi : (Program.labels p)[i]? = some l) :
    Program.blockIdx p l = i :=
  idxOf_eq_of_getElem? hnd hi

theorem Program.drop_flatMap_cons {bs : List (Label × Program)} {i : Nat}
    {l : Label} {b : Program} (hi : bs[i]? = some (l, b)) :
    (bs.drop i).flatMap Program.blockCells
      = Directive.label l :: (b ++ (bs.drop (i + 1)).flatMap Program.blockCells) := by
  have hlt : i < bs.length := by
    by_cases h : i < bs.length
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at hi; cases hi
  have hget : bs[i] = (l, b) := by
    have h1 := List.getElem?_eq_getElem hlt
    rw [hi] at h1
    exact (Option.some.inj h1.symm)
  rw [List.drop_eq_getElem_cons hlt, hget, List.flatMap_cons]
  simp only [Program.blockCells, List.cons_append]

theorem Program.fromLabel_split {p : Program} {l : Label}
    (hnd : (Program.labels p).Nodup) (hne : Program.fromLabel p l ≠ []) :
    ∃ t rest, p = t ++ (Directive.label l :: rest)
      ∧ Program.fromLabel p l = Directive.label l :: rest
      ∧ l ∉ Program.labels t
      ∧ t.length = p.length - (Program.fromLabel p l).length := by
  obtain ⟨rest, hr⟩ := Program.fromLabel_head p hne
  obtain ⟨t, ht⟩ := Program.fromLabel_suffix p l
  refine ⟨t, rest, by rw [← ht, hr], hr, ?_, ?_⟩
  · intro hmem
    rw [← ht, Program.labels_append, hr] at hnd
    exact (List.nodup_append.mp hnd).2.2 l hmem l List.mem_cons_self rfl
  · have hlen := congrArg List.length ht
    simp only [List.length_append] at hlen
    omega

abbrev Program.Decreases (var : Label → MachineData → Nat) :
    Option Label → Nat → MachineData → Label → Nat → MachineData → Prop
  | none, _, _, _, _, _ => True
  | some l, i, t, l', j, s => var l' s < var l t ∨ (var l' s = var l t ∧ i < j)

theorem Program.blockAt_next {p : Program} (hnd : (Program.labels p).Nodup)
    {l : Label} {blk : Program.Block} (h : Program.blockAt p l = some blk)
    {l' : Label} (hn : blk.next = some l') :
    (Program.blockAt p l').isSome ∧ Program.blockIdx p l' = Program.blockIdx p l + 1 := by
  obtain ⟨-, i, hi, hnext, -⟩ := Program.blockAtAux_spec h
  rw [hn, Program.firstLabel_drop] at hnext
  have hndv : ((Program.view p).2.map (·.1)).Nodup := by rwa [← Program.labels_view]
  cases hj : (Program.view p).2[i + 1]? with
  | none => rw [hj] at hnext; cases hnext
  | some lb =>
    obtain ⟨l₁, b₁⟩ := lb
    rw [hj] at hnext
    simp only [Option.map_some, Option.some.injEq] at hnext
    subst hnext
    refine ⟨?_, ?_⟩
    · show (Program.blockAtAux 1 (Program.view p).2 l').isSome = true
      rw [Program.blockAtAux_of_getElem hndv hj]
      rfl
    · rw [Program.blockIdx_eq hnd hj, Program.blockIdx_eq hnd hi]

theorem Program.blockIdx_le (p : Program) (l : Label) :
    Program.blockIdx p l ≤ (Program.view p).2.length := by
  have h := List.idxOf_le_length (a := l) (l := Program.labels p)
  have hlen : (Program.labels p).length = (Program.view p).2.length := by
    rw [Program.labels_view, List.length_map]
  rw [hlen] at h
  exact h

def Program.cfgMeasure (p : Program) (var : Label → MachineData → Nat)
    (x : Label × MachineData) : Nat :=
  var x.1 x.2 * ((Program.view p).2.length + 1)
    + ((Program.view p).2.length - Program.blockIdx p x.1)

def Program.blocksFrom (b : Option Label) (j : Nat) (body : Program) :
    List (Label × Program) → List Program.Block
  | [] => [⟨b, j, Program.straight body, none⟩]
  | (l, body') :: bs =>
    ⟨b, j, Program.straight body, some l⟩ :: Program.blocksFrom (some l) (j + 1) body' bs

def Program.blocks (p : Program) : List Program.Block :=
  Program.blocksFrom none 0 (Program.view p).1 (Program.view p).2

theorem Program.mem_blocksFrom_head {b : Option Label} {j : Nat} {body : Program} :
    ∀ {bs : List (Label × Program)},
      ⟨b, j, Program.straight body, Program.firstLabel bs⟩ ∈ Program.blocksFrom b j body bs
  | [] => List.mem_singleton_self _
  | (_, _) :: _ => List.mem_cons_self

theorem Program.mem_blocksFrom_of_blockAtAux {l : Label} {blk : Program.Block} :
    ∀ {bs : List (Label × Program)} {b : Option Label} {j : Nat} {body : Program},
      Program.blockAtAux (j + 1) bs l = some blk →
        ⟨blk.label, blk.idx, Program.straight blk.body, blk.next⟩ ∈ Program.blocksFrom b j body bs
  | [], _, _, _, hb => by cases hb
  | (l', b') :: bs, _, _, _, hb => by
    simp only [Program.blockAtAux] at hb
    refine List.mem_cons_of_mem _ ?_
    split at hb
    · rename_i hc
      subst hc
      cases hb
      exact Program.mem_blocksFrom_head
    · exact Program.mem_blocksFrom_of_blockAtAux hb

theorem Program.entryBlock_mem_blocks (p : Program) : Program.entryBlock p ∈ Program.blocks p := by
  have h := Program.mem_blocksFrom_head (b := none) (j := 0) (body := (Program.view p).1)
    (bs := (Program.view p).2)
  rwa [Program.straight_eq_self (Program.view_free p).1] at h

theorem Program.mem_blocks_of_blockAt {p : Program} {l : Label} {blk : Program.Block}
    (hb : Program.blockAt p l = some blk) : blk ∈ Program.blocks p := by
  have h := Program.mem_blocksFrom_of_blockAtAux (b := none) (j := 0) (body := (Program.view p).1) hb
  obtain ⟨-, i, hi, -, -⟩ := Program.blockAtAux_spec hb
  rwa [Program.straight_eq_self ((Program.view_free p).2 _ (List.mem_of_getElem? hi))] at h

@[vcgen_simp] theorem Program.Block.label_mk (b : Option Label) (j : Nat) (body : Program) (n : Option Label) :
    (⟨b, j, body, n⟩ : Program.Block).label = b := rfl

@[vcgen_simp] theorem Program.Block.idx_mk (b : Option Label) (j : Nat) (body : Program) (n : Option Label) :
    (⟨b, j, body, n⟩ : Program.Block).idx = j := rfl

@[vcgen_simp] theorem Program.Block.body_mk (b : Option Label) (j : Nat) (body : Program) (n : Option Label) :
    (⟨b, j, body, n⟩ : Program.Block).body = body := rfl

@[vcgen_simp] theorem Program.Block.next_mk (b : Option Label) (j : Nat) (body : Program) (n : Option Label) :
    (⟨b, j, body, n⟩ : Program.Block).next = n := rfl

@[vcgen_simp] theorem Program.view_nil : Program.view [] = ([], []) := rfl

@[vcgen_simp] theorem Program.view_cons_label (l : Label) (p : Program) :
    Program.view (.label l :: p) = ([], (l, (Program.view p).1) :: (Program.view p).2) := rfl

@[vcgen_simp] theorem Program.view_cons_instr (i : Instr) (p : Program) :
    Program.view (.instr i :: p) = (.instr i :: (Program.view p).1, (Program.view p).2) := rfl

@[vcgen_simp] theorem Program.view_cons_byteArray (a : ByteArray) (p : Program) :
    Program.view (.byteArray a :: p) = (.byteArray a :: (Program.view p).1, (Program.view p).2) := rfl

@[vcgen_simp] theorem Program.blocks_eq (p : Program) :
    Program.blocks p = Program.blocksFrom none 0 (Program.view p).1 (Program.view p).2 := rfl

@[vcgen_simp] theorem Program.blocksFrom_nil (b : Option Label) (j : Nat) (body : Program) :
    Program.blocksFrom b j body [] = [⟨b, j, Program.straight body, none⟩] := rfl

@[vcgen_simp] theorem Program.blocksFrom_cons (b : Option Label) (j : Nat) (body : Program) (l : Label)
    (body' : Program) (bs : List (Label × Program)) :
    Program.blocksFrom b j body ((l, body') :: bs)
      = ⟨b, j, Program.straight body, some l⟩ :: Program.blocksFrom (some l) (j + 1) body' bs := rfl
