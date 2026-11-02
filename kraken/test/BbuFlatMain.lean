import FlatShuffler.FlatModel

/-!
Run `FlatShuffler.Flat.build_bottom_up` on lines "m n s1 .. sm t1 .. tn d1 .. dm k v1 .. vk" and print one
line for each, in the format of `test/BbuPr31Main.lean`:

- "assertion" for the result -2,
- "ok OPS | STACK | DESTS" if `blocked` gets 0 and 0,
- "blocked OFFSET EXCESS OPS | STACK | DESTS" else,
- "bad input" if a destination is not below n or occurs twice,
- "invalid: ..." if the result is not -2 and not the number of operations.

A value is a number: 0 is junk, 1 a function return label, 2 + 2 id a variable (a `Phi`) and
3 + 2 id a literal (a `Const`), as in `c/bbu_harness.c`. STACK is the values of the slots below
the size and DESTS `m_destinationOf` of each, or "-" for `NONE`. The kraken project builds it as
`bbu_flat`:

  lake exe bbu_flat < states.txt
-/

open FlatShuffler FlatShuffler.Flat

def slotOf (k : Nat) : StackSlot :=
  if k = 0 then .junk
  else if k = 1 then ⟨0, FunctionReturnLabel, Unreachable⟩
  else ⟨.ofNat 32 ((k - 2) / 2), Value, if k % 2 = 1 then Const else 1⟩

def codeOf (s : StackSlot) : Nat :=
  if s.kind = Junk then 0
  else if s.kind = FunctionReturnLabel then 1
  else 2 + 2 * s.payload.toNat + (if s.valueOpcode = Const then 1 else 0)

def opText (o : Op) : String :=
  if o.kind = Swap then s!"s {o.depth.toNat}"
  else if o.kind = Dup then s!"d {o.depth.toNat}"
  else if o.kind = Push ∨ o.kind = Load then s!"p {codeOf o.slot}"
  else s!"? {o.kind.toNat}"

-- `l` from offset 0, and `d` above it.
def vecOf {α : Type} (l : Array α) (d : α) : Vector α maxStackSize := Vector.ofFn fun i => l[i.val]?.getD d

-- Content for the members that the constructor does not initialize.
def uninit : Uninit := ⟨Vector.replicate maxStackSize 7, Vector.replicate maxStackSize 7, 77, 99⟩

def render (r : Word) (st : Flat.St) : String :=
  if r = -2 then "assertion"
  else if r ≠ .ofNat 64 st.trace.length then s!"invalid: the result is {r.toInt}"
  else
    let status :=
      if st.blockedExcess = 0 then
        if st.blockedOffset = 0 then ["ok"] else ["invalid: offset without excess"]
      else ["blocked", toString st.blockedOffset.toNat, toString st.blockedExcess.toNat]
    let below := (List.range st.size.toNat).map (BitVec.ofNat 64)
    let stack := below.map fun i => toString (codeOf (get st.data i))
    let dests := below.map fun i =>
      let d := get st.dest i
      if d = NONE then "-" else toString d.toNat
    " ".intercalate (status ++ st.trace.map opText ++ "|" :: stack ++ "|" :: dests)

def runLine (m n : Nat) (rest : Array Nat) : String :=
  let source := (rest.extract 0 m).map slotOf
  let target := (rest.extract m (m + n)).map slotOf
  let dests := rest.extract (m + n) (2 * m + n)
  let k := rest[2 * m + n]?.getD 0
  let ids := rest.extract (2 * m + n + 1) (2 * m + n + 1 + k)
  let spilled : Array Bool := ids.foldl (fun a i => if i < a.size then a.set! i true else a)
    (Array.replicate (ids.foldl max 0 + 1) false)
  let spills (i : BitVec 32) : BitVec 8 := if spilled[i.toNat]?.getD false then 1 else 0
  if source.size ≠ m ∨ target.size ≠ n ∨ dests.size ≠ m ∨ ids.size ≠ k then "bad input"
  else if dests.any (· ≥ n) ∨ dests.toList.eraseDups.length ≠ m then "bad input"
  else
    match build_bottom_up (.ofNat 64 m) (.ofNat 64 n) (vecOf source .junk) (vecOf target .junk)
        (vecOf (dests.map (BitVec.ofNat 64)) 0) spills uninit with
    | (r, some st) => render r st
    | (r, none) => if r = -2 then "assertion" else s!"invalid: no state, the result is {r.toInt}"

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  match ((line.trimAscii.toString.splitOn " ").filterMap String.toNat?).toArray with
  | a => if h : 2 ≤ a.size then stdout.putStrLn (runLine a[0] a[1] (a.extract 2 a.size))
         else throw <| IO.userError s!"bad line: {line}"
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
