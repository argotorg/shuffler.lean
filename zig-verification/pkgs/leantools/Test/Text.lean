import LeanTools.Text
import Test.Harness

open LeanTools Test

namespace Test.Text

def replaced (r : Except ReplaceError String) : Option String :=
  match r with
  | .ok s => some s
  | .error _ => none

def failure (r : Except ReplaceError String) : Option ReplaceError :=
  match r with
  | .ok _ => none
  | .error e => some e

def unit : T Unit := do
  -- view
  checkEq "view numbers lines" (view "a\nb\nc") "1\ta\n2\tb\n3\tc\n"
  checkEq "view offset and limit" (view "a\nb\nc\nd" (offset := 2) (limit := some 2)) "2\tb\n3\tc\n[lines 4-4 not shown: view from offset 4]\n"
  checkEq "view offset past the end" (view "a\nb" (offset := 5)) "[the file has 2 lines]\n"
  checkEq "view empty file" (view "") "[the file is empty]\n"
  -- each line here is 7 bytes
  checkEq "view byte cap" (view "aaaa\nbbbb\ncccc" (maxBytes := 12)) "1\taaaa\n[lines 2-3 not shown: view from offset 2]\n"
  checkEq "view byte cap exact" (view "aaaa\nbbbb\ncccc" (maxBytes := 14)) "1\taaaa\n2\tbbbb\n[lines 3-3 not shown: view from offset 3]\n"
  checkEq "view shows one line over the cap" (view "aaaa\nbbbb" (maxBytes := 3)) "1\taaaa\n[lines 2-2 not shown: view from offset 2]\n"
  checkEq "view keeps a final line without newline" (view "a\nb\n") "1\ta\n2\tb\n"
  -- truncate
  checkEq "truncate short" (truncate "abc" 5) "abc"
  checkEq "truncate long" (truncate "abcdef" 4) "abcd\n[2 more characters not shown]"
  -- replace: exact
  checkEq "exact unique" (replaced (replace "x := 1\ny := 2" "y := 2" "y := 3")) (some "x := 1\ny := 3")
  checkEq "exact ambiguous" (failure (replace "a b a" "a" "c")) (some (.ambiguous 2))
  checkEq "replace all" (replaced (replace "a b a" "a" "c" (replaceAll := true))) (some "c b c")
  checkEq "not found" (failure (replace "abc" "x" "y")) (some .notFound)
  checkEq "empty old" (failure (replace "abc" "" "y")) (some .emptyOld)
  checkEq "whitespace-only old" (failure (replace "a  b" "  " "y")) (some .emptyOld)
  -- replace: whitespace-tolerant
  checkEq "tolerant spaces" (replaced (replace "simp  only [h]" "simp only [h]" "omega")) (some "omega")
  checkEq "tolerant newline and indent"
    (replaced (replace "  rw [a]\n    exact b\n" "rw [a]\n  exact b" "omega")) (some "  omega\n")
  checkEq "tolerant needs some whitespace" (failure (replace "ab" "a b" "c")) (some .notFound)
  checkEq "tolerant ambiguous" (failure (replace "a  b\na\tb" "a b" "c")) (some (.ambiguous 2))
  checkEq "exact wins over tolerant" (replaced (replace "a b\na  b" "a b" "c")) (some "c\na  b")
  checkEq "tolerant replace all" (replaced (replace "a  b\na\tb" "a b" "c" (replaceAll := true))) (some "c\nc")
  -- a leading whitespace run matches the whole run once, not once at each of its characters
  checkEq "tolerant leading whitespace" (replaced (replace "x\n    simp" " \tsimp" "omega")) (some "xomega")
  checkEq "tolerant trailing whitespace" (replaced (replace "simp\t \nx" "simp \n" "omega")) (some "omegax")
  checkEq "tolerant inside a token" (replaced (replace "x.push64  ra" ".push64 ra" "!")) (some "x!")
  checkEq "tolerant whitespace reaches the file end"
    (replaced (replace "α\t " "α " "β")) (some "β")
  checkEq "tolerant whitespace is required at the file end"
    (failure (replace "α" "α " "β")) (some .notFound)

/-- Random text over a small alphabet with spaces and newlines, so that substrings repeat. -/
def alphabet : Array Char := #['a', 'b', 'c', ' ', '\n']

structure Case where
  text : String
  start : Nat
  len : Nat
  new : String
deriving Repr

def genCase (g : StdGen) : Case × StdGen :=
  let (text, g) := randString alphabet 40 g
  let (start, g) := below (text.length + 1) g
  let (len, g) := below (text.length - start + 1) g
  let (new, g) := randString alphabet 6 g
  ({ text, start, len, new }, g)

/-- Characters `i ..< i + n` of `s`, and the parts before and from `i`. -/
def sub (s : String) (i n : Nat) : String := String.ofList ((s.toList.drop i).take n)
def pre (s : String) (i : Nat) : String := String.ofList (s.toList.take i)
def post (s : String) (i : Nat) : String := String.ofList (s.toList.drop i)

/-- The start positions of all occurrences of `old`, overlapping ones included. -/
def occurrences (text old : String) : List Nat :=
  (List.range (text.length + 1)).filter fun i => (post text i).startsWith old

/-- `s` with each whitespace run made one space. -/
def norm (s : String) : String :=
  " ".intercalate ((s.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty))

/-- The regions `[i, j)` with non-whitespace ends that equal `old` up to whitespace runs. -/
def tolerantRegions (text old : String) : List (Nat × Nat) :=
  (List.range text.length).flatMap fun i => (List.range (text.length + 1)).filterMap fun j =>
    let r := sub text i (j - i)
    if i < j && !r.front.isWhitespace && !r.back.isWhitespace && norm r == norm old
    then some (i, j) else none

def oldOf (c : Case) : String := sub c.text c.start c.len

def edges (old : String) : Bool :=
  !old.isEmpty && !old.front.isWhitespace && !old.back.isWhitespace

/-- The only occurrence of `old` is replaced in place. -/
def propExact (c : Case) : Bool :=
  let old := oldOf c
  match occurrences c.text old with
  | [i] => old.all Char.isWhitespace ||
      replaced (replace c.text old c.new) == some (pre c.text i ++ c.new ++ post c.text (i + old.length))
  | _ => true

/-- Two or more occurrences, overlapping ones included, make the edit ambiguous. -/
def propAmbiguous (c : Case) : Bool :=
  let old := oldOf c
  let n := (occurrences c.text old).length
  old.all Char.isWhitespace || n < 2 || failure (replace c.text old c.new) == some (.ambiguous n)

/-- Replacing an occurring string by itself, everywhere, gives the text back. -/
def propIdentity (c : Case) : Bool :=
  let old := oldOf c
  match replace c.text old old (replaceAll := true) with
  | .ok s => s == c.text
  | .error .notFound => false
  | .error _ => true

/-- With each whitespace run of `old` widened by one space, a match up to whitespace that is
unique replaces the same region as the exact string. -/
def propTolerant (c : Case) : Bool :=
  let old := oldOf c
  let widened := String.join (old.toList.map fun ch => if ch.isWhitespace then " " ++ ch.toString else ch.toString)
  if !edges old || (occurrences c.text widened).length > 0 then true
  else match tolerantRegions c.text old with
    | [(i, j)] => replaced (replace c.text widened c.new) == some (pre c.text i ++ c.new ++ post c.text j)
    | rs => failure (replace c.text widened c.new) == some (if rs.isEmpty then .notFound else .ambiguous rs.length)

def props : T Unit := do
  forAll "exact replacement" 2000 1 genCase propExact
  forAll "ambiguous replacement" 2000 4 genCase propAmbiguous
  forAll "identity replacement" 2000 2 genCase propIdentity
  forAll "tolerant replacement" 2000 3 genCase propTolerant

def heartbeats : T Unit := do
  checkEq "heartbeats: none" (heartbeatsOver 400000 "theorem t : True := trivial") none
  checkEq "heartbeats: at the cap" (heartbeatsOver 400000 "set_option maxHeartbeats 400000") none
  checkEq "heartbeats: below" (heartbeatsOver 400000 "set_option maxHeartbeats 200000 in\ntheorem t : True := trivial") none
  checkEq "heartbeats: above" (heartbeatsOver 400000 "set_option maxHeartbeats 4000000") (some 4000000)
  checkEq "heartbeats: 0 is no limit" (heartbeatsOver 400000 "set_option maxHeartbeats 0") (some 0)
  checkEq "heartbeats: the first above, of two" (heartbeatsOver 400000
    "set_option maxHeartbeats 100\nset_option maxHeartbeats 500000 in\nexample : True := trivial") (some 500000)
  checkEq "heartbeats: underscores" (heartbeatsOver 400000 "set_option maxHeartbeats 4_000_000") (some 4000000)
  checkEq "heartbeats: other options" (heartbeatsOver 400000 "set_option maxRecDepth 100000") none

/-- Edits that replace one text by another, as `edit_working_file` applies them in one call. -/
def edits : T Unit := do
  let e (o n : String) : Edit := { old := o, new := n }
  checkEq "edits: one edit is a replace" ((applyEdits "x := 1\ny := 2" [e "y := 2" "y := 3"]).toOption) (some "x := 1\ny := 3")
  checkEq "edits: in order, each on the result of the one before"
    ((applyEdits "a b" [e "a" "x", e "x b" "y"]).toOption) (some "y")
  checkEq "edits: the order matters" ((applyEdits "a b" [e "x b" "y", e "a" "x"]).toOption) none
  checkEq "edits: the first that fails is named, with its index from 1"
    (match applyEdits "a b" [e "a" "x", e "zz" "y", e "q" "r"] with | .error (i, err) => some (i, err) | .ok _ => none)
    (some (2, ReplaceError.notFound))
  checkEq "edits: an ambiguous edit fails"
    (match applyEdits "a a" [e "a" "x"] with | .error (i, err) => some (i, err) | .ok _ => none)
    (some (1, ReplaceError.ambiguous 2))
  checkEq "edits: replace all in one edit" ((applyEdits "a a" [{ old := "a", new := "x", all := true }]).toOption) (some "x x")
  checkEq "edits: no edit leaves the text" ((applyEdits "a" []).toOption) (some "a")
  -- the edits of a list applied in two parts, or at once, give the same text
  let alphabet := "abc ".toList.toArray
  forAll "edits: a list is the same as its two parts" 400 21
    (fun g =>
      let (t, g) := randString alphabet 12 g
      let (n1, g) := below 4 g
      let (n2, g) := below 4 g
      let one (g : StdGen) : Edit × StdGen :=
        let (o, g) := randString alphabet 3 g
        let (n, g) := randString alphabet 3 g
        let (all, g) := below 2 g
        ({ old := o, new := n, all := all == 1 }, g)
      let mk (k : Nat) (g : StdGen) : List Edit × StdGen := Id.run do
        let mut g := g
        let mut es := []
        for _ in [0:k] do
          let (x, g') := one g
          g := g'
          es := es ++ [x]
        return (es, g)
      let (es1, g) := mk n1 g
      let (es2, g) := mk n2 g
      ((t, es1.map fun x => (x.old, x.new, x.all), es2.map fun x => (x.old, x.new, x.all)), g))
    fun (t, l1, l2) =>
      let toE := List.map fun (o, n, a) => ({ old := o, new := n, all := a } : Edit)
      (applyEdits t (toE l1 ++ toE l2)).toOption ==
        ((applyEdits t (toE l1)).toOption.bind fun t1 => (applyEdits t1 (toE l2)).toOption)

/-- File-sized whitespace searches exercise the same replacement function as worker edits. -/
def largeEdits : T Unit := do
  let leadingText := String.join (List.replicate 40000 "x  y;")
  let started ← IO.monoMsNow
  checkEq "large edit: absent indented text"
    (failure (replace leadingText "  absent text" "done")) (some .notFound)
  checkEq "large edit: tolerant match at the file end"
    (replaced (replace (leadingText ++ "\t final  goal") "  final goal" "done"))
    (some (leadingText ++ "done"))
  let elapsed := (← IO.monoMsNow) - started
  check "large whitespace edits return within five seconds" (elapsed < 5000) s!"{elapsed} ms"

def suite : T Unit := do unit; props; heartbeats; edits; largeEdits

end Test.Text
