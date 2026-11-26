import Skel.Gen.Model

namespace Skel.Test.LiveInputs
open Skel.Gen

def block (n : Nat) (regs : List (Reg64 × Val)) (term : Term)
    (accesses : List Access := []) : Block :=
  ⟨(Ident.parse s!"b{n}").getD ⟨"b", by decide⟩, n, accesses, regs, term, []⟩

def entry : Block := block 0 [(.rdx, .replaceLow .b8 (.reg .rdx) (.lit 1))] (.exit (.goto 4))

def finish (v : Val) : Block := block 4 [(.rax, v)] (.exit .ret)

def inputs (bs : List Block) (callees : List Callee := []) : List Reg64 :=
  (modelVars bs callees ⟨[], 0⟩).inputs

def checks : List (String × Bool) := [
  ("unused partial register write is not an input", !(inputs [entry, finish (.lit 0)]).contains .rdx),
  ("dead write still has a model field", (modelVars [entry, finish (.lit 0)] [] ⟨[], 0⟩).state.contains .rdx),
  ("used partial register write keeps its input", (inputs [entry, finish (.reg .rdx)]).contains .rdx),
  ("store value keeps its input", (inputs [block 0 [] (.exit .ret)
    [.store 0 (.reg .rdi) .W64 (.reg .rdx)]]).contains .rdx),
  ("store address keeps its input", (inputs [block 0 [] (.exit .ret)
    [.store 0 (.reg .rdx) .W64 (.lit 0)]]).contains .rdx),
  ("load address keeps its input", (inputs [block 0 [(.rax, .load 0)] (.exit .ret)
    [.load 0 (.reg .rdx) .W64]]).contains .rdx),
  ("branch keeps its input", (inputs [block 0 []
    (.branch (.eq (.reg .rdx) (.lit 0)) .ret .ret)]).contains .rdx),
  ("call argument keeps its input", (inputs [block 0 [] (.exit (.call "callee" 4)), finish (.lit 0)]
    [⟨"callee", "C", [.rdx], "C.pc", 0, false, 0, none⟩]).contains .rdx),
  ("read on either branch keeps its input", (inputs [entry,
    block 4 [] (.branch (.eq (.reg .rdi) (.lit 0)) (.goto 8) (.goto 12)),
    block 8 [(.rax, .reg .rdx)] (.exit .ret), block 12 [(.rax, .lit 0)] (.exit .ret)]).contains .rdx),
  ("stack save keeps its input", (inputs [block 0 [(.rdx, .lit 0)] (.exit .ret)
    [.store 0 (.sub (.reg .rsp) (.lit 8)) .W64 (.reg .rdx)]]).contains .rdx),
  ("kept flag condition keeps its input", (inputs [
    { block 0 [] (.exit (.goto 4)) with flags := [(.zf, .eq (.reg .rdx) (.lit 0))] },
    block 4 [(.rax, .lit 0)] (.branch (.flag .zf) .ret .ret)]).contains .rdx),
  ("a flag input alone adds no register input", !(inputs [block 0 [(.rax, .lit 0)]
    (.branch (.flag .zf) .ret .ret)]).contains .rdx),
  ("empty program has no inputs", (inputs []).isEmpty)
]

end Skel.Test.LiveInputs
