import Skel.Full.GraphJson

open Lean Skel.Gen Skel.Full

def main : IO Unit := do
  let entry : Block := ⟨⟨"entry", by decide⟩, 0, [], [], .branch (.eq (.lit 0) (.lit 0)) (.goto 8) .trap, []⟩
  let call : Block := ⟨⟨"next", by decide⟩, 8, [], [], .exit (.call "callee-label" 16), []⟩
  let ret : Block := ⟨⟨"done", by decide⟩, 16, [], [], .exit .ret, []⟩
  let j := graphJson [("caller-label", "caller", .ok [entry, call, ret]),
                      ("callee-label", "callee", .ok [ret]),
                      ("bad-label", "bad", .error "no blocks")]
  let fs ← IO.ofExcept (j.getObjValAs? (Array Json) "functions")
  unless fs.size == 3 do throw (IO.userError "function count")
  let first := fs[0]!
  unless (first.getObjValAs? (Array String) "callees").toOption == some #["callee"] do
    throw (IO.userError "call graph must resolve function labels")
  let edges ← IO.ofExcept (first.getObjValAs? (Array Json) "edges")
  let nodes ← IO.ofExcept (first.getObjValAs? (Array Json) "blocks")
  unless nodes.any (fun n => (n.getObjValAs? (Array String) "calls").toOption == some #["callee"]) do
    throw (IO.userError "call nodes must name their callees")
  unless edges.size == 4 do throw (IO.userError "branch, continuation and return edges")
  unless edges.any (fun e => (e.getObjValAs? String "label").toOption == some "false") do
    throw (IO.userError "branch labels")
  unless edges.any (fun e => (e.getObjValAs? String "to").toOption == some "next") do
    throw (IO.userError "offsets must resolve to block names")
  unless (fs[2]!.getObjValAs? String "error").toOption == some "no blocks" do
    throw (IO.userError "generation errors must be visible")
  let bad : Block := { entry with term := .exit (.goto 1234) }
  let invalid := graphJson [("broken", "broken", .ok [bad])]
  let bs ← IO.ofExcept (invalid.getObjValAs? (Array Json) "functions")
  unless (bs[0]!.getObjValAs? String "error").toOption.any (!·.isEmpty) do
    throw (IO.userError "a missing target must be reported")
  IO.println "graph JSON: 8 checks passed"
