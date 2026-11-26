/-! The order of the functions of `skel full` (task FULL-DRV, W10): the call graph, callees first.

A graph is a list of functions, each with the functions that it calls. `levels` puts each function in the first level after the
levels of all its callees: level 0 has the functions with no callee in the graph. A call to a function that is not in the graph
is not an edge. The functions of a call cycle (and their callers) are in no level: `levels` gives them apart. The order inside a
level is the order of the graph. -/

namespace Skel.Full

/-- A call graph: each function with the functions that it calls. -/
abbrev Graph := List (String × List String)

/-- The callees of `f` in `g` that are functions of `g`, with no repeat and not `f` itself. -/
def Graph.callees (g : Graph) (f : String) : List String :=
  (((g.lookup f).getD []).filter fun c => c != f && (g.lookup c).isSome).eraseDups

/-- The functions that call themselves. -/
def Graph.selfCalls (g : Graph) : List String :=
  (g.filter fun (f, cs) => cs.contains f).map (·.1)

/-- The levels of `g`, callees first, and the functions in no level (a call cycle, or a caller of one). -/
def levels (g : Graph) : List (List String) × List String :=
  go g.length [] (g.map (·.1) |>.filter (!g.selfCalls.contains ·)) []
where
  go : Nat → List String → List String → List (List String) → List (List String) × List String
    | 0, _, todo, acc => (acc.reverse, todo ++ g.selfCalls)
    | fuel + 1, done, todo, acc =>
      let ready := todo.filter fun f => (g.callees f).all done.contains
      if ready.isEmpty then (acc.reverse, todo ++ g.selfCalls)
      else go fuel (done ++ ready) (todo.filter (!ready.contains ·)) (ready :: acc)

/-- The functions of `g` in the order of `levels` (callees first), then those in no level. -/
def order (g : Graph) : List String :=
  let (ls, rest) := levels g
  ls.flatten ++ rest

end Skel.Full
