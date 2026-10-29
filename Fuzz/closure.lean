import Lean

-- Prints the transitive imports of the given module, one per line.
-- Fuzz/build.sh uses this to find the object files to link.
def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules (args.map fun m => { module := m.toName }).toArray {}
  env.header.moduleNames.forM (IO.println ·)
