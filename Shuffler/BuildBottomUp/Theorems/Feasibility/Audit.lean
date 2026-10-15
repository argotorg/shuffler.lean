import Shuffler.BuildBottomUp.Theorems.Feasibility.Theorems

-- Audit the axioms of each feasibility statement.

/-- info: 'Shuffler.Placement.canPlace_iff_reserve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shuffler.Placement.canPlace_iff_reserve

/-- info: 'Shuffler.Placement.exists_matching_trace_iff_reserve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shuffler.Placement.exists_matching_trace_iff_reserve

/-- info: 'Shuffler.Generate.canGenerate_iff_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shuffler.Generate.canGenerate_iff_ready

/-- info: 'Shuffler.Generate.WithSwaps.canGenerate_iff_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shuffler.Generate.WithSwaps.canGenerate_iff_ready

/-- info: 'Shuffler.Placement.noPopNeeded_iff_exists_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shuffler.Placement.noPopNeeded_iff_exists_trace
