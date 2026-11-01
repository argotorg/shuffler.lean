module

public import BbuKraken.FlatPlan
import all BbuKraken.FlatPlan

@[expose] public section

namespace Bbu.Flat

-- Restore the ghost values above the physical data buffer.
def restoreData (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) : St :=
  { st with data := Vector.ofFn fun i => if i.val < cap then st.data[i.val] else old[i.val] }

end Bbu.Flat
