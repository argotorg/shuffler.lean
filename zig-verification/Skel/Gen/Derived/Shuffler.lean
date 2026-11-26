import Skel.Gen.Derived.ShufflerA
import Skel.Gen.Derived.ShufflerB
import Skel.Gen.Derived.ShufflerC

/-! The derived blocks of the 31 functions of the full shuffler `Lift.Shuffler.Code.code` (SH-C): the block source of `generate` for
the census of the 23 functions that are not in the pilot (`docs/research/shuffler-census-23-20261119.md`). The three parts are
`Skel/Gen/Derived/Shuffler{A,B,C}.lean` (made by `scratch/n16/mkderived.py`). -/

namespace Skel.Gen.Derived

def shuffler : Derived := shufflerA ++ shufflerB ++ shufflerC

end Skel.Gen.Derived
