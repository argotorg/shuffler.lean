import Shuffler.BuildBottomUp.Optimality.Theorems

open Shuffler.Optimality.BBU

-- The k = 1 and k = 2 edges at the window size and above it.
example : IsGreatest (swapCounts 17 1) 32 :=
  bbuSwapBound_isGreatest 17 1 (by omega) fun _ _ => by decide
example : IsGreatest (swapCounts 16 2) 32 :=
  bbuSwapBound_isGreatest 16 2 (by omega) fun _ _ => by decide
example : IsGreatest (swapCounts 40 2) 34 :=
  bbuSwapBound_isGreatest 40 2 (by omega) fun _ _ => by decide
example : IsGreatest (swapCounts 18 100) 230 :=
  bbuSwapBound_isGreatest 18 100 (by omega) fun _ _ => by decide
-- Inside the window, at n = 3 and n = 15.
example : IsGreatest (swapCounts 3 2) 6 :=
  swapCounts_isGreatest 3 2 (by omega) (by omega) (by decide)
example : IsGreatest (swapCounts 15 20) 66 :=
  swapCounts_isGreatest 15 20 (by omega) (by omega) (by decide)
-- Outside WindowAttained: (3, 3), and (15, 18) with 18 % 16 = 2.
example : ¬ WindowAttained (min 3 17) 3 := by decide
example : ¬ WindowAttained (min 15 17) 18 := by decide
