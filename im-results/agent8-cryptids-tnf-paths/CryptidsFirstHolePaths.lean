import FirstHolePath
import CryptidsWeightedLeaves

set_option maxRecDepth 12000
set_option maxHeartbeats 0
namespace BB6.Agent8TNFPath.Cryptids
open BB6Coverage BB6.Cryptids608 BB6.Agent47WeightedHalt

def path_r1 : List (Nat × Slot) :=
  [(1, (1, false)), (2, (2, true)), (3, (3, false)), (4, (2, false)), (5, (4, false)), (7, (1, true)), (10, (4, true)), (11, (5, false)), (49, (0, true)), (52, (5, true))]
def path_r2 : List (Nat × Slot) :=
  [(1, (1, false)), (2, (2, false)), (4, (1, true)), (5, (3, true)), (7, (3, false)), (8, (4, false)), (10, (2, true)), (11, (5, true)), (12, (0, true)), (35, (4, true))]
def path_r3 : List (Nat × Slot) :=
  [(1, (1, false)), (2, (2, false)), (3, (3, false)), (4, (1, true)), (5, (4, false)), (8, (2, true)), (9, (5, true)), (12, (4, true)), (20, (0, true)), (38, (3, true))]
def path_r4 : List (Nat × Slot) :=
  [(1, (1, false)), (2, (2, false)), (3, (3, true)), (4, (4, true)), (8, (4, false)), (9, (3, false)), (10, (0, true)), (13, (1, true)), (14, (2, true)), (15, (5, false))]
def path_r5 : List (Nat × Slot) :=
  [(1, (1, false)), (2, (2, true)), (3, (3, false)), (5, (2, false)), (9, (3, true)), (10, (4, true)), (13, (1, true)), (16, (0, true)), (21, (4, false)), (22, (5, true))]
def path_r6 : List (Nat × Slot) :=
  [(1, (1, false)), (2, (2, false)), (3, (3, true)), (4, (4, true)), (5, (5, false)), (7, (3, false)), (9, (2, true)), (10, (0, true)), (19, (5, true)), (62, (1, true))]

theorem path_r1_checked : pathCheck expectedRLE_r1 BB6.CoverageAdapter.firstOneCylinder 2 path_r1 = true := by decide
theorem path_r1_reachable : FirstHolePath (forgetHaltRows expectedRLE_r1) 6 := checked_from_root _ _ path_r1_checked
#print axioms path_r1_reachable

theorem path_r2_checked : pathCheck expectedRLE_r2 BB6.CoverageAdapter.firstOneCylinder 2 path_r2 = true := by decide
theorem path_r2_reachable : FirstHolePath (forgetHaltRows expectedRLE_r2) 6 := checked_from_root _ _ path_r2_checked
#print axioms path_r2_reachable

theorem path_r3_checked : pathCheck expectedRLE_r3 BB6.CoverageAdapter.firstOneCylinder 2 path_r3 = true := by decide
theorem path_r3_reachable : FirstHolePath (forgetHaltRows expectedRLE_r3) 6 := checked_from_root _ _ path_r3_checked
#print axioms path_r3_reachable

theorem path_r4_checked : pathCheck expectedRLE_r4 BB6.CoverageAdapter.firstOneCylinder 2 path_r4 = true := by decide
theorem path_r4_reachable : FirstHolePath (forgetHaltRows expectedRLE_r4) 6 := checked_from_root _ _ path_r4_checked
#print axioms path_r4_reachable

theorem path_r5_checked : pathCheck expectedRLE_r5 BB6.CoverageAdapter.firstOneCylinder 2 path_r5 = true := by decide
theorem path_r5_reachable : FirstHolePath (forgetHaltRows expectedRLE_r5) 6 := checked_from_root _ _ path_r5_checked
#print axioms path_r5_reachable

theorem path_r6_checked : pathCheck expectedRLE_r6 BB6.CoverageAdapter.firstOneCylinder 2 path_r6 = true := by decide
theorem path_r6_reachable : FirstHolePath (forgetHaltRows expectedRLE_r6) 6 := checked_from_root _ _ path_r6_checked
#print axioms path_r6_reachable
end BB6.Agent8TNFPath.Cryptids
