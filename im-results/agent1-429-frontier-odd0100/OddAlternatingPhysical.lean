import W2FullPhysicalMax
import OddAlternatingMax
import Lean.Elab.Tactic.Omega

namespace BB429OddAlternatingPhysical

open BB6Coverage BB429PhysicalFrontier BB429PhysicalBridge
open BB429OddExcursion BB429CZeroEvenReturn BB429OddAlternatingMax
open BB429SourceE1Delta
open BB429DeltaPhysicalBridge BB429W4HeadPrefix BB429W2FullPhysicalMax
open BB429W4HeadMax

/-- The new arbitrary-suffix two-parameter return lifts to the actual
    six-state, two-symbol bi-infinite physical machine. -/
theorem physical_odd_alternating_return
    (m q : Nat) (tail : List Bool) (c : Config)
    (hrep : Represents
      (z 2 (ones (2*m+1) ++ [false] ++ tens (2*q+1) ++ [false] ++ tail)
        false []) c) :
    ∃ c', BB6Coverage.run target429 (4*m+14*q+21) c = some c' ∧
      Represents
        (z 2 ([true,false] ++ ones (2*m+4*q+6) ++ tail) false []) c' ∧
      c'.head = c.head + 3 := by
  have hp := runWithMax_toDelta (4*m+14*q+21)
    (z 2 (ones (2*m+1) ++ [false] ++ tens (2*q+1) ++ [false] ++ tail)
      false [])
  have hd : runWithDelta (4*m+14*q+21)
      (z 2 (ones (2*m+1) ++ [false] ++ tens (2*q+1) ++ [false] ++ tail)
        false []) =
      some (z 2 ([true,false] ++ ones (2*m+4*q+6) ++ tail)
        false [], 3) := by
    rw [odd_alternating_head_max m q tail] at hp
    simpa using hp.symm
  exact source_runWithDelta_rep _ _ c hrep _ _ hd

/-- Every primitive prefix of the physical return stays at or before
    the final head position, exactly three cells beyond entry. -/
theorem physical_odd_alternating_all_prefix_bound
    (m q t : Nat) (tail : List Bool) (c : Config)
    (hrep : Represents
      (z 2 (ones (2*m+1) ++ [false] ++ tens (2*q+1) ++ [false] ++ tail)
        false []) c)
    (ht : t ≤ 4*m+14*q+21) :
    ∃ c', BB6Coverage.run target429 t c = some c' ∧
      c'.head ≤ c.head + 3 := by
  exact physical_runWithMax_bound (4*m+14*q+21) t
    (z 2 (ones (2*m+1) ++ [false] ++ tens (2*q+1) ++ [false] ++ tail)
      false []) c hrep
    (z 2 ([true,false] ++ ones (2*m+4*q+6) ++ tail)
      false [],3,3)
    (odd_alternating_head_max m q tail) ht

#print axioms physical_odd_alternating_return
#print axioms physical_odd_alternating_all_prefix_bound

end BB429OddAlternatingPhysical
