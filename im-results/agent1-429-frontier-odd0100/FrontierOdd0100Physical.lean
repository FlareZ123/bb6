import W2FullPhysicalMax
import FrontierOdd0100Max
import Lean.Elab.Tactic.Omega

namespace BB429Odd0100Physical

open BB6Coverage BB429PhysicalFrontier BB429PhysicalBridge
open BB429OddExcursion BB429CZeroEvenReturn BB429Odd0100Max
open BB429SourceE1Delta
open BB429DeltaPhysicalBridge BB429W4HeadPrefix BB429W2FullPhysicalMax
open BB429W4HeadMax

/-- The exact whole-tape raw-machine lift and physical +3 displacement.
    All configurations represented by the stipulated input zipper qualify. -/
theorem physical_odd_0100_return (m : Nat) (tail : List Bool) (c : Config)
    (hrep : Represents
      (z 2 (ones (2*m) ++ [true,false,true,false,false] ++ tail) false []) c) :
    ∃ c', BB6Coverage.run target429 (4*m+21) c = some c' ∧
      Represents
        (z 2 ([true,false] ++ ones (2*m+6) ++ tail) false []) c' ∧
      c'.head = c.head + 3 := by
  have hp := runWithMax_toDelta (4*m+21)
    (z 2 (ones (2*m) ++ [true,false,true,false,false] ++ tail) false [])
  have hd : runWithDelta (4*m+21)
      (z 2 (ones (2*m) ++ [true,false,true,false,false] ++ tail) false []) =
      some (z 2 ([true,false] ++ ones (2*m+6) ++ tail) false [], 3) := by
    simpa [odd_0100_all_head_max m tail] using hp.symm
  exact source_runWithDelta_rep _ _ c hrep _ _ hd

/-- All primitive intermediate raw-machine head positions stay on or left
    of the terminal new right record, three cells past entry. -/
theorem physical_odd_0100_all_prefix_bound (m t : Nat) (tail : List Bool)
    (c : Config)
    (hrep : Represents
      (z 2 (ones (2*m) ++ [true,false,true,false,false] ++ tail) false []) c)
    (ht : t ≤ 4*m+21) :
    ∃ c', BB6Coverage.run target429 t c = some c' ∧
      c'.head ≤ c.head + 3 := by
  exact physical_runWithMax_bound (4*m+21) t
    (z 2 (ones (2*m) ++ [true,false,true,false,false] ++ tail) false [])
    c hrep
    (z 2 ([true,false] ++ ones (2*m+6) ++ tail) false [],3,3)
    (odd_0100_all_head_max m tail) ht

#print axioms physical_odd_0100_return
#print axioms physical_odd_0100_all_prefix_bound
end BB429Odd0100Physical
