import W2FullPhysicalMax
import OddCZeroToE1Max
import Lean.Elab.Tactic.Omega

namespace BB429OddCZeroPhysical

open BB6Coverage BB429PhysicalFrontier BB429PhysicalBridge
open BB429OddExcursion BB429CZeroEvenReturn
open BB429OddCZeroToE1Max BB429DeltaPhysicalBridge
open BB429W4HeadPrefix BB429W2FullPhysicalMax BB429W4HeadMax

/-- All-parameter original physical machine odd-frontier extraction.
    An odd positive run of left ones followed by zero leads to E/1 after
    2m+6 primitive instructions, with exact signed head displacement. -/
theorem physical_odd_C0_to_E1 (m : Nat) (tail : List Bool) (c : Config)
    (hrep : Represents (z 2 (ones (2*m+1) ++ (false :: tail)) false []) c) :
    ∃ c', BB6Coverage.run target429 (2*m+6) c = some c' ∧
      Represents (z 4 tail true (true :: tens m ++ [false,true])) c' ∧
      c'.head = c.head - ((2*m+2:Nat):Int) := by
  have hp := runWithMax_toDelta (2*m+6)
    (z 2 (ones (2*m+1) ++ (false :: tail)) false [])
  have hd : runWithDelta (2*m+6)
      (z 2 (ones (2*m+1) ++ (false :: tail)) false []) =
      some (z 4 tail true (true :: tens m ++ [false,true]),
        -((2*m+2:Nat):Int)) := by
    simpa [odd_C0_to_E1_head_max m tail] using hp.symm
  obtain ⟨c',hrun,hrep',hhead⟩ :=
    source_runWithDelta_rep _ _ c hrep _ _ hd
  refine ⟨c',hrun,hrep',?_⟩
  omega

/-- Every genuine primitive head position through the odd-parity
    extraction lies at or before the single right-neighbor boundary. -/
theorem physical_odd_C0_to_E1_prefix_bound (m t : Nat) (tail : List Bool)
    (c : Config)
    (hrep : Represents (z 2 (ones (2*m+1) ++ (false :: tail)) false []) c)
    (ht : t ≤ 2*m+6) :
    ∃ c', BB6Coverage.run target429 t c = some c' ∧
      c'.head ≤ c.head + 1 := by
  exact physical_runWithMax_bound (2*m+6) t
    (z 2 (ones (2*m+1) ++ (false :: tail)) false [])
    c hrep
    (z 4 tail true (true :: tens m ++ [false,true]),
      -((2*m+2:Nat):Int),1)
    (odd_C0_to_E1_head_max m tail) ht

#print axioms physical_odd_C0_to_E1
#print axioms physical_odd_C0_to_E1_prefix_bound
end BB429OddCZeroPhysical
