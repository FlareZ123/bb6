import W2FullPhysicalMax
import CZeroCensus
import Lean.Elab.Tactic.Omega

namespace BB429Base1000

open BB6Coverage BB429PhysicalFrontier BB429PhysicalBridge
open BB429OddExcursion BB429CZeroEvenReturn BB429W4HeadMax
open BB429W4HeadPrefix BB429SourceE1Delta BB429DeltaPhysicalBridge
open BB429W2FullPhysicalMax BB429W4CZeroCount

/-- Exceptional length-one odd left run, followed by three zeros:
    C/0 reaches a new right frontier exactly four positions farther right,
    preserving every bit of the arbitrary remote left suffix. -/
theorem base1000_head_max (tail : List Bool) :
    runWithMax 16 (z 2 ([true,false,false,false] ++ tail) false []) =
      some (z 2 ([true,true,true,true,true,false,true,true] ++ tail)
        false [],4,4) := by rfl

/-- The sole C/0 instruction start in these 16 original-source steps is
    the initial one; the endpoint is the next C/0. -/
theorem base1000_czero_count (tail : List Bool) :
    runCount 16 (z 2 ([true,false,false,false] ++ tail) false []) =
      some (z 2 ([true,true,true,true,true,false,true,true] ++ tail)
        false [],1) := by rfl

/-- Original six-state infinite-tape lift of the complete C/0 section. -/
theorem physical_base1000_return (tail : List Bool) (c : Config)
    (hrep : Represents (z 2 ([true,false,false,false] ++ tail) false []) c) :
    ∃ d, BB6Coverage.run target429 16 c = some d ∧
      Represents (z 2 ([true,true,true,true,true,false,true,true] ++ tail)
        false []) d ∧ d.head = c.head + 4 := by
  have hp := runWithMax_toDelta 16
    (z 2 ([true,false,false,false] ++ tail) false [])
  rw [base1000_head_max tail] at hp
  have hd : runWithDelta 16
      (z 2 ([true,false,false,false] ++ tail) false []) =
      some (z 2 ([true,true,true,true,true,false,true,true] ++ tail)
        false [],4) := by simpa using hp.symm
  exact source_runWithDelta_rep _ _ c hrep _ _ hd

/-- Whole original physical 16-step prefix never passes the endpoint's
    new right record at head +4. -/
theorem physical_base1000_all_prefix (t : Nat) (tail : List Bool)
    (c : Config)
    (hrep : Represents (z 2 ([true,false,false,false] ++ tail) false []) c)
    (ht : t ≤ 16) :
    ∃ d, BB6Coverage.run target429 t c = some d ∧
      d.head ≤ c.head+4 := by
  exact physical_runWithMax_bound 16 t
    (z 2 ([true,false,false,false] ++ tail) false []) c hrep
    (z 2 ([true,true,true,true,true,false,true,true] ++ tail)
      false [],4,4) (base1000_head_max tail) ht

#print axioms base1000_head_max
#print axioms base1000_czero_count
#print axioms physical_base1000_return
#print axioms physical_base1000_all_prefix
end BB429Base1000
