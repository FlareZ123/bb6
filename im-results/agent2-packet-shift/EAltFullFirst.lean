import Lean.Elab.Tactic.Omega
import PrefixENoFSource
import EAltBoundaryFirst
import ATurnFamily

set_option maxHeartbeats 20000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EAltFullFirst
open CryptidBoundary
open BB6.Agent2ATurnFamily
open BB6.Agent2EAltBoundaryFirst

def sourceStart (k q r : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+2) true ++
    false::(pairs q ++ (BB6.Agent2ATurnFamily.front (r+1)++ys)))

def sourceEnd (k q r : Nat) (ys : List Bool) : Cfg :=
  ⟨[],false,List.replicate (8*k+3) true ++
    BB6.Agent2EGenericTurn.outPacket q (pairs (r+3)) ys,5⟩

def duration (k q r : Nat) : Nat :=
  12*k*k+49*k+6*(r+1)+62+4*q

/-- Exact earliest physical blank-left F-on-zero return of the original
    six-state table on the unbounded E word
    0(10)^q 11(01)^(r+1)11Y. Every parameter and arbitrary Y are universal.
    The strict physical predicate also detects explicitly padded zero cells. -/
theorem full_E_alternating_first_physical (k q r : Nat)
    (ys : List Bool) :
    run (duration k q r) (sourceStart k q r ys) =
      sourceEnd k q r ys ∧
    ∀ t, 0<t → t<duration k q r →
      ¬ Physical (run t (sourceStart k q r ys)) := by
  constructor
  · simpa [duration,sourceStart,sourceEnd] using
      (BB6.Agent2ATurnFamily.full_E_alternating_family k q r ys)
  · intro t hpos hlt hp
    by_cases hpref : t<12*k*k+41*k+33
    · exact (BB6.CryptidPrefixFirstReturn.prefixE_positive_noF
        k (pairs q ++ (BB6.Agent2ATurnFamily.front (r+1)++ys)) t hpos hpref) hp.1
    · have hprefix : run (12*k*k+41*k+33)
          (sourceStart k q r ys) =
        BB6.Agent2EGenericTurn.eStart (4*k) q (BB6.Agent2ATurnFamily.front (r+1)++ys) := by
        dsimp [sourceStart]
        rw [prefix_E]
        rfl
      have htime : t=(12*k*k+41*k+33)+(t-(12*k*k+41*k+33)) := by
        omega
      have hrest : t-(12*k*k+41*k+33) <
          2*(4*k)+4*q+6*(r+1)+29 := by
        dsimp [duration] at hlt
        omega
      rw [htime,run_add,hprefix] at hp
      exact (boundary_first_physical (4*k) q r ys)
        (t-(12*k*k+41*k+33)) hrest hp

#print axioms full_E_alternating_first_physical
end BB6.Agent2EAltFullFirst
