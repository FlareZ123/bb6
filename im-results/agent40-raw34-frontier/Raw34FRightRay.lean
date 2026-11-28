import Raw34D1RDOneStepCore
import RayFinite
import Lean.Elab.Tactic.Omega

/-!
A previously unclassified Raw34 rightward-blank-ray structural family:
D1=0RF or 1RF, and F0=0RF or 1RF.  After the six fixed blank
transitions the head is F at +4 and every cell >=4 is blank.  F0
always writes an arbitrary bit, moves right and returns to F, so F1
is never consulted. This holds for every total completion, including
HALT in any of the six other free entries.
-/
namespace BB6.Agent40Raw34FRightRay
open BB6Coverage BB6.Agent23Raw34Next

def fMask (s : Fin 6) : Bool := decide (s = ⟨5,by decide⟩)
def tables : List (List Nat) := [
  [21,0,22,0,11,0,16,13,0,0,13,0],
  [21,0,22,0,11,0,16,13,0,0,25,0],
  [21,0,22,0,11,0,16,25,0,0,13,0],
  [21,0,22,0,11,0,16,25,0,0,25,0]
]

theorem count : tables.length = 4 := by decide

/-- The source checker simultaneously verifies the true initial six moves,
the pristine right half-ray and the closed F-state blank-motion invariant. -/
theorem checked :
    tables.all (fun code => finiteRayCheck (table code) 6 true fMask) = true := by
  decide

/-- An exact all-time blank-run nonhalting conclusion, arbitrary completions. -/
theorem never (code : List Nat) (hc : code ∈ tables)
    (m : Machine) (hm : compatible (table code) m) : NeverHalts m := by
  have hvalid : finiteRayCheck (table code) 6 true fMask = true :=
    List.all_eq_true.mp checked code hc
  have h := (finiteRayCheck_sound (table code) 6 true fMask 0 hvalid).sound m hm
  rcases h with hn | ⟨n, hn, _⟩
  · exact hn
  · omega

#print axioms count
#print axioms checked
#print axioms never
end BB6.Agent40Raw34FRightRay
