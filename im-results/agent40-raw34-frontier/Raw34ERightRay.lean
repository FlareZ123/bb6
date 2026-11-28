import Raw34FRightRay
import Lean.Elab.Tactic.Omega

/-!
The E-only complement of the four proven F-only rightward pristine rays:
D1 ∈ {0RE,1RE}, E0 ∈ {0RE,1RE}. Starting from the genuine blank,
the head reaches E at +4 after six steps; only E0 is read thereafter.
E1 and all F transitions may be HALT. This is an ALL-COMPLETION
NeverHalts theorem and is not implied by ten closed-state masks when
the absent E1 instruction happens to HALT.
-/
namespace BB6.Agent40Raw34ERightRay
open BB6Coverage BB6.Agent23Raw34Next

def eMask (s : Fin 6) : Bool := decide (s = ⟨4,by decide⟩)
def tables : List (List Nat) := [
  [21,0,22,0,11,0,16,12,12,0,0,0],
  [21,0,22,0,11,0,16,12,24,0,0,0],
  [21,0,22,0,11,0,16,24,12,0,0,0],
  [21,0,22,0,11,0,16,24,24,0,0,0]
]

theorem count : tables.length = 4 := by decide
theorem checked :
    tables.all (fun code => finiteRayCheck (table code) 6 true eMask) = true := by
  decide

theorem never (code : List Nat) (hc : code ∈ tables)
    (m : Machine) (hm : compatible (table code) m) : NeverHalts m := by
  have hvalid : finiteRayCheck (table code) 6 true eMask = true :=
    List.all_eq_true.mp checked code hc
  have h := (finiteRayCheck_sound (table code) 6 true eMask 0 hvalid).sound m hm
  rcases h with hn | ⟨n, hn, _⟩
  · exact hn
  · omega

#print axioms count
#print axioms checked
#print axioms never
end BB6.Agent40Raw34ERightRay
