import Raw34ERightRay
import Lean.Elab.Tactic.Omega

/-!
Authentic blank-tape left ray in the E state: D1, E0 and E1 all
move left and stay E, writing arbitrary symbols. At entry time nine
the head has crossed the two inherited marked cells and is on the
pristine left half tape. All other five root instructions, including
F0, F1 and potential HALTs, are irrelevant.
The eight sources are E/F-conjugates of accepted F-only left rays.
-/
namespace BB6.Agent40Raw34ELeftRay
open BB6Coverage BB6.Agent23Raw34Next BB6.Agent40Raw34ERightRay

def tables : List (List Nat) := [
  [21,0,22,0,11,0,16,6,6,6,0,0],
  [21,0,22,0,11,0,16,6,6,18,0,0],
  [21,0,22,0,11,0,16,6,18,6,0,0],
  [21,0,22,0,11,0,16,6,18,18,0,0],
  [21,0,22,0,11,0,16,18,6,6,0,0],
  [21,0,22,0,11,0,16,18,6,18,0,0],
  [21,0,22,0,11,0,16,18,18,6,0,0],
  [21,0,22,0,11,0,16,18,18,18,0,0]
]

theorem count : tables.length = 8 := by decide
theorem checked :
    tables.all (fun code => finiteRayCheck (table code) 9 false eMask) = true := by
  decide

theorem never (code : List Nat) (hc : code ∈ tables)
    (m : Machine) (hm : compatible (table code) m) : NeverHalts m := by
  have hh : finiteRayCheck (table code) 9 false eMask = true :=
    List.all_eq_true.mp checked code hc
  have h := (finiteRayCheck_sound (table code) 9 false eMask 0 hh).sound m hm
  rcases h with hn | ⟨n, hn, _⟩
  · exact hn
  · omega

#print axioms count
#print axioms checked
#print axioms never
end BB6.Agent40Raw34ELeftRay
