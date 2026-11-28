import Raw34FRightRay
import Lean.Elab.Tactic.Omega

/-!
The complementary left-escaping F oscillator: D1, F0 and F1 all
write arbitrarily and move LEFT into F.  The finite prefix first walks
left over the two inherited 1 cells; by step 9 the head is on a
pristine left ray (state F, head -2). Thereafter only F0 is consulted
and the head strictly decreases. This argument is valid regardless of
the five remaining instructions, including any HALTs.
-/
namespace BB6.Agent40Raw34FLeftRay
open BB6Coverage BB6.Agent23Raw34Next BB6.Agent40Raw34FRightRay

def tables : List (List Nat) := [
  [21,0,22,0,11,0,16,7,0,0,7,7],
  [21,0,22,0,11,0,16,7,0,0,7,19],
  [21,0,22,0,11,0,16,7,0,0,19,7],
  [21,0,22,0,11,0,16,7,0,0,19,19],
  [21,0,22,0,11,0,16,19,0,0,7,7],
  [21,0,22,0,11,0,16,19,0,0,7,19],
  [21,0,22,0,11,0,16,19,0,0,19,7],
  [21,0,22,0,11,0,16,19,0,0,19,19]
]

theorem count : tables.length = 8 := by decide
theorem checked :
    tables.all (fun code => finiteRayCheck (table code) 9 false fMask) = true := by
  decide

theorem never (code : List Nat) (hc : code ∈ tables)
    (m : Machine) (hm : compatible (table code) m) : NeverHalts m := by
  have hvalid : finiteRayCheck (table code) 9 false fMask = true :=
    List.all_eq_true.mp checked code hc
  have h := (finiteRayCheck_sound (table code) 9 false fMask 0 hvalid).sound m hm
  rcases h with hn | ⟨n, hn, _⟩
  · exact hn
  · omega

#print axioms count
#print axioms checked
#print axioms never
end BB6.Agent40Raw34FLeftRay
