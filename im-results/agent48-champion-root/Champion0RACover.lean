import F0SiblingA
import F0Counter0RA
import F0Counter0RA1RF
import Champion0RARD

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent48RA
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt
open BB6.Agent6F0 BB6.Agent6F0.AFirst

theorem ordinary_zeroRA (B : Nat) (hB : 311 ≤ B) (mv : Move) :
    Cover (WeightedBound B) (childA ⟨false,true,0⟩ mv) := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact short_child_A B _ _ 235 (by omega) (by decide)
  · exact short_child_A B _ _ 305 (by omega) (by decide)
  · exact short_child_A B _ _ 225 (by omega) (by decide)
  · exact side_cover B _ 425 78 true 25 (by decide) (by decide)
  · exact BB6.Agent6F0.CounterRA.cover_zeroRA_pair B false
  · exact short_child_A B _ _ 224 (by omega) (by decide)
  · exact side_cover B _ 122 102 true 0 (by decide) (by decide)
  · exact short_child_A B _ _ 224 (by omega) (by decide)
  · exact short_child_A B _ _ 230 (by omega) (by decide)
  · exact short_child_A B _ _ 233 (by omega) (by decide)
  · exact short_child_A B _ _ 239 (by omega) (by decide)
  · exact short_child_A B _ _ 233 (by omega) (by decide)
  · exact short_child_A B _ _ 226 (by omega) (by decide)
  · exact BB6.Agent48RA_RD.cover_zeroRA_zeroRD B
  · exact BB6.Agent6F0.CounterRA.cover_zeroRA_pair B true
  · exact short_child_A B _ _ 241 (by omega) (by decide)
  · exact short_child_A B _ _ 237 (by omega) (by decide)
  · exact side_cover B _ 228 55 true 14 (by decide) (by decide)
  · exact short_child_A B _ _ 227 (by omega) (by decide)
  · exact short_child_A B _ _ 292 (by omega) (by decide)
  · exact short_child_A B _ _ 226 (by omega) (by decide)
  · exact side_cover B _ 124 100 true 1 (by decide) (by decide)
  · exact side_cover B _ 222 2 true 8 (by decide) (by decide)
  · exact BB6.Agent6F0.CounterRF.cover_zeroRA_oneRF B

theorem cover_zeroRA (B : Nat) (hB : 311 ≤ B) :
    Cover (WeightedBound B) (parent ⟨false,true,0⟩) :=
  all_children_A B _ 223 (by omega) (by decide) (ordinary_zeroRA B hB)

#print axioms cover_zeroRA
end BB6.Agent48RA
