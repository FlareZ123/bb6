import F0SiblingA
import ChampionREReplay
import Champion0RCTriple
import ChampionThreeFAR

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent48Remaining
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt
open BB6.Agent6F0 BB6.Agent6F0.AFirst

theorem ordinary_zeroRC (B : Nat) (hB : 65 ≤ B)
    (hRD : Cover (WeightedBound B) (childA ⟨false,true,2⟩ ⟨false,true,3⟩))
    (mv : Move) : Cover (WeightedBound B) (childA ⟨false,true,2⟩ mv) := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact side_cover B _ 142 90 true 4 (by decide) (by decide)
  · exact side_cover B _ 264 157 true 2 (by decide) (by decide)
  · exact short_child_A B _ _ 59 (by omega) (by decide)
  · exact side_cover B _ 326 182 true 14 (by decide) (by decide)
  · exact short_child_A B _ _ 57 (by omega) (by decide)
  · exact side_cover B _ 224 248 true 2 (by decide) (by decide)
  · exact short_child_A B _ _ 57 (by omega) (by decide)
  · exact side_cover B _ 194 209 true 2 (by decide) (by decide)
  · exact side_cover B _ 52 5 true 6 (by decide) (by decide)
  · exact side_cover B _ 54 3 true 7 (by decide) (by decide)
  · exact side_cover B _ 39 32 true 0 (by decide) (by decide)
  · exact side_cover B _ 169 258 true (-1) (by decide) (by decide)
  · exact side_cover B _ 855 79 true 7 (by decide) (by decide)
  · exact hRD
  · exact BB6.Agent48CounterRC.cover_zeroRC B .ld
  · exact side_cover B _ 401 119 true 19 (by decide) (by decide)
  · exact BB6.Agent48CounterRC.cover_zeroRC B .le
  · exact side_cover B _ 332 186 true 14 (by decide) (by decide)
  · exact side_cover B _ 52 6 true 6 (by decide) (by decide)
  · exact BB6.Agent48CounterRC.cover_zeroRC B .re
  · exact side_cover B _ 202 221 true 2 (by decide) (by decide)
  · exact side_cover B _ 53 4 true 7 (by decide) (by decide)
  · exact side_cover B _ 44 13 true 3 (by decide) (by decide)
  · exact side_cover B _ 53 4 true 7 (by decide) (by decide)

theorem cover_zeroRC_of_RD (B : Nat) (hB : 65 ≤ B)
    (hRD : Cover (WeightedBound B) (childA ⟨false,true,2⟩ ⟨false,true,3⟩)) :
    Cover (WeightedBound B) (parent ⟨false,true,2⟩) :=
  all_children_A B _ 56 (by omega) (by decide) (ordinary_zeroRC B hB hRD)

/-- Table-code equality is checked on all twelve slots, before lifting a FAR proof. -/
theorem liftRE (B i : Nat) (mv : Move)
    (h : (List.finRange 6).all (fun q =>
      [false,true].all (fun b => decide (BB6.Agent48Three.threeTable 19 24 i (q,b) =
        child ⟨true,true,4⟩ mv (q,b)))) = true)
    (hc : Cover NeverHalts (BB6.Agent48Three.threeTable 19 24 i)) :
    Cover (WeightedBound B) (child ⟨true,true,4⟩ mv) := by
  have he : BB6.Agent48Three.threeTable 19 24 i = child ⟨true,true,4⟩ mv := by
    funext s
    rcases s with ⟨q,b⟩
    have hq := List.all_eq_true.mp h q (by simp)
    have hb := List.all_eq_true.mp hq b (by cases b <;> simp)
    exact of_decide_eq_true hb
  rw [← he]
  exact BB6.Agent48Parent.liftNever B hc

theorem ordinary_oneRE (B : Nat) (hB : 12488 ≤ B)
    (hRD : Cover (WeightedBound B) (child ⟨true,true,4⟩ ⟨false,true,3⟩))
    (mv : Move) : Cover (WeightedBound B) (child ⟨true,true,4⟩ mv) := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact short_child B _ _ 6225 (by omega) BB6.Agent48REReplay.r0.checked
  · exact short_child B _ _ 6225 (by omega) BB6.Agent48REReplay.r1.checked
  · exact short_child B _ _ 6225 (by omega) BB6.Agent48REReplay.r2.checked
  · exact short_child B _ _ 6225 (by omega) BB6.Agent48REReplay.r3.checked
  · exact liftRE B 4 _ (by decide) BB6.Agent48Three.far_19_24_4
  · exact liftRE B 5 _ (by decide) BB6.Agent48Three.far_19_24_5
  · exact liftRE B 6 _ (by decide) BB6.Agent48Three.far_19_24_6
  · exact liftRE B 7 _ (by decide) BB6.Agent48Three.far_19_24_7
  · exact liftRE B 8 _ (by decide) BB6.Agent48Three.far_19_24_8
  · exact short_child B _ _ 12482 (by omega) BB6.Agent48REReplay.r9.checked
  · exact liftRE B 10 _ (by decide) BB6.Agent48Three.far_19_24_10
  · exact liftRE B 11 _ (by decide) BB6.Agent48Three.far_19_24_11
  · exact liftRE B 12 _ (by decide) BB6.Agent48Three.far_19_24_12
  · exact hRD
  · exact liftRE B 14 _ (by decide) BB6.Agent48Three.far_19_24_14
  · exact liftRE B 15 _ (by decide) BB6.Agent48Three.far_19_24_15
  · exact liftRE B 16 _ (by decide) BB6.Agent48Three.far_19_24_16
  · exact liftRE B 17 _ (by decide) BB6.Agent48Three.far_19_24_17
  · exact liftRE B 18 _ (by decide) BB6.Agent48Three.far_19_24_18
  · exact liftRE B 19 _ (by decide) BB6.Agent48Three.far_19_24_19
  · exact liftRE B 20 _ (by decide) BB6.Agent48Three.far_19_24_20
  · exact liftRE B 21 _ (by decide) BB6.Agent48Three.far_19_24_21
  · exact liftRE B 22 _ (by decide) BB6.Agent48Three.far_19_24_22
  · exact liftRE B 23 _ (by decide) BB6.Agent48Three.far_19_24_23

theorem cover_oneRE_of_RD (B : Nat) (hB : 12488 ≤ B)
    (hRD : Cover (WeightedBound B) (child ⟨true,true,4⟩ ⟨false,true,3⟩)) :
    Cover (WeightedBound B) (parent ⟨true,true,4⟩) :=
  all_children B _ 6224 (by omega) BB6.Agent48REReplay.parent.checked (ordinary_oneRE B hB hRD)

#print axioms cover_zeroRC_of_RD
#print axioms cover_oneRE_of_RD
end BB6.Agent48Remaining
