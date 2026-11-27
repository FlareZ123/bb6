import ThirdImageBroadTwoEdges
import SixForcedNormalize
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent2CThirdBroadStrictness

/-- The existing six-sector normalizer fixes the entire new forbidden
    first-parent residue class: none of its six source gates applies. -/
theorem six_normalizer_parent_fixed (A K : Nat)
    (hA : A%8=0) (hQ : (A+K+1)%64=48) :
    BB6.Agent11SixForced.sixForcedNormalize A K=(A,K) := by
  have hodd : ¬ BB6.Agent3.oddLowGate A K := by
    unfold BB6.Agent3.oddLowGate
    omega
  have heven : ¬ BB6.Agent3.evenSevenGate A K := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have haffine : ¬ BB6.Agent3.evenAffineGate A K := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hsix : ¬ BB6.Agent46.sixEvenRightGate A K := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  have hval : ¬ BB6.Agent3ValSix.valSixGate A K := by
    unfold BB6.Agent3ValSix.valSixGate
    omega
  have hfour : ¬ BB6.Agent11SixForced.evenOddFourGate A K := by
    unfold BB6.Agent11SixForced.evenOddFourGate
    omega
  unfold BB6.Agent11SixForced.sixForcedNormalize
  rw [dif_neg hodd, dif_neg heven, dif_neg haffine,
    dif_neg hsix, dif_neg hval, dif_neg hfour]

/-- On a new I2 minus I3 target, the existing six-sector inverse
    normalizer makes exactly one reduction and stops at the newly
    source-forbidden first parent. -/
theorem six_normalizer_target_parent (x y : Nat)
    (hs : (x+y)%16=4) (hq : (3*(x+y)+2*y)%256=206) (hy5 : 5≤y) :
    BB6.Agent11SixForced.sixForcedNormalize x y =
      ((x+y-4)/2,(x+3*y-10)/4) := by
  have hgate : BB6.Agent3.oddLowGate x y := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hA : ((x+y-4)/2)%8=0 := by omega
  have hQ : (((x+y-4)/2)+((x+3*y-10)/4)+1)%64=48 := by omega
  unfold BB6.Agent11SixForced.sixForcedNormalize
  rw [dif_pos hgate]
  exact six_normalizer_parent_fixed ((x+y-4)/2)
    ((x+3*y-10)/4) hA hQ

/-- The previously strongest six-sector source exclusion always returns
    false on the new image-strict cylinder, although every point in it
    is source-proven unreachable from the genuine blank start. -/
theorem six_filter_misses (x y : Nat)
    (hs : (x+y)%16=4) (hq : (3*(x+y)+2*y)%256=206) (hy5 : 5≤y) :
    BB6.Agent11SixForced.sixForcedExcluded x y=false := by
  have hn := six_normalizer_target_parent x y hs hq hy5
  unfold BB6.Agent11SixForced.sixForcedExcluded
  simp only [hn]
  apply decide_eq_false_iff_not.mpr
  omega

theorem high_stop_six_filter_misses (j m k : Nat)
    (hm6 : 6≤m) (hm4 : m%4=2)
    (hj : j%256=(15*m+222)%256)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent11SixForced.sixForcedExcluded (2*j+3) k=false := by
  obtain ⟨hs,hq,hy5⟩ :=
    BB6.Agent2CThirdBroad.high_stop_coordinates j m k hm6 hm4 hj hstop
  exact six_filter_misses (2*j+3) k hs hq hy5

#print axioms six_normalizer_parent_fixed
#print axioms six_normalizer_target_parent
#print axioms six_filter_misses
#print axioms high_stop_six_filter_misses

end BB6.Agent2CThirdBroadStrictness
