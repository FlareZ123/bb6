import OddOddConeSource
import FullForcedFilter
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0

namespace BB6.Agent2COddOddStrictness

open BB6.Agent46

/-- The former four-gate forced inverse normalizer leaves every target in
    the new 48/64 odd-odd congruence cone untouched. -/
theorem old_normalizer_fixed (x y : Nat)
    (hx : x%8=5) (hy : y%8=3) (hs : (x+y)%64=48) :
    BB6.Agent3.fullForcedNormalize x y = (x,y) := by
  have hodd : ¬ BB6.Agent3.oddLowGate x y := by
    unfold BB6.Agent3.oddLowGate
    omega
  have heven : ¬ BB6.Agent3.evenSevenGate x y := by
    unfold BB6.Agent3.evenSevenGate
    omega
  have haffine : ¬ BB6.Agent3.evenAffineGate x y := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hsix : ¬ BB6.Agent46.sixEvenRightGate x y := by
    unfold BB6.Agent46.sixEvenRightGate
    omega
  unfold BB6.Agent3.fullForcedNormalize
  rw [dif_neg hodd, dif_neg heven, dif_neg haffine, dif_neg hsix]

/-- Strong strictness relative to the already certified four-sector
    one-path inverse normalizer: its Boolean excludes none of the cone. -/
theorem old_filter_misses (x y : Nat)
    (hx : x%8=5) (hy : y%8=3) (hs : (x+y)%64=48) :
    BB6.Agent3.fullForcedExcluded x y = false := by
  have hn := old_normalizer_fixed x y hx hy hs
  unfold BB6.Agent3.fullForcedExcluded
  simp only [hn]
  apply decide_eq_false_iff_not.mpr
  omega

theorem high_stop_old_filter_misses (j m k : Nat)
    (hm5 : 5≤m) (hm4 : m%4=1)
    (hj64 : j%64=(3*m+50)%64)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent3.fullForcedExcluded (2*j+3) k = false := by
  obtain ⟨hx,hy,hs,_⟩ :=
    BB6.Agent2COddOddCone.high_stop_cone_coordinates j m k hm5 hm4 hj64 hstop
  exact old_filter_misses (2*j+3) k hx hy hs

#print axioms old_normalizer_fixed
#print axioms old_filter_misses
#print axioms high_stop_old_filter_misses

end BB6.Agent2COddOddStrictness
