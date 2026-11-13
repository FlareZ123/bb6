import CThreeSixAllCriterion
import M0EvenEvenSumZeroRays
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0SumZeroAll

/-- Strengthen the latest exact six-sector high stopping predicate by
    removing the two source-proven m=0 sum-zero rays. The low branch and
    all prior C58, dyadic, diagonal, m=0, and six-sector filters remain. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11SixAll.highAllowed j m ∧
  ¬(m=0 ∧ j%2048=1895) ∧
  ¬(m=0 ∧ j%8192=359)

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

/-- Lossless exact original-blank Machine C halting iff after excluding
    both newly closed m=0 high-stop families from the latest six-sector
    criterion. Both parameter existentials remain unbounded. -/
theorem blank_halts_iff_six_mzero_sumzero :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11SixAll.lowAllowed m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11SixAll.blank_halts_iff_six_both]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff (2*j+3) k).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_bound j m)
        omega
      have hnot1895 : ¬(m=0 ∧ j%2048=1895) := by
        rintro ⟨hm,hj⟩
        subst m
        exact BB6.Agent11M0SumZero.high_stop_mzero_1895 j k hj hstop hr
      have hnot359 : ¬(m=0 ∧ j%8192=359) := by
        rintro ⟨hm,hj⟩
        subst m
        exact BB6.Agent11M0SumZero.high_stop_mzero_359 j k hj hstop hr
      exact Or.inr ⟨j,m,⟨hprior,hnot1895,hnot359⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_six_mzero_sumzero

end BB6.Agent11M0SumZeroAll


/-- The six-sector normalizer takes exactly the first two forced
    inverses on every odd-t m=0 high target, then stops at the
    even-even sum-zero residual A_t. -/
private theorem six_forced_stops_at_mzero_residual (t : Nat)
    (ht : t%2=1) :
    BB6.Agent11SixForced.sixForcedNormalize
      (17+64*t) (28+96*t) = (26+104*t,18+76*t) := by
  have hx0 : (17+64*t)%2=1 := by omega
  have hy0 : (28+96*t)%2=0 := by omega
  have hnotOdd0 :
      ¬BB6.Agent3.oddLowGate (17+64*t) (28+96*t) := by
    intro h
    simp [BB6.Agent3.oddLowGate, hy0] at h
  have hnotSeven0 :
      ¬BB6.Agent3.evenSevenGate (17+64*t) (28+96*t) := by
    intro h
    simp [BB6.Agent3.evenSevenGate, hx0, hy0] at h
  have hAffine0 :
      BB6.Agent3.evenAffineGate (17+64*t) (28+96*t) := by
    unfold BB6.Agent3.evenAffineGate
    omega
  have hodd1 :
      BB6.Agent3.oddLowGate (43+160*t) (13+48*t) := by
    unfold BB6.Agent3.oddLowGate
    omega
  have hxA : (26+104*t)%2=0 := by omega
  have hyA : (18+76*t)%2=0 := by omega
  have hsumA4 : ((26+104*t)+(18+76*t))%4=0 := by omega
  have hsumA8 : ((26+104*t)+(18+76*t))%8=0 := by omega
  have hxA16 : (26+104*t)%16≠5 := by omega
  have hnotOddA :
      ¬BB6.Agent3.oddLowGate (26+104*t) (18+76*t) := by
    intro h
    simp [BB6.Agent3.oddLowGate, hxA, hyA] at h
  have hnotSevenA :
      ¬BB6.Agent3.evenSevenGate (26+104*t) (18+76*t) := by
    intro h
    simp [BB6.Agent3.evenSevenGate, hxA, hyA] at h
  have hnotAffineA :
      ¬BB6.Agent3.evenAffineGate (26+104*t) (18+76*t) := by
    intro h
    simp [BB6.Agent3.evenAffineGate, hsumA4] at h
  have hnotSixA :
      ¬BB6.Agent46.sixEvenRightGate (26+104*t) (18+76*t) := by
    intro h
    simp [BB6.Agent46.sixEvenRightGate, hsumA8] at h
  have hnotValSixA :
      ¬BB6.Agent3ValSix.valSixGate (26+104*t) (18+76*t) := by
    intro h
    simp [BB6.Agent3ValSix.valSixGate, hxA16] at h
  have hnotEvenOddA :
      ¬BB6.Agent11SixForced.evenOddFourGate
        (26+104*t) (18+76*t) := by
    intro h
    simp [BB6.Agent11SixForced.evenOddFourGate, hxA, hyA] at h
  have hnormA :
      BB6.Agent11SixForced.sixForcedNormalize
        (26+104*t) (18+76*t) = (26+104*t,18+76*t) := by
    simp [BB6.Agent11SixForced.sixForcedNormalize,
      hnotOddA,hnotSevenA,hnotAffineA,hnotSixA,hnotValSixA,hnotEvenOddA]
  simp [BB6.Agent11SixForced.sixForcedNormalize,
    hnotOdd0,hnotSeven0,hAffine0,hodd1,hnormA]

/-- Every odd-t m=0 high target is admitted by the old six-sector
    filter: its normalizer stops at A_t, whose right coordinate is even. -/
private theorem six_forced_admits_mzero_t (t : Nat) (ht : t%2=1) :
    BB6.Agent11SixForced.sixForcedExcluded
      (17+64*t) (28+96*t)=false := by
  have hnorm := six_forced_stops_at_mzero_residual t ht
  have hy : (18+76*t)%2=0 := by omega
  simp [BB6.Agent11SixForced.sixForcedExcluded, hnorm, hy]

/-- Every j=7+32t with odd t survives the entire pre-existing
    six-sector high predicate. The two new ray families are therefore
    genuinely strict removals, not redundant re-statements of old gates. -/
theorem prior_six_all_admits_mzero_odd_t (t : Nat) (ht : t%2=1) :
    BB6.Agent11SixAll.highAllowed (7+32*t) 0 := by
  have hprior :=
    BB6.Agent11M0DeepFull.prior_late_diagonal_admits_mzero_three
      (7+32*t) (by omega)
  have hdeep : BB6.Agent11M0DeepFull.highAllowed (7+32*t) 0 := by
    unfold BB6.Agent11M0DeepFull.highAllowed
      BB6.Agent11DiagonalM0.highAllowed
    exact ⟨⟨hprior,by omega⟩,by omega⟩
  have hforced :
      BB6.Agent11SixForced.sixForcedExcluded
        (2*(7+32*t)+3)
        (2^(2*0+2)*((7+32*t)+3)-((7+32*t)+3*0+5))=false := by
    have hx : 2*(7+32*t)+3=17+64*t := by omega
    have hy :
        2^(2*0+2)*((7+32*t)+3)-((7+32*t)+3*0+5)=28+96*t := by omega
    rw [hx,hy]
    exact six_forced_admits_mzero_t t ht
  change BB6.Agent11M0DeepFull.highAllowed (7+32*t) 0 ∧
    BB6.Agent11SixForced.sixForcedExcluded
      (2*(7+32*t)+3)
      (2^(2*0+2)*((7+32*t)+3)-((7+32*t)+3*0+5))=false
  exact ⟨hdeep,hforced⟩

/-- The j=1895 mod 2048 family was admitted by the old exact six-sector
    criterion and is removed only by the new sum-zero parent argument. -/
theorem sumzero_1895_strict (v : Nat) :
    BB6.Agent11SixAll.highAllowed (1895+2048*v) 0 ∧
    ¬highAllowed (1895+2048*v) 0 := by
  have hprior :=
    prior_six_all_admits_mzero_odd_t (64*v+59) (by omega)
  have hj : 7+32*(64*v+59)=1895+2048*v := by omega
  have hprior' : BB6.Agent11SixAll.highAllowed (1895+2048*v) 0 := by
    simpa only [hj] using hprior
  refine ⟨hprior',?_⟩
  intro h
  exact h.2.1 ⟨rfl,by omega⟩

/-- The j=359 mod 8192 family was admitted by the old exact six-sector
    criterion and is removed only by the new sum-zero parent argument. -/
theorem sumzero_359_strict (w : Nat) :
    BB6.Agent11SixAll.highAllowed (359+8192*w) 0 ∧
    ¬highAllowed (359+8192*w) 0 := by
  have hprior :=
    prior_six_all_admits_mzero_odd_t (256*w+11) (by omega)
  have hj : 7+32*(256*w+11)=359+8192*w := by omega
  have hprior' : BB6.Agent11SixAll.highAllowed (359+8192*w) 0 := by
    simpa only [hj] using hprior
  refine ⟨hprior',?_⟩
  intro h
  exact h.2.2 ⟨rfl,by omega⟩

#print axioms sumzero_1895_strict
#print axioms sumzero_359_strict
