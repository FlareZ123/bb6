import ValSixMixedNormalize
import EvenOddFourExact
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11SixForced
open BB6.Agent46 BB6.Agent3

/-- Entire source-exact even-left/odd-right valuation-two return sector,
    discovered in Agent3's EvenOddFourExact.lean but absent from the
    previous mixed five-sector recursive normalizer. -/
def evenOddFourGate (x y : Nat) : Prop :=
  x%2=0 ∧ y%2=1 ∧ 5≤y ∧ (x+y+1)%8=4

instance evenOddFourGate_decidable (x y : Nat) :
    Decidable (evenOddFourGate x y) := by
  unfold evenOddFourGate
  infer_instance

/-- Extended source-exact normalization: the existing five inverse
    regions, plus the new even/odd valuation-two sector. Every step
    decreases the weighted rank x+2y by at least four, including the
    newly introduced branch, so this is truly unbounded and total. -/
def sixForcedNormalize (x y : Nat) : Nat × Nat :=
  if h : oddLowGate x y then
    sixForcedNormalize ((x+y-4)/2) ((x+3*y-10)/4)
  else if he : evenSevenGate x y then
    sixForcedNormalize ((x+y-5)/2) ((x+3*y-9)/4)
  else if hf : evenAffineGate x y then
    sixForcedNormalize (x+y-2) ((y-2)/2)
  else if hs : sixEvenRightGate x y then
    sixForcedNormalize (x+y-2) ((y-2)/2)
  else if hv : BB6.Agent3ValSix.valSixGate x y then
    sixForcedNormalize (x+y-2) ((y-2)/2)
  else if hfour : evenOddFourGate x y then
    sixForcedNormalize ((x+y-5)/2) ((x+3*y-9)/4)
  else (x,y)
termination_by x+2*y
decreasing_by
  all_goals
    simp_wf
    simp only [oddLowGate, evenSevenGate, evenAffineGate,
      sixEvenRightGate, BB6.Agent3ValSix.valSixGate,evenOddFourGate] at *
    omega

/-- All six reductions are genuine source transitions: at *every*
    time, blank reachability of an arbitrary state is equivalent to
    reachability of its fully normalized ancestor. -/
theorem sixForcedNormalize_reach_iff (x y : Nat) :
    CReach x y ↔ CReach (sixForcedNormalize x y).1
                        (sixForcedNormalize x y).2 := by
  generalize hz : x+2*y=z
  induction z using Nat.strongRecOn generalizing x y with
  | ind z ih =>
      unfold sixForcedNormalize
      by_cases hg : oddLowGate x y
      · rw [dif_pos hg]
        rcases hg with ⟨hx,hy,hy5,h4,h16,hsize⟩
        have hh := oddodd_lowval_blank_reach_iff x y hx hy hy5 h4 h16 hsize
        have hlt : ((x+y-4)/2)+2*((x+3*y-10)/4)<z := by omega
        have hrec := ih _ hlt ((x+y-4)/2) ((x+3*y-10)/4) (by rfl)
        exact hh.trans hrec
      · rw [dif_neg hg]
        by_cases he : evenSevenGate x y
        · rw [dif_pos he]
          rcases he with ⟨hx,hy,hy5,hseven,hsize⟩
          have hh := odd_seven_blank_reach_iff x y hx hy hy5 hseven hsize
          have hlt : ((x+y-5)/2)+2*((x+3*y-9)/4)<z := by omega
          have hrec := ih _ hlt ((x+y-5)/2) ((x+3*y-9)/4) (by rfl)
          exact hh.trans hrec
        · rw [dif_neg he]
          by_cases hf : evenAffineGate x y
          · rw [dif_pos hf]
            rcases hf with ⟨hy,heven,hs⟩
            have hh := BB6.Agent15.blank_reach_iff_affine x y hy heven hs
            have hlt : x+y-2+2*((y-2)/2)<z := by omega
            have hrec := ih _ hlt (x+y-2) ((y-2)/2) (by rfl)
            exact hh.trans hrec
          · rw [dif_neg hf]
            by_cases hs : sixEvenRightGate x y
            · rw [dif_pos hs]
              rcases hs with ⟨hy,heven,h0,h7⟩
              have hh := six_even_right_blank_reach_iff x y hy heven h0 h7
              have hlt : x+y-2+2*((y-2)/2)<z := by omega
              have hrec := ih _ hlt (x+y-2) ((y-2)/2) (by rfl)
              exact hh.trans hrec
            · rw [dif_neg hs]
              by_cases hv : BB6.Agent3ValSix.valSixGate x y
              · rw [dif_pos hv]
                rcases hv with ⟨hx,hy,hmod⟩
                have hh := BB6.Agent3ValSix.second_val_six_root_iff
                  x y hx hy hmod
                have hlt : x+y-2+2*((y-2)/2)<z := by omega
                have hrec := ih _ hlt (x+y-2) ((y-2)/2) (by rfl)
                exact hh.trans hrec
              · rw [dif_neg hv]
                by_cases hfou : evenOddFourGate x y
                · rw [dif_pos hfou]
                  rcases hfou with ⟨hx,hy,hy5,hmod⟩
                  have hh := evenodd_four_blank_reach_iff x y
                    hx hy hy5 hmod
                  have hlt : ((x+y-5)/2)+2*((x+3*y-9)/4)<z := by omega
                  have hrec := ih _ hlt ((x+y-5)/2) ((x+3*y-9)/4) (by rfl)
                  exact hh.trans hrec
                · rw [dif_neg hfou]

/-- Source-exact fixed-target decision, with the complete six-sector
    predecessor normalization and a finite half-rank root test. -/
def sixForcedRootDecision (x y : Nat) : Bool :=
  let p := sixForcedNormalize x y
  BB6.Agent11Fast.backwardFastFuel ((p.1+2*p.2)/2) p

theorem sixForcedRootDecision_iff (x y : Nat) :
    sixForcedRootDecision x y = true ↔ CReach x y := by
  unfold sixForcedRootDecision
  have hh := BB6.Agent11Fast.backwardFastFuelHalfFull_iff
    (sixForcedNormalize x y).1 (sixForcedNormalize x y).2
  change _ ↔ CReach (sixForcedNormalize x y).1
                        (sixForcedNormalize x y).2 at hh
  exact hh.trans (sixForcedNormalize_reach_iff x y).symm

/-- A uniform decidable sufficient nonreachability predicate: no cutoff
    or finite orbit sample, valid for arbitrarily large target counters. -/
def sixForcedExcluded (x y : Nat) : Bool :=
  let p := sixForcedNormalize x y
  decide (5≤p.2 ∧ p.2%2=1 ∧
    ((p.1+p.2)%4=1 ∨ (p.1+p.2)%4=2))

theorem sixForcedExcluded_sound (x y : Nat)
    (hex : sixForcedExcluded x y = true) :
    ¬ CReach x y := by
  intro hr
  obtain ⟨time,ht⟩ := (sixForcedNormalize_reach_iff x y).mp hr
  have hh : 5≤(sixForcedNormalize x y).2 ∧
      (sixForcedNormalize x y).2%2=1 ∧
      (((sixForcedNormalize x y).1+(sixForcedNormalize x y).2)%4=1 ∨
       ((sixForcedNormalize x y).1+(sixForcedNormalize x y).2)%4=2) := by
    simpa [sixForcedExcluded] using (of_decide_eq_true hex)
  rcases hh with ⟨hy,ho,hbad⟩
  cases time with
  | zero =>
      have heq : sixForcedNormalize x y=(5,1) := by
        simpa [BB6.Agent8Section.run] using ht.symm
      have hp := congrArg Prod.snd heq
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n
        (sixForcedNormalize x y).1 (sixForcedNormalize x y).2 ht hy ho
      omega

#print axioms sixForcedNormalize_reach_iff
#print axioms sixForcedRootDecision_iff
#print axioms sixForcedExcluded_sound

end BB6.Agent11SixForced
