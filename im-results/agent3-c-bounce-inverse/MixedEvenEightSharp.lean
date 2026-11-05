import MixedFourNormalize
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Uniform exact inverse barrier over a whole two-dimensional even-right
    sector. Every target x≡1(mod4), y≡0(mod8), y≥16 has a real unique
    immediate predecessor with forbidden odd right/sum2 image, so no
    arbitrary-start section trajectory reaches it in two or more steps. -/
theorem mixed_even_eight_sharp (x y : Nat)
    (hy : 16≤y) (hy8 : y%8=0) (hx : x%4=1) :
    (secNext (x+y-2,(y-2)/2)=some (x,y)) ∧
    (∀ (start : Nat×Nat) (time : Nat),
      BB6.Agent8Section.run secNext (time+2) (some start) ≠
        some (x,y)) ∧
    ¬ CReach x y := by
  have hparity : y%2=0 ∧ (x+y)%4=1 := by omega
  have hbad : 5≤(y-2)/2 ∧ ((y-2)/2)%2=1 ∧
      ((x+y-2)+(y-2)/2)%4=2 := by omega
  have hedge : secNext (x+y-2,(y-2)/2)=some (x,y) := by
    exact (BB6.Agent15.section_sum_one_even_iff_affine
      (x+y-2) ((y-2)/2) x y (by omega) hparity.1 hparity.2).mpr
      ⟨rfl,rfl⟩
  refine ⟨hedge,?_,?_⟩
  · intro start time hh
    have ht : BB6.Agent8Section.run secNext ((time+1)+1) (some start)=
        some (x,y) := by
      simpa only [show (time+1)+1=time+2 by omega] using hh
    change (BB6.Agent8Section.run secNext (time+1) (some start)).bind secNext =
      some (x,y) at ht
    cases hp : BB6.Agent8Section.run secNext (time+1) (some start) with
    | none => simp [hp] at ht
    | some p =>
        rcases p with ⟨a,k⟩
        have he : secNext (a,k)=some (x,y) := by simpa [hp] using ht
        have huni := (BB6.Agent15.section_sum_one_even_iff_affine
          a k x y (by omega) hparity.1 hparity.2).mp he
        rcases huni with ⟨ha,hk⟩
        rw [ha,hk] at hp
        change (BB6.Agent8Section.run secNext time (some start)).bind secNext =
          some (x+y-2,(y-2)/2) at hp
        cases hprev : BB6.Agent8Section.run secNext time (some start) with
        | none => simp [hprev] at hp
        | some q =>
            rcases q with ⟨b,c⟩
            have hq : secNext (b,c)=some (x+y-2,(y-2)/2) := by
              simpa [hprev] using hp
            have hi := section_odd_image b c (x+y-2) ((y-2)/2)
              hq hbad.1 hbad.2.1
            omega
  · intro hr
    have hp : CReach (x+y-2) ((y-2)/2) :=
      (BB6.Agent15.blank_reach_iff_affine x y
        (by omega) hparity.1 hparity.2).mp hr
    rcases hp with ⟨time,hn⟩
    cases time with
    | zero =>
        simp [BB6.Agent8Section.run] at hn
        omega
    | succ t =>
        have hi := blank_section_odd_image t (x+y-2) ((y-2)/2)
          hn hbad.1 hbad.2.1
        omega

#print axioms mixed_even_eight_sharp
end BB6.Agent3
