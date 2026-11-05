import MixedMod16SevenBounce
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- This previously branching mod16-seven output region has EXACTLY TWO
    genuine incoming source edges, one direct affine and one depth-one
    bounce, and absolutely no other parent at any bounce recursion depth.
    The branches are always distinct for y≥64. -/
theorem mod16_seven_two_exact_parents (x y : Nat)
    (hx:x%2=1) (he:y%2=0) (hmod:(x+y+1)%16=8) (hy:64≤y) :
    let ad := x+y-2
    let kd := (y-2)/2
    let ab := (x+y+1)/4-3
    let kb := (x+2*y-ab-10)/2
    secNext (ad,kd)=some (x,y) ∧
    secNext (ab,kb)=some (x,y) ∧
    (ad,kd)≠(ab,kb) ∧
    (∀ a k, secNext (a,k)=some (x,y) →
       (a=ad ∧ k=kd) ∨ (a=ab ∧ k=kb)) := by
  dsimp
  let ad := x+y-2
  let kd := (y-2)/2
  let ab := (x+y+1)/4-3
  let kb := (x+2*y-ab-10)/2
  have hed : secNext (ad,kd)=some (x,y) := by
    exact direct_even_section x y (by omega) he
  have heb : secNext (ab,kb)=some (x,y) := by
    exact mod16_eight_bounce_construct x y hx he hmod hy
  have hadneq : ad ≠ ab := by dsimp [ad,ab]; omega
  have huniq : ∀ a k, secNext (a,k)=some (x,y) →
       (a=ad ∧ k=kd) ∨ (a=ab ∧ k=kb) := by
    intro a k hedge
    have hs := mod16_seven_exact_predecessors a k x y
      (by omega) hx he hmod hedge
    rcases hs with ⟨ha,hk⟩ | ⟨h4, h2⟩
    · exact Or.inl ⟨ha,hk⟩
    · exact Or.inr ⟨by dsimp [ab]; omega, by dsimp [kb,ab]; omega⟩
  exact ⟨hed,heb,(by intro h; exact hadneq (congrArg Prod.fst h)),huniq⟩

#print axioms mod16_seven_two_exact_parents
end BB6.Agent3
