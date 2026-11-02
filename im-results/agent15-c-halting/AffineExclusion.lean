import AffineNormalize
import SectionDyadic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

/-- Terminating blank-section exclusion filter after forced inverse steps. -/
def affineExcluded (a k : Nat) : Bool :=
  let (x,y) := affineNormalize a k
  decide (y=0 ∨ y=2 ∨ (y%2=1 ∧ (x+y)%4=2 ∧ (x,y)≠(5,1)))

theorem affineExcluded_sound (a k : Nat) (hex : affineExcluded a k=true) :
    ¬ CReach a k := by
  intro hr
  have H := (reach_iff_normalize a k).mp hr
  cases hp : affineNormalize a k with
  | mk x y =>
    rw [hp] at H
    change CReach x y at H
    rcases H with ⟨time,hrt⟩
    unfold affineExcluded at hex
    simp only [hp,decide_eq_true_eq] at hex
    rcases hex with (hzero|htwo|hmod)
    · have hpos := BB6Agent38.blank_section_positive time x y hrt
      omega
    · subst y
      exact blank_no_right_two time x hrt
    · rcases hmod with ⟨hodd,hs,hn⟩
      have he := BB6Agent38.blank_section_mod4 time x y hrt hodd hs
      exact hn he

#eval affineExcluded 3 1
#eval affineExcluded 7 70
#eval affineExcluded 9 16
#print axioms affineExcluded_sound
end BB6.Agent15
