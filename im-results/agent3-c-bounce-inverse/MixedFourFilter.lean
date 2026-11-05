import MixedFourNormalize
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Sound executable nonreachability test for the mixed exact normalizer.
    False means unknown and does not assert reachability. -/
def mixedFourExcluded (x y : Nat) : Bool :=
  let p := mixedFourNormalize x y
  decide (5≤p.2 ∧ p.2%2=1 ∧
    ((p.1+p.2)%4=1 ∨ (p.1+p.2)%4=2))

theorem mixedFourExcluded_sound (x y : Nat)
    (hex : mixedFourExcluded x y = true) :
    ¬ CReach x y := by
  intro hr
  obtain ⟨time,hn⟩ := (mixedFourNormalize_reach_iff x y).mp hr
  have hh : 5≤(mixedFourNormalize x y).2 ∧
      (mixedFourNormalize x y).2%2=1 ∧
      (((mixedFourNormalize x y).1+(mixedFourNormalize x y).2)%4=1 ∨
       ((mixedFourNormalize x y).1+(mixedFourNormalize x y).2)%4=2) := by
    simpa [mixedFourExcluded] using (of_decide_eq_true hex)
  rcases hh with ⟨hy,ho,hbad⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hn
      omega
  | succ t =>
      have hi := blank_section_odd_image t
        (mixedFourNormalize x y).1 (mixedFourNormalize x y).2 hn hy ho
      omega

#print axioms mixedFourExcluded_sound
end BB6.Agent3
