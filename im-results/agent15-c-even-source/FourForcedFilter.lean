import FourForcedNormalize
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

/-- Sound, executable Boolean filter for all four forced inverse sectors. -/
def fourForcedExcluded (x y : Nat) : Bool :=
  let p := fourForcedNormalize x y
  decide (5≤p.2 ∧ p.2%2=1 ∧
    ((p.1+p.2)%4=1 ∨ (p.1+p.2)%4=2))

/-- True means nonreachability from the actual Machine C blank section;
    false means unknown. No simulation or finite cutoff is used. -/
theorem fourForcedExcluded_sound (x y : Nat)
    (hex : fourForcedExcluded x y=true) :
    ∀ time, BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  intro time ht
  obtain ⟨n,hn⟩ := (blank_reach_iff_fourForcedNormalize x y).mp ⟨time,ht⟩
  have hh : 5≤(fourForcedNormalize x y).2 ∧
      (fourForcedNormalize x y).2%2=1 ∧
      (((fourForcedNormalize x y).1+(fourForcedNormalize x y).2)%4=1 ∨
       ((fourForcedNormalize x y).1+(fourForcedNormalize x y).2)%4=2) := by
    simpa [fourForcedExcluded] using (of_decide_eq_true hex)
  rcases hh with ⟨hy,ho,hbad⟩
  cases n with
  | zero =>
      have heq : fourForcedNormalize x y=(5,1) := by
        simpa [BB6.Agent8Section.run] using hn.symm
      have hp := congrArg Prod.snd heq
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n
        (fourForcedNormalize x y).1 (fourForcedNormalize x y).2 hn hy ho
      omega

#print axioms fourForcedExcluded_sound
end BB6.Agent15
