import OddForcedNormalize
import Agent3CImage
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3
open BB6.Agent46
def oddForcedExcluded (x y : Nat) : Bool :=
  let p := oddForcedNormalize x y
  decide (5≤p.2 ∧ p.2%2=1 ∧
    ((p.1+p.2)%4=1 ∨ (p.1+p.2)%4=2))
theorem oddForcedExcluded_sound (x y : Nat)
    (hex : oddForcedExcluded x y = true) :
    ∀ time, BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  intro time ht
  obtain ⟨n,hn⟩ := (blank_reach_iff_oddForcedNormalize x y).mp ⟨time,ht⟩
  have hh : 5≤(oddForcedNormalize x y).2 ∧
      (oddForcedNormalize x y).2%2=1 ∧
      (((oddForcedNormalize x y).1+(oddForcedNormalize x y).2)%4=1 ∨
       ((oddForcedNormalize x y).1+(oddForcedNormalize x y).2)%4=2) := by
    simpa [oddForcedExcluded] using (of_decide_eq_true hex)
  rcases hh with ⟨hy,ho,hbad⟩
  cases n with
  | zero =>
      have heq : oddForcedNormalize x y=(5,1) := by
        simpa [BB6.Agent8Section.run] using hn.symm
      have hp := congrArg Prod.snd heq
      omega
  | succ n =>
      have hi := blank_section_odd_image n
        (oddForcedNormalize x y).1 (oddForcedNormalize x y).2 hn hy ho
      omega
#print axioms oddForcedExcluded_sound
end BB6.Agent3
