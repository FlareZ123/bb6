import FullForcedNormalize
import Agent3CImage
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3
open BB6.Agent46
def fullForcedExcluded (x y : Nat) : Bool :=
  let p := fullForcedNormalize x y
  decide (5≤p.2 ∧ p.2%2=1 ∧
    ((p.1+p.2)%4=1 ∨ (p.1+p.2)%4=2))
theorem fullForcedExcluded_sound (x y : Nat)
    (hex : fullForcedExcluded x y = true) :
    ∀ time, BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  intro time ht
  obtain ⟨n,hn⟩ := (blank_reach_iff_fullForcedNormalize x y).mp ⟨time,ht⟩
  have hh : 5≤(fullForcedNormalize x y).2 ∧
      (fullForcedNormalize x y).2%2=1 ∧
      (((fullForcedNormalize x y).1+(fullForcedNormalize x y).2)%4=1 ∨
       ((fullForcedNormalize x y).1+(fullForcedNormalize x y).2)%4=2) := by
    simpa [fullForcedExcluded] using (of_decide_eq_true hex)
  rcases hh with ⟨hy,ho,hbad⟩
  cases n with
  | zero =>
      have heq : fullForcedNormalize x y=(5,1) := by
        simpa [BB6.Agent8Section.run] using hn.symm
      have hp := congrArg Prod.snd heq
      omega
  | succ n =>
      have hi := blank_section_odd_image n
        (fullForcedNormalize x y).1 (fullForcedNormalize x y).2 hn hy ho
      omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem high_m6_j93_exact_excluded (time : Nat) :
  BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (189,1572748) :=
  fullForcedExcluded_sound 189 1572748 (by decide +kernel) time
#print axioms fullForcedExcluded_sound
#print axioms high_m6_j93_exact_excluded
end BB6.Agent3
