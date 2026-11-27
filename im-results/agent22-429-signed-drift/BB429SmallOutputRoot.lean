import BB429NewResidue
import Lean.Elab.Tactic.Omega

/-!
# New all-time small-output predecessor obstructions for genuine #429 root

For every blank-root accelerated return, first counter 1,4,5 are
unreachable. Every reachable return with first counter 11 has EVEN
second counter. These conclusions are all-parameter, source-rooted,
independent of any finite blank-tape simulation.

Useful as additional leaves in the source-certified inverse-tree
kernel, especially for the branch29 residue q=1023 mod2048.
-/
namespace BB429SmallOutputRoot
open BB429NewResidue
set_option maxRecDepth 30000
set_option maxHeartbeats 20000000

theorem step_ne_one (u w b : Nat) : BB429.next (u,w)≠some (1,b) := by
  intro h
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem step_ne_four (u w b : Nat) : BB429.next (u,w)≠some (4,b) := by
  intro h
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem step_five_forces_one (u w b : Nat)
    (h : BB429.next (u,w)=some (5,b)) : u=1 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem step_eleven_even (u w b : Nat) (hu : u≠4)
    (h : BB429.next (u,w)=some (11,b)) : b%2=0 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem no_root_one (b : Nat) : ¬Reach 1 b := by
  intro hr
  obtain ⟨u,w,_,hn⟩ := pred 1 b (by omega) hr
  exact step_ne_one u w b hn

theorem no_root_four (b : Nat) : ¬Reach 4 b := by
  intro hr
  obtain ⟨u,w,_,hn⟩ := pred 4 b (by omega) hr
  exact step_ne_four u w b hn

theorem no_root_five (b : Nat) : ¬Reach 5 b := by
  intro hr
  obtain ⟨u,w,hrp,hn⟩ := pred 5 b (by omega) hr
  have hu := step_five_forces_one u w b hn
  subst u
  exact no_root_one w hrp

theorem no_root_eleven_odd (b : Nat) (hb : b%2=1) : ¬Reach 11 b := by
  intro hr
  obtain ⟨u,w,hrp,hn⟩ := pred 11 b (by omega) hr
  have hu : u≠4 := by
    intro h
    subst u
    exact no_root_four w hrp
  have he := step_eleven_even u w b hu hn
  omega

#print axioms no_root_one
#print axioms no_root_four
#print axioms no_root_five
#print axioms no_root_eleven_odd
end BB429SmallOutputRoot
