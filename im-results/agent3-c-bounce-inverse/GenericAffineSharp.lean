import GenericAffinePaths
import ChildBTwoDepth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Membership in the two complementary exact two-step predecessor cones. -/
def affineConeAB (p : Nat × Nat) : Prop :=
  (∃ u v, p=(16*u+3,32*v+16)) ∨
  (∃ u v, p=(16*u+11,32*v+32))

private theorem generic_A_sharp (seed d a u v : Nat)
    (hmod:seed%4=0) (hl:32≤seed) (ha:a%4=3)
    (hco:BB6.Agent15.affineNormalize a (affineRightSeed seed d)=
      (16*u+3,32*v+16)) :
    (∀ (start : Nat×Nat) (time : Nat),
      BB6.Agent8Section.run secNext (time+d+3) (some start) ≠
        some (a,affineRightSeed seed d)) ∧
    (∃ (start : Nat×Nat),
      BB6.Agent8Section.run secNext (d+2) (some start)=
        some (a,affineRightSeed seed d)) := by
  constructor
  · intro start time ht
    have hs : BB6.Agent8Section.run secNext ((time+3)+d) (some start) =
      some (a,affineRightSeed seed d) := by
      simpa only [show time+3+d=time+d+3 by omega] using ht
    have hp := gen_right_pull_d start seed d a (time+3) hmod hl ha hs
    rw [hco] at hp
    exact (child_A_no_three start time u v) hp
  · let start : Nat×Nat := (8*u+24*v+10,4*u+20*v+7)
    refine ⟨start,?_⟩
    have hs : BB6.Agent8Section.run secNext 2 (some start) =
      some (16*u+3,32*v+16) := child_A_two_witness u v
    have hf := gen_right_forward_d seed d a hmod hl ha
    rw [hco] at hf
    rw [show d+2=2+d by omega,BB6.Agent8Section.run_add,hs]
    exact hf

private theorem generic_B_sharp (seed d a u v : Nat)
    (hmod:seed%4=0) (hl:32≤seed) (ha:a%4=3)
    (hco:BB6.Agent15.affineNormalize a (affineRightSeed seed d)=
      (16*u+11,32*v+32)) :
    (∀ (start : Nat×Nat) (time : Nat),
      BB6.Agent8Section.run secNext (time+d+3) (some start) ≠
        some (a,affineRightSeed seed d)) ∧
    (∃ (start : Nat×Nat),
      BB6.Agent8Section.run secNext (d+2) (some start)=
        some (a,affineRightSeed seed d)) := by
  constructor
  · intro start time ht
    have hs : BB6.Agent8Section.run secNext ((time+3)+d) (some start) =
      some (a,affineRightSeed seed d) := by
      simpa only [show time+3+d=time+d+3 by omega] using ht
    have hp := gen_right_pull_d start seed d a (time+3) hmod hl ha hs
    rw [hco] at hp
    exact (child_B_no_three start time u v) hp
  · let start : Nat×Nat := (8*u+24*v+26,4*u+20*v+19)
    refine ⟨start,?_⟩
    have hs : BB6.Agent8Section.run secNext 2 (some start) =
      some (16*u+11,32*v+32) := child_B_two_witness u v
    have hf := gen_right_forward_d seed d a hmod hl ha
    rw [hco] at hf
    rw [show d+2=2+d by omega,BB6.Agent8Section.run_add,hs]
    exact hf

/-- Exact all-start ancestry for arbitrary forced affine depth whose
    terminal normalizer lies in either source-certified two-edge cone. -/
theorem generic_affine_AB_sharp (seed d a : Nat)
    (hmod:seed%4=0) (hl:32≤seed) (ha:a%4=3)
    (hzone:affineConeAB
       (BB6.Agent15.affineNormalize a (affineRightSeed seed d))) :
    (∀ (start : Nat×Nat) (time : Nat),
      BB6.Agent8Section.run secNext (time+d+3) (some start) ≠
        some (a,affineRightSeed seed d)) ∧
    (∃ (start : Nat×Nat),
      BB6.Agent8Section.run secNext (d+2) (some start)=
        some (a,affineRightSeed seed d)) := by
  rcases hzone with ⟨u,v,hco⟩ | ⟨u,v,hco⟩
  · exact generic_A_sharp seed d a u v hmod hl ha hco
  · exact generic_B_sharp seed d a u v hmod hl ha hco

#print axioms generic_affine_AB_sharp
end BB6.Agent3
