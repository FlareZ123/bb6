import MixedUniversalAncestry
import GenericAffineSharp
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Any mixed forced inverse chain terminating in either source-certified
    two-edge A/B rectangle has precisely d+2 possible incoming edges
    from arbitrary section starts, and no blank-root incoming path. -/
theorem mixed_four_AB_cone_sharp (x y : Nat)
    (hzone : affineConeAB (mixedFourNormalize x y)) :
    ∃ d : Nat,
      (∀ (start : Nat × Nat) (time : Nat),
         BB6.Agent8Section.run secNext (time+d+3) (some start) ≠
           some (x,y)) ∧
      (∃ start : Nat × Nat,
         BB6.Agent8Section.run secNext (d+2) (some start) =
           some (x,y)) ∧
      ¬ CReach x y := by
  obtain ⟨d,hf,hp⟩ := mixed_four_all_start_exact_ancestry x y
  refine ⟨d,?_,?_,?_⟩
  · intro start time ht
    have ht2 : BB6.Agent8Section.run secNext ((time+3)+d) (some start) =
        some (x,y) := by
      simpa only [show time+3+d=time+d+3 by omega] using ht
    have hnormal := hp start (time+3) ht2
    rcases hzone with ⟨u,v,huv⟩ | ⟨u,v,huv⟩
    · rw [huv] at hnormal
      exact child_A_no_three start time u v hnormal
    · rw [huv] at hnormal
      exact child_B_no_three start time u v hnormal
  · rcases hzone with ⟨u,v,huv⟩ | ⟨u,v,huv⟩
    · let start : Nat×Nat := (8*u+24*v+10,4*u+20*v+7)
      refine ⟨start,?_⟩
      have htwo := child_A_two_witness u v
      have ht : BB6.Agent8Section.run secNext d
          (some (16*u+3,32*v+16))=some (x,y) := by
        rw [←huv]
        exact hf
      rw [show d+2=2+d by omega,BB6.Agent8Section.run_add,htwo]
      exact ht
    · let start : Nat×Nat := (8*u+24*v+26,4*u+20*v+19)
      refine ⟨start,?_⟩
      have htwo := child_B_two_witness u v
      have ht : BB6.Agent8Section.run secNext d
          (some (16*u+11,32*v+32))=some (x,y) := by
        rw [←huv]
        exact hf
      rw [show d+2=2+d by omega,BB6.Agent8Section.run_add,htwo]
      exact ht
  · intro hr
    have hnorm := (mixedFourNormalize_reach_iff x y).mp hr
    rcases hnorm with ⟨time,ht⟩
    rcases hzone with ⟨u,v,huv⟩ | ⟨u,v,huv⟩
    · rw [huv] at ht
      exact even_child_A_unreachable u v time ht
    · rw [huv] at ht
      exact even_child_B_unreachable u v time ht

#print axioms mixed_four_AB_cone_sharp
end BB6.Agent3
