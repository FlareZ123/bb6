import GenericAffineSharp
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Uniform source-semantic sufficient criterion for an unreachable genuine
    Machine C high stopping input, covering every high parameter m.
    In addition it determines the exact maximal arbitrary-root incoming path
    length for any input having a forced affine seed and terminal A/B cone. -/
theorem high_gate_affine_AB (j m k seed d : Nat)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hj : j%2=0)
    (hmod : seed%4=0) (hl : 32≤seed)
    (hright : k=affineRightSeed seed d)
    (hzone : affineConeAB
      (BB6.Agent15.affineNormalize (2*j+3) k)) :
    secNext (2*j+3,k)=none ∧
    (¬ BB6.Agent15.CReach (2*j+3) k) ∧
    ((∀ start : Nat×Nat, ∀ time : Nat,
        BB6.Agent8Section.run secNext (time+d+3) (some start) ≠
          some (2*j+3,k)) ∧
      (∃ start : Nat×Nat,
        BB6.Agent8Section.run secNext (d+2) (some start)=
          some (2*j+3,k))) := by
  have hstop : secNext (2*j+3,k)=none := by
    apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
    right; right
    exact ⟨j,m,rfl,hgate⟩
  have hnot : ¬ BB6.Agent15.CReach (2*j+3) k := by
    intro hr
    have hnormal := (BB6.Agent15.reach_iff_normalize (2*j+3) k).mp hr
    obtain ⟨time,ht⟩ := hnormal
    rcases hzone with ⟨u,v,hco⟩ | ⟨u,v,hco⟩
    · rw [hco] at ht
      exact even_child_A_unreachable u v time ht
    · rw [hco] at ht
      exact even_child_B_unreachable u v time ht
  have ha : (2*j+3)%4=3 := by omega
  have hnormalized : affineConeAB
      (BB6.Agent15.affineNormalize (2*j+3)
        (affineRightSeed seed d)) := by
    simpa only [←hright] using hzone
  have hsharp := generic_affine_AB_sharp seed d (2*j+3) hmod hl ha hnormalized
  constructor
  · exact hstop
  constructor
  · exact hnot
  · simpa only [←hright] using hsharp

#print axioms high_gate_affine_AB
end BB6.Agent3
