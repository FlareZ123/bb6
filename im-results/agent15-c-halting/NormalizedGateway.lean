import AffineNormalize
import BlankParam

namespace BB6.Agent15
open BB6.Agent46

/-- The exact blank Machine C stopping problem reduces to reachability of
    two arithmetic parameter families after completely stripping their
    forced affine inverse chains. -/
theorem blank_halts_iff_normalized_families :
    BB6.CReachBridge.RunHalts ↔
      (∃ m k, k+3*m+4=2^(2*m+3) ∧
         CReach (affineNormalize 1 k).1 (affineNormalize 1 k).2) ∨
      (∃ j m k, k+j+3*m+5=2^(2*m+2)*(j+3) ∧
         CReach (affineNormalize (2*j+3) k).1 (affineNormalize (2*j+3) k).2) := by
  rw [blank_halts_iff_two_parametric_families]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with h1|h2
    · rcases h1 with ⟨ha,m,heq⟩
      subst a
      exact Or.inl ⟨m,k,heq,(reach_iff_normalize 1 k).mp ⟨time,hr⟩⟩
    · rcases h2 with ⟨j,m,ha,heq⟩
      subst a
      exact Or.inr ⟨j,m,k,heq,(reach_iff_normalize (2*j+3) k).mp ⟨time,hr⟩⟩
  · rintro (h1|h2)
    · rcases h1 with ⟨m,k,heq,hReach⟩
      obtain ⟨time,hr⟩ := (reach_iff_normalize 1 k).mpr hReach
      exact ⟨time,1,k,hr,Or.inl ⟨rfl,m,heq⟩⟩
    · rcases h2 with ⟨j,m,k,heq,hReach⟩
      obtain ⟨time,hr⟩ := (reach_iff_normalize (2*j+3) k).mpr hReach
      exact ⟨time,2*j+3,k,hr,Or.inr ⟨j,m,rfl,heq⟩⟩

#print axioms blank_halts_iff_normalized_families
end BB6.Agent15
