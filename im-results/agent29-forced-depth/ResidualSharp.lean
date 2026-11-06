import ResidualSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Barrier

/-- The uniform 220 wall is exact on the authentic high stopping-input
    and affine-normalization arithmetic locus. The witness is not claimed
    to lie on the true blank-rooted section orbit. -/
theorem second_deep_220_is_sharp :
    1774+4+3*3+5=2^(2*3+2)*(4+3) ∧
    4%2=0 ∧ 3%2=1 ∧ (4+3)%4=3 ∧
    (BB6.Agent15.affineNormalize (2*4+3) 1774).2=220 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  simp [BB6.Agent15.affineNormalize]

#print axioms second_deep_220_is_sharp
end BB6.Agent29Barrier
