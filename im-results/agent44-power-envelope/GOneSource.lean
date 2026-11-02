import GInverse
import GOneCertificate

namespace BB6.Agent44

/-- The original source's GAncestor_power lemma forces the shifted counter
to be a pure power of two when the exceptional input is 1. The universal
affine rectangle excludes that possibility for the entire candidate census,
conditional on the generated node's affine equality. -/
theorem p1_affine_no_one_ancestor
    (q R b d : Nat) (A C : Int) (hR : 30≤R)
    (hcase : (65536≤A ∧ A≤74888 ∧ 12≤C ∧ C≤74562) ∨
             (74928≤A ∧ A≤130720 ∧ 10≤C ∧ C≤130036))
    (hD : ((d+b/2+3:Nat):Int) =
      A*((7*(2^(65536*q+R-16)):Nat)-(q+1):Nat)+C) :
    ∀ k : Nat, ¬ BB6.P1Reduction.GAncestor b d k 1 := by
  intro k hk
  obtain ⟨e, he⟩ := BB6.P1Reduction.GAncestor_power b d k 1 hk
  have hpow : d+b/2+3 = 2^(e+2) := by
    simpa [Nat.pow_add, show (2:Nat)^2 = 4 by decide, Nat.mul_comm] using he
  exact p1_shifted_leaf_no_power q R (d+b/2+3) A C hR hcase hD (e+2) hpow

#print axioms BB6.Agent44.p1_affine_no_one_ancestor
end BB6.Agent44
