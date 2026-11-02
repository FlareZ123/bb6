import M32HighAll
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CCert

private theorem high_parameter_mod32 (j m k : Nat) (hm : 2 ≤ m)
    (hgate : k+j+3*m+5 = 2^(2*m+2)*(j+3)) :
    (k+j+3*m+5)%32=0 := by
  have hp : 32 ∣ 2^(2*m+2) := by
    simpa using Nat.pow_dvd_pow 2 (show 5 ≤ 2*m+2 by omega)
  obtain ⟨d, hd⟩ := hp
  have hdiv : 32 ∣ 2^(2*m+2)*(j+3) := by
    refine ⟨d*(j+3), ?_⟩
    rw [hd]
    simp only [Nat.mul_assoc]
  rw [hgate]
  exact Nat.mod_eq_zero_of_dvd hdiv

private theorem j0_membership (m:Nat)
    (h:(0,m%32) ∈ newHighPairs) : m%32=13 ∨ m%32=25 := by
  simpa [newHighPairs] using h

private theorem j1_membership (m:Nat)
    (h:(1,m%32) ∈ newHighPairs) : m%32=28 := by
  simpa [newHighPairs] using h

private theorem j2_membership (m:Nat)
    (h:(2,m%32) ∈ newHighPairs) : False := by
  simpa [newHighPairs] using h

/-- All 24 high stopping-parameter residue pairs: no small-j exceptions. -/
theorem high_24_pairs_absent_all_j (j m k : Nat)
    (hm:2≤m)(heq:k+j+3*m+5=2^(2*m+2)*(j+3))
    (hp:(j%32,m%32) ∈ newHighPairs) :
    seen (q (2*j+3)) (q k) (q 0) = false := by
  have hk : 8 ≤ k := high_gateway_k_ge_eight j m k (by omega) heq
  have hmod := high_parameter_mod32 j m k hm heq
  by_cases hj : 3 ≤ j
  · exact high_24_pairs_absent j m k hj hm heq hp
  · have hsmall : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hsmall with rfl | rfl | rfl
    · have hmres := j0_membership m hp
      rcases hmres with h13|h25
      · have hkr : k%32=20 := by omega
        have hkq : q k=q 20 := q_congr_big _ _ hk (by omega) (by omega)
        rw [hkq]
        decide
      · have hkr : k%32=16 := by omega
        have hkq : q k=q 16 := q_congr_big _ _ hk (by omega) (by omega)
        rw [hkq]
        decide
    · have hmres := j1_membership m hp
      have hkr : k%32=6 := by omega
      have hkq : q k=q 38 := q_congr_big _ _ hk (by omega) (by omega)
      rw [hkq]
      decide
    · exact False.elim (j2_membership m hp)

theorem high_24_pairs_unreachable_all_j (j m k : Nat)
    (hm:2≤m)(heq:k+j+3*m+5=2^(2*m+2)*(j+3))
    (hp:(j%32,m%32) ∈ newHighPairs) :
    ¬ Reach (2*j+3,k,0) := by
  intro h
  have hs := reachable_seen h
  rw [high_24_pairs_absent_all_j j m k hm heq hp] at hs
  cases hs

#print axioms high_24_pairs_unreachable_all_j
end CCert
