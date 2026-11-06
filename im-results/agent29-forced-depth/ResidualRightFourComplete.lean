import ResidualOneComplete
import ResidualSource
import SecondOneInfinite
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Barrier

/-- The COMPLETE odd-exponent original Machine C stopping-input sector with
    affine-normalized right counter four is the previously constructed
    m=1, j=10,202,3274,... tower. No blank-root assertion is made. -/
theorem second_odd_right_four_complete (j m k : Nat)
    (hmpos : 1≤m) (hm : m%2=1)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (BB6.Agent15.affineNormalize (2*j+3) k).2=4 ↔
      m=1 ∧ ∃r, j=BB6.Agent29Depth.secondOneJ r := by
  constructor
  · intro hfour
    have hklarge := BB6.Agent15.second_halt_k_ge_seven j m k hstop
    have hpowmod : (2^(2*m+2))%4=0 := by
      apply Nat.mod_eq_zero_of_dvd
      change 2^2 ∣ 2^(2*m+2)
      exact Nat.pow_dvd_pow 2 (by omega)
    have hprodmod : (2^(2*m+2)*(j+3))%4=0 := by
      rw [Nat.mul_mod,hpowmod]
      omega
    have hj : j%2=0 := by
      by_contra hj0
      have hjodd : j%2=1 := by omega
      have hkodd : k%2=1 := by omega
      have hnot : ¬(4≤k ∧ k%2=0 ∧ ((2*j+3)+k)%4=1) := by omega
      have hnorm : BB6.Agent15.affineNormalize (2*j+3) k=(2*j+3,k) := by
        rw [BB6.Agent15.affineNormalize, dif_neg hnot]
      rw [hnorm] at hfour
      omega
    have ha : (2*j+3)%4=3 := by omega
    have hk2 : k%4=2 := by
      by_contra hn
      have hnot : ¬(4≤k ∧ k%2=0 ∧ ((2*j+3)+k)%4=1) := by omega
      have hnorm : BB6.Agent15.affineNormalize (2*j+3) k=(2*j+3,k) := by
        rw [BB6.Agent15.affineNormalize, dif_neg hnot]
      rw [hnorm] at hfour
      omega
    have hs : (j+m)%4=3 := by omega
    have hmcase : m=1 ∨ 3≤m := by omega
    rcases hmcase with h1 | h3
    · subst m
      have hk : k=15*j+40 := by
        have hp : 2^(2*1+2)=16 := by decide
        rw [hp] at hstop
        omega
      have hscale := (BB6.Agent15.normalize_three_depth_invariants
        (2*j+3) k ha).2.1
      have hscale4 : 2^(BB6.Agent15.oddDepth k)*6=k+2 := by
        dsimp at hscale
        rw [hfour] at hscale
        simpa using hscale
      have hpow : 2^(BB6.Agent15.oddDepth k+1)=5*j+14 := by
        have he : 2^(BB6.Agent15.oddDepth k+1)=
            2*(2^(BB6.Agent15.oddDepth k)) := by
          rw [Nat.pow_succ]
          ac_rfl
        rw [he]
        omega
      obtain ⟨r,hr,_⟩ := mone_dyadic_index_complete
        j (BB6.Agent15.oddDepth k) hpow
      exact ⟨rfl,⟨r,hr⟩⟩
    · have hb := second_deep_affine_residual_ge_220 j m k
        hstop hj hm hs h3
      omega
  · rintro ⟨h1,⟨r,hr⟩⟩
    subst m
    subst j
    have hk : k=15*BB6.Agent29Depth.secondOneJ r+40 := by
      have hp : 2^(2*1+2)=16 := by decide
      rw [hp] at hstop
      omega
    subst k
    exact BB6.Agent29Depth.second_one_family_normalizes_four r

#print axioms second_odd_right_four_complete
end BB6.Agent29Barrier
