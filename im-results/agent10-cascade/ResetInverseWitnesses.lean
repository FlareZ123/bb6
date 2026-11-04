import ReturnInverseArithmetic

namespace CascadeResetInverse
open CascadeSource CascadeSweep

private theorem power_linear (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

private theorem one_guard_backwards (h k : Nat)
    (hg : 8*2^(k+1)≤h+(k+1)+5) :
    8*2^k≤h+k+5 := by
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
  have hh : 2^(k+1)=2*2^k := by rw [Nat.pow_succ];omega
  rw [hh] at hg
  omega

private theorem all_prior_guards (h k j : Nat) (hj : j≤k)
    (hg : 8*2^k≤h+k+5) :
    8*2^j≤h+j+5 := by
  induction k generalizing j with
  | zero =>
    have hj0 : j=0 := by omega
    subst j
    exact hg
  | succ k ih =>
    by_cases heq : j=k+1
    · subst j
      exact hg
    · have hjk : j≤k := by omega
      exact ih j hjk (one_guard_backwards h k hg)

/-- Exactly one final guard test suffices to validate all previous growing
    phases. This is the converse of first_low from FullReturn. -/
theorem guards_from_low (h k : Nat)
  (hlow : 4*2^k≤h+k+4) :
  ∀ j, j<k → 8*2^j≤h+j+5 := by
  cases k with
  | zero =>
    intro j hj
    omega
  | succ k =>
    have hh : 8*2^k=4*2^(k+1) := by rw [Nat.pow_succ];omega
    have hlast : 8*2^k≤h+k+5 := by
      rw [hh]
      omega
    intro j hj
    exact all_prior_guards h k j (by omega) hlast

/-- Every height inside an even-return band has a constructive source-C
    reset predecessor, strictly smaller than the target. -/
theorem every_even_band_has_parent (k u : Nat)
  (hband : 6*2^k-1≤u ∧ u≤8*2^k-3) :
  ∃ h, h<u ∧ ReachC (h,0) (u,0) := by
  have hpow : k+2≤4*2^k := by
    have hv := power_linear k
    omega
  let h := 2*u-8*2^k-k
  have hlarge : 8*2^k+k≤2*u := by omega
  have heq : 2*u=8*2^k+h+k := by
    dsimp [h]
    omega
  have hlow : 4*2^k≤h+k+4 := by omega
  have hhigh : h+k+5<8*2^k := by omega
  have hnot : h+k+4≠4*2^k := by omega
  have hpar : (h+k)%2=0 := by omega
  have hu : u=4*2^k+(h+k)/2 := by omega
  refine ⟨h,by omega,?_⟩
  rw [hu]
  exact even_reset h k (guards_from_low h k hlow) hlow hhigh hnot hpar

/-- Every candidate with valid dyadic odd-exit q band has a genuine
    source-C reset predecessor, even at arbitrarily high 2-adic valuation. -/
theorem every_odd_band_has_parent (k t d : Nat)
  (hd : d%2=1)
  (hband : 6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) :
  ∃ h, ReachC (h,0) ((3^(t+1)*d-5)/2,0) := by
  let q := 2^t*d
  have hpow : k+4≤4*2^k := by
    have hv := power_linear k
    omega
  let h := 2*q-8*2^k-k-5
  have hlarge : 8*2^k+k+5≤2*q := by omega
  have heq : 2*q=8*2^k+h+k+5 := by
    dsimp [h]
    omega
  have hlow : 4*2^k≤h+k+4 := by omega
  have hhigh : h+k+5<8*2^k := by omega
  have hnot : h+k+4≠4*2^k := by omega
  have hpar : (h+k)%2=1 := by omega
  have hq : 4*2^k+(h+k)/2+3=2^t*d := by
    dsimp [q] at heq
    omega
  exact ⟨h,odd_reset h k t d (guards_from_low h k hlow) hlow hhigh hnot hpar hq hd⟩

#print axioms guards_from_low
#print axioms every_even_band_has_parent
#print axioms every_odd_band_has_parent
end CascadeResetInverse
