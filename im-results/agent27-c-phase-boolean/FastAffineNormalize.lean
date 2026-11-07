import FullBoolean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent27FastNorm

def sourceGuard (a k : Nat) : Prop :=
  4≤k ∧ k%2=0 ∧ (a+k)%4=1

instance (a k : Nat) : Decidable (sourceGuard a k) := by
  unfold sourceGuard
  infer_instance

/-- A structurally recursive, logarithmic-fuel implementation of the
    authentic original affine normalizer. -/
def fastNormalizeFuel : Nat → Nat → Nat → Nat × Nat
  | 0, a, k => (a,k)
  | n+1,a,k =>
    if h : sourceGuard a k then
      fastNormalizeFuel n (a+k-2) ((k-2)/2)
    else (a,k)

private theorem fastNormalizeFuel_correct
    (fuel a k : Nat) (hbound : k ≤ 2^fuel) :
    fastNormalizeFuel fuel a k = BB6.Agent15.affineNormalize a k := by
  induction fuel generalizing a k with
  | zero =>
    have hnot : ¬ sourceGuard a k := by
      unfold sourceGuard
      change k ≤ 1 at hbound
      omega
    simp only [fastNormalizeFuel]
    rw [BB6.Agent15.affineNormalize.eq_1]
    have hnp : ¬(4≤k ∧ k%2=0 ∧ (a+k)%4=1) := by
      exact hnot
    simp only [dif_neg hnp]
  | succ n ih =>
    by_cases hg : sourceGuard a k
    · have hnew : (k-2)/2 ≤ 2^n := by
        unfold sourceGuard at hg
        rw [Nat.pow_succ] at hbound
        omega
      have hrec := ih (a+k-2) ((k-2)/2) hnew
      simp only [fastNormalizeFuel, dif_pos hg]
      rw [BB6.Agent15.affineNormalize.eq_1]
      have hp : 4≤k ∧ k%2=0 ∧ (a+k)%4=1 := hg
      simp only [dif_pos hp]
      exact hrec
    · simp only [fastNormalizeFuel, dif_neg hg]
      rw [BB6.Agent15.affineNormalize.eq_1]
      have hnp : ¬(4≤k ∧ k%2=0 ∧ (a+k)%4=1) := hg
      simp only [dif_neg hnp]

private theorem log_fuel_bound (k : Nat) :
    k ≤ 2^((k+1).log2+1) := by
  have hk : k+1 ≠ 0 := by omega
  have hb : ¬ (k+1).log2+1 ≤ (k+1).log2 := by omega
  have hlt : k+1 < 2^((k+1).log2+1) := by
    by_cases hc : k+1 < 2^((k+1).log2+1)
    · exact hc
    · have hh : 2^((k+1).log2+1) ≤ k+1 := by omega
      exact False.elim (hb ((Nat.le_log2 hk).mpr hh))
  omega

/-- Source-equivalent affine normalization evaluated through only
    logarithmically many structural recursion steps. -/
def fastNormalize (a k : Nat) : Nat × Nat :=
  fastNormalizeFuel ((k+1).log2+1) a k

theorem fastNormalize_eq (a k : Nat) :
    fastNormalize a k = BB6.Agent15.affineNormalize a k := by
  exact fastNormalizeFuel_correct ((k+1).log2+1) a k (log_fuel_bound k)

/-- Test both distinct phase families at their smallest indices. -/
#guard (fastNormalize 4515 9702331119358).2 == 75799461868
#guard (fastNormalize 6587 55280923390).2 == 431882212

#print axioms fastNormalize_eq
end BB6.Agent27FastNorm
