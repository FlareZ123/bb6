import ReverseBlock
import LagCore
namespace BB6.Agent45WeightedDigitGap
open BB6.Agent45ReverseBlock (corr)
open BB6.Agent45.DelayedCarry (Trace total target target_eq trace_bounds quotient)

/-- Every bit in a k-bit integer has correction weight at least one. -/
theorem le_corr (k B : Nat) (hB : B<2^k) : B≤corr k B := by
  induction k generalizing B with
  | zero =>
    have hb : B=0 := by simpa using hB
    simp [corr,hb]
  | succ k ih =>
    have hh : B/2<2^k := by rw [Nat.pow_succ] at hB; omega
    have h := ih (B/2) hh
    simp only [corr]
    rcases (show B%2=0 ∨ B%2=1 by omega) with h0|h1
    · rw [h0]; omega
    · rw [h1,Nat.mul_one]; omega

/-- If B has exactly k+1 bits, the correction lies below 2B by k+1. -/
theorem corr_top_gap (k B : Nat) (hlo : 2^k≤B) (hhi : B<2^(k+1)) :
    corr (k+1) B+(k+1)≤2*B := by
  induction k generalizing B with
  | zero =>
    have hb : B=1 := by simp at hlo hhi; omega
    simp [hb,corr]
  | succ k ih =>
    have hlo' : 2^k≤B/2 := by rw [Nat.pow_succ] at hlo; omega
    have hhi' : B/2<2^(k+1) := by rw [Nat.pow_succ] at hhi; omega
    have hh := ih (B/2) hlo' hhi'
    change 2*corr (k+1) (B/2)+(k+2)*(B%2)+(k+2)≤2*B
    rcases (show B%2=0 ∨ B%2=1 by omega) with h0|h1
    · rw [h0,Nat.mul_zero,Nat.add_zero]; omega
    · rw [h1,Nat.mul_one]; omega

/-- The weighted digit index sum D(B) is k*B-corr k B for a k-bit word. -/
def digitWeight (k B : Nat) : Nat := k*B-corr k B

theorem corr_le_mul (k B : Nat) (hB : B<2^k) : corr k B≤k*B := by
  induction k generalizing B with
  | zero => simp [corr]
  | succ k ih =>
    have hh : B/2<2^k := by rw [Nat.pow_succ] at hB; omega
    have h := ih (B/2) hh
    have hb : B=2*(B/2)+B%2 := by omega
    have he : (k+1)*B=(k+1)*(2*(B/2))+(k+1)*(B%2) := by rw [←Nat.mul_add,←hb]
    have hp : (k+1)*(2*(B/2))=2*(k*(B/2))+2*(B/2) := by
      rw [Nat.add_mul,Nat.one_mul]
      ac_rfl
    rw [corr,he,hp]; omega

theorem weight_bounds (k B : Nat) (hlo : 2^k≤B) (hhi : B<2^(k+1)) :
    digitWeight (k+1) B≤k*B ∧ k*B+k+1≤digitWeight (k+1) B+B := by
  have hc := corr_top_gap k B hlo hhi
  have hl := le_corr (k+1) B hhi
  have hh := corr_le_mul (k+1) B hhi
  unfold digitWeight
  rw [Nat.add_mul,Nat.one_mul] at hh ⊢
  omega

/-- No positive finite binary word solves D(B)-A*B=1 for A>=0. -/
theorem no_positive_solution (A k B : Nat) (hlo : 2^k≤B) (hhi : B<2^(k+1)) :
    digitWeight (k+1) B≠A*B+1 := by
  intro he
  obtain ⟨hu,hl⟩ := weight_bounds k B hlo hhi
  have hB : 0<B := by have := Nat.two_pow_pos k; omega
  have hA : A<k := by
    by_cases h : A<k
    · exact h
    · have hprod := Nat.mul_le_mul_right B (show k≤A by omega)
      omega
  have hprod := Nat.mul_le_mul_right B (show A+1≤k by omega)
  rw [Nat.add_mul,Nat.one_mul] at hprod
  omega

/-- Complementary finite words exclude negative 2-adic integer roots. -/
theorem no_negative_solution (A k B : Nat) (hlo : 2^k≤B) (hhi : B<2^(k+1)) :
    digitWeight (k+1) B≠A*B+A+1 := by
  intro he
  obtain ⟨hu,hl⟩ := weight_bounds k B hlo hhi
  have hA : A<k := by
    by_cases h : A<k
    · exact h
    · have hprod := Nat.mul_le_mul_right B (show k≤A by omega)
      omega
  have hprod := Nat.mul_le_mul_right B (show A+1≤k by omega)
  rw [Nat.add_mul,Nat.one_mul] at hprod
  omega

#print axioms weight_bounds
#print axioms no_positive_solution
#print axioms no_negative_solution
end BB6.Agent45WeightedDigitGap
