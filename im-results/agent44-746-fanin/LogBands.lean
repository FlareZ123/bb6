import Std
set_option maxHeartbeats 0
namespace CascadeAgent44

def BandOdd (q : Nat) : Prop :=
  ∃ k, 1 ≤ k ∧ 6*2^k+1 ≤ q ∧ q ≤ 8*2^k-1

private theorem pow_two_offset (k : Nat) :
    2^(k+2)=4*2^k ∧ 2^(k+3)=8*2^k := by
  constructor
  · rw [show k+2=k+(2:Nat) by omega, Nat.pow_add]
    simp [show (2:Nat)^2=4 by decide, Nat.mul_comm]
  · rw [show k+3=k+(3:Nat) by omega, Nat.pow_add]
    simp [show (2:Nat)^3=8 by decide, Nat.mul_comm]

/-- A near-upper-end dyadic band is equivalent to no drop in binary
logarithm when multiplying by 2/3, except exact lower boundary. -/
theorem bandOdd_log_iff (r : Nat) (hr : 0 < r) :
    BandOdd (3*r) ↔
      3 ≤ Nat.log2 (2*r) ∧
      Nat.log2 (3*r) = Nat.log2 (2*r) ∧
      2^(Nat.log2 (2*r)) < 2*r := by
  constructor
  · rintro ⟨k,hk,hlo,hhi⟩
    have hpow := pow_two_offset k
    have h4 : 4*2^k < 2*r := by omega
    have h8 : 2*r < 8*2^k := by omega
    have h6 : 6*2^k < 3*r := by omega
    have h8' : 3*r < 8*2^k := by omega
    have hj2 : Nat.log2 (2*r) = k+2 := by
      apply (Nat.log2_eq_iff (by omega)).mpr
      rw [hpow.1,hpow.2]
      omega
    have hj3 : Nat.log2 (3*r) = k+2 := by
      apply (Nat.log2_eq_iff (by omega)).mpr
      rw [hpow.1,hpow.2]
      omega
    constructor
    · rw [hj2];omega
    constructor
    · rw [hj3,hj2]
    · rw [hj2,hpow.1]
      exact h4
  · rintro ⟨hj,hlog,hs⟩
    let j := Nat.log2 (2*r)
    let k := j-2
    have hkj : k+2=j := by dsimp [k,j];omega
    have hk : 1 ≤ k := by dsimp [k,j] at *;omega
    have hpow4 : 2^j = 4*2^k := by
      rw [←hkj]
      exact (pow_two_offset k).1
    have hpow8 : 2^(j+1)=8*2^k := by
      rw [←hkj]
      have heq : k+2+1=k+3 := by omega
      rw [heq]
      exact (pow_two_offset k).2
    have hup : 3*r < 2^(j+1) := by
      have hi := Nat.lt_log2_self (n:=3*r)
      rw [hlog] at hi
      exact hi
    have hlo : 6*2^k < 3*r := by
      dsimp [j] at hpow4 hs
      omega
    have hhi : 3*r < 8*2^k := by
      rw [hpow8] at hup
      exact hup
    exact ⟨k,hk,by omega,by omega⟩

/-- The lower bound on the binary length follows automatically once
    there is a strict lower-bit inequality and no logarithm drop. -/
theorem bandOdd_simple_iff (r : Nat) (hr : 0 < r) :
    BandOdd (3*r) ↔
      Nat.log2 (3*r) = Nat.log2 (2*r) ∧
      2^(Nat.log2 (2*r)) < 2*r := by
  rw [bandOdd_log_iff r hr]
  constructor
  · intro h
    exact ⟨h.2.1,h.2.2⟩
  · rintro ⟨hlog,hs⟩
    have hj : 3 ≤ Nat.log2 (2*r) := by
      let j := Nat.log2 (2*r)
      have hU : 3*r < 2^(j+1) := by
        have hi := Nat.lt_log2_self (n:=3*r)
        rw [hlog] at hi
        exact hi
      have hLow : 2^j < 2*r := hs
      by_cases hj : 3 ≤ j
      · exact hj
      have hsmall : j=0 ∨ j=1 ∨ j=2 := by omega
      rcases hsmall with h0 | h1 | h2
      · rw [h0] at hLow hU
        simp at hLow hU
        omega
      · rw [h1] at hLow hU
        simp at hLow hU
        omega
      · rw [h2] at hLow hU
        simp at hLow hU
        omega
    exact ⟨hj,hlog,hs⟩

theorem log2_exact_power (k : Nat) : Nat.log2 (2^k) = k := by
  apply (Nat.log2_eq_iff (by
    have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
    omega)).mpr
  constructor
  · exact Nat.le_refl _
  · rw [Nat.pow_succ]
    have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
    omega

private theorem log2_two_power_eq (r : Nat) (hr : 0 < r) :
    2^(Nat.log2 (2*r)) = 2*r ↔ ∃k, r=2^k := by
  have hlog : Nat.log2 (2*r) = Nat.log2 r + 1 := by
    have h := Nat.log2_two_mul (n:=r) (by omega)
    simpa [Nat.mul_comm] using h
  constructor
  · intro he
    rw [hlog,Nat.pow_succ] at he
    refine ⟨Nat.log2 r,?_⟩
    omega
  · rintro ⟨k,hk⟩
    subst r
    rw [hlog,log2_exact_power,Nat.pow_succ]
    omega

/-- The only obstruction to the telescoping binary-logarithm criterion is
    exact powers of two, which sit on a forbidden lower dyadic band endpoint. -/
theorem bandOdd_log_power_iff (r : Nat) (hr : 0 < r) :
    BandOdd (3*r) ↔
      Nat.log2 (3*r) = Nat.log2 (2*r) ∧ ¬∃k, r=2^k := by
  rw [bandOdd_simple_iff r hr]
  have hp : 2^(Nat.log2 (2*r)) ≤ 2*r := Nat.log2_self_le (by omega)
  have heq : 2^(Nat.log2 (2*r)) = 2*r ↔ ∃k, r=2^k :=
    log2_two_power_eq r hr
  constructor
  · rintro ⟨hl,hlt⟩
    refine ⟨hl,?_⟩
    intro hex
    have h := heq.mpr hex
    omega
  · rintro ⟨hl,hex⟩
    refine ⟨hl,?_⟩
    have hn : 2^(Nat.log2 (2*r)) ≠ 2*r := by
      intro hh
      exact hex (heq.mp hh)
    omega

#print axioms bandOdd_log_power_iff
#print axioms bandOdd_simple_iff
#print axioms bandOdd_log_iff
end CascadeAgent44
