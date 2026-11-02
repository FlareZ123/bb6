import ExceptionThresholds
namespace SheepEvenBound
theorem exceptional_universal (D c K e n a A B : Nat)
    (hc : 2^e = c+K) (hc2 : 2^e < 2*c) (he : e ≤ n)
    (hgap : K*2^(n-e)>D*(n+3)+A+B)
    (hlarge : D*(n-e+4)≥A) :
    2^n+A ≠ c*2^a+D*(a+3)+B := by
  have hn : n=e+(n-e) := by omega
  have hp2 : 2^n=(c+K)*2^(n-e) := by
    calc
      2^n=2^(e+(n-e)) := congrArg (fun x => 2^x) hn
      _=2^e*2^(n-e) := by rw [Nat.pow_add]
      _=(c+K)*2^(n-e) := by rw [hc]
  by_cases ha : a≤n-e
  · have hpow : 2^a≤2^(n-e) := Nat.pow_le_pow_right (by decide) ha
    have hcpow : c*2^a≤c*2^(n-e) := Nat.mul_le_mul_left c hpow
    have hlin : D*(a+3)≤D*(n+3) := by
      have haa : a≤n := by omega
      exact Nat.mul_le_mul_left D (by omega)
    have heq : (c+K)*2^(n-e)=c*2^(n-e)+K*2^(n-e) := Nat.add_mul c K _
    intro heq2
    rw [hp2,heq] at heq2
    omega
  · have ha' : n-e+1≤a := by omega
    have hpow : 2^(n-e+1)≤2^a := Nat.pow_le_pow_right (by decide) ha'
    have hpnext : 2^(n-e+1)=2*2^(n-e) := by
      rw [Nat.pow_succ]
      omega
    have hcpow : c*(2*2^(n-e))≤c*2^a := by
      rw [←hpnext]
      exact Nat.mul_le_mul_left c hpow
    have hcmul : c*(2*2^(n-e))=(2*c)*2^(n-e) := by
      simp [Nat.mul_assoc,Nat.mul_comm]
    have hcl : (c+K)*2^(n-e)<(2*c)*2^(n-e) := by
      have hz : 0<2^(n-e) := Nat.pow_pos (by decide)
      have hc1 : c+K<2*c := by omega
      exact Nat.mul_lt_mul_of_pos_right hc1 hz
    have hlin : A≤D*(a+3) := by
      have hh : n-e+4≤a+3 := by omega
      have hd := Nat.mul_le_mul_left D hh
      omega
    intro heq2
    rw [hp2] at heq2
    omega
#print axioms exceptional_universal
end SheepEvenBound
