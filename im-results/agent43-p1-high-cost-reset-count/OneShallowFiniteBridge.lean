import OneShallowFinite
import OneShallowLarge

namespace BB6.Agent43TwoRun

private theorem small_bounds
    (n s r p d K A R : Nat) (hn : 14≤n) (hn27 : n≤27)
    (hP : 8^s*p=2^n) (hD : 8^s*d=14*n+92)
    (hK : K≤588*8^s) (hA : 1≤A)
    (heq : K*p=A*8^r+R) : s≤2 ∧ r≤12 := by
  have hqD : 8^s≤14*n+92 :=
    Nat.le_of_dvd (by omega) ⟨d, hD.symm⟩
  have hs : s≤2 := by
    by_cases h:s≤2
    · exact h
    · have hpow : (8:Nat)^3≤8^s :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have h512 : 512≤8^s := by simpa using hpow
      omega
  have hKmul := Nat.mul_le_mul_right p hK
  have hKbig : K*p≤588*2^n := by
    calc
      _ ≤ (588*8^s)*p := hKmul
      _ = 588*2^n := by rw [←hP]; ac_rfl
  have hP27 : 2^n≤(2:Nat)^27 :=
    Nat.pow_le_pow_right (by decide) hn27
  have hKmax : K*p≤588*2^27 := by
    have hh := Nat.mul_le_mul_left 588 hP27
    omega
  have hAmin : 8^r≤A*8^r := by
    have hh := Nat.mul_le_mul_right (8^r) hA
    simpa using hh
  have hr : r≤12 := by
    by_cases h:r≤12
    · exact h
    · have hpow : (8:Nat)^13≤8^r :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hgap : 588*2^27 < (8:Nat)^13 := by decide
      omega
  exact ⟨hs,hr⟩

private theorem finite_no0
    (n s r p d : Nat) (hn : 14≤n) (hn27:n≤27)
    (hs : s≤2) (hr : r≤12)
    (hP : 8^s*p=2^n) (hD : 8^s*d=14*n+92)
    (heq : (588*8^s-98)*p =
      (224*n+672*s+672*r+800)*8^r +
      (84*n+252*s+272-d)) : False := by
  let N : Fin 14 := ⟨n-14, by omega⟩
  let S : Fin 3 := ⟨s, by omega⟩
  let R : Fin 13 := ⟨r, by omega⟩
  have hnot : smallBad0 n s r = false := by
    have hh := no_small_bad0 N S R
    simpa only [N,S,R, Fin.val_mk, show n-14+14=n by omega] using hh
  have hPmod : 2^n % (8^s)=0 := by
    rw [←hP]
    exact Nat.mul_mod_right _ _
  have hDmod : (14*n+92)%(8^s)=0 := by
    rw [←hD]
    exact Nat.mul_mod_right _ _
  have hPdiv : (2^n)/(8^s)=p := by
    rw [←hP]
    exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
  have hDdiv : (14*n+92)/(8^s)=d := by
    rw [←hD]
    exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
  have hyes : smallBad0 n s r = true := by
    simp only [smallBad0,hPmod,hDmod,hPdiv,hDdiv,heq]
    decide
  rw [hyes] at hnot
  contradiction

private theorem finite_no1
    (n s r p d : Nat) (hn : 14≤n) (hn27:n≤27)
    (hs : s≤2) (hr : r≤12)
    (hP : 8^s*p=2^n) (hD : 8^s*d=14*n+92)
    (heq : (392*8^s-98)*p =
      (448*n+1344*s+1344*r+2048)*8^r +
      (56*n+168*s+200-d)) : False := by
  let N : Fin 14 := ⟨n-14, by omega⟩
  let S : Fin 3 := ⟨s, by omega⟩
  let R : Fin 13 := ⟨r, by omega⟩
  have hnot : smallBad1 n s r = false := by
    have hh := no_small_bad1 N S R
    simpa only [N,S,R, Fin.val_mk, show n-14+14=n by omega] using hh
  have hPmod : 2^n % (8^s)=0 := by
    rw [←hP]
    exact Nat.mul_mod_right _ _
  have hDmod : (14*n+92)%(8^s)=0 := by
    rw [←hD]
    exact Nat.mul_mod_right _ _
  have hPdiv : (2^n)/(8^s)=p := by
    rw [←hP]
    exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
  have hDdiv : (14*n+92)/(8^s)=d := by
    rw [←hD]
    exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
  have hyes : smallBad1 n s r = true := by
    simp only [smallBad1,hPmod,hDmod,hPdiv,hDdiv,heq]
    decide
  rw [hyes] at hnot
  contradiction

/-- The middle shallow depth zero is forbidden uniformly, all n>=14. -/
theorem no_zero_middle_all
    (n s r p d : Nat) (hn : 14≤n)
    (hP : 8^s*p=2^n) (hD : 8^s*d=14*n+92)
    (heq : (588*8^s-98)*p =
      (224*n+672*s+672*r+800)*8^r +
      (84*n+252*s+272-d)) : False := by
  by_cases h28 : 28≤n
  · exact no_zero_middle_large n s r p d h28 hP hD heq
  · have hn27 : n≤27 := by omega
    have hbounds := small_bounds n s r p d (588*8^s-98)
      (224*n+672*s+672*r+800) (84*n+252*s+272-d)
      hn hn27 hP hD (by omega) (by omega) heq
    exact finite_no0 n s r p d hn hn27 hbounds.1 hbounds.2 hP hD heq

/-- The middle shallow depth one is forbidden uniformly, all n>=14. -/
theorem no_one_middle_all
    (n s r p d : Nat) (hn : 14≤n)
    (hP : 8^s*p=2^n) (hD : 8^s*d=14*n+92)
    (heq : (392*8^s-98)*p =
      (448*n+1344*s+1344*r+2048)*8^r +
      (56*n+168*s+200-d)) : False := by
  by_cases h28 : 28≤n
  · exact no_one_middle_large n s r p d h28 hP hD heq
  · have hn27 : n≤27 := by omega
    have hbounds := small_bounds n s r p d (392*8^s-98)
      (448*n+1344*s+1344*r+2048) (56*n+168*s+200-d)
      hn hn27 hP hD (by omega) (by omega) heq
    exact finite_no1 n s r p d hn hn27 hbounds.1 hbounds.2 hP hD heq

#print axioms BB6.Agent43TwoRun.no_zero_middle_all
#print axioms BB6.Agent43TwoRun.no_one_middle_all
end BB6.Agent43TwoRun