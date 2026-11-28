import GenericCutoff

namespace NeedleRotation.Asymmetric

/-- Exact source parent equation, arbitrary affine reverse node, with bounds
    on coefficient sizes uniform over the whole physical valuation interval. -/
theorem generic_affine_source_quadratic
    (r a N P b q w L x H₂ H₃ : Nat) (d : Int)
    (hx : 0<x) (hL : L%2=1) (hd : d%2=0)
    (hP : ((2:Int)^a+3)*(P:Int)+(N:Int)=((2:Int)^a)^(2*r))
    (hb : 2*(L:Int)*(b:Int)=(2:Int)^x*2^a*(P:Int)+d)
    (hsize : b<2^(2*r*a))
    (hp : b=(2^(w+1)+3)*q+3*2^w+w+3)
    (hH₂ : d.natAbs+L*(2*(2*r*a)+5)+2^x*N<2^H₂)
    (hH₃ : 3*(d.natAbs+L*(2*(2*r*a)+5))<2^H₃) :
    5*((w+1)*(w+1))≤5*(x+1+H₂+H₃+22)*(w+1)+8*((2*r+1)*a+a) ∨
      (w+1)∣(2*r+1)*a+x-a ∨ (w+1)∣(2*r+1)*a+x ∨ (w+1)∣a := by
  let m:=w+1
  let M:=2*r*a
  let c: Int := 2^x
  let C: Int := d+(L:Int)*(5-2*(m:Int))
  have hm : 0<m := by dsimp [m]; omega
  have hpow : 2^m<b := by
    dsimp [m]
    rw [Nat.pow_succ]
    have h := Nat.two_pow_pos w
    omega
  have hphys : m≤M := by
    by_cases h : m≤M
    · exact h
    · have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show M≤m by omega)
      change b<2^M at hsize
      omega
  have hL' : (L:Int)%2=1 := by exact_mod_cast hL
  have hCodd : C%2=1 := by
    dsimp [C]
    rw [Int.add_emod, hd, Int.mul_emod, hL', Int.sub_emod,Int.mul_emod]
    simp
  have hCabs : C.natAbs≤d.natAbs+L*(2*M+5) := by
    dsimp [C]
    have hh:=Int.natAbs_add_le d ((L:Int)*(5-2*(m:Int)))
    rw [Int.natAbs_mul,Int.natAbs_natCast] at hh
    have hsub:=Int.natAbs_sub_le 5 (2*(m:Int))
    rw [Int.natAbs_mul,Int.natAbs_natCast] at hsub
    have hsub' : (5-2*(m:Int)).natAbs≤2*M+5 := by omega
    exact Nat.le_trans hh (Nat.add_le_add_left (Nat.mul_le_mul_left L hsub') _)
  have hmid : (C-c*(N:Int)).natAbs<2^H₂ := by
    have hsub:=Int.natAbs_sub_le C (c*(N:Int))
    rw [Int.natAbs_mul,Int.natAbs_natCast] at hsub
    have hc : c.natAbs=2^x := by simp [c,Int.natAbs_pow]
    rw [hc] at hsub
    change d.natAbs+L*(2*M+5)+2^x*N<2^H₂ at hH₂
    omega
  have hconst : (3*C).natAbs<2^H₃ := by
    rw [Int.natAbs_mul]
    change 3*C.natAbs<2^H₃
    change 3*(d.natAbs+L*(2*M+5))<2^H₃ at hH₃
    omega
  have hInt : (b:Int)=((2:Int)^m+3)*(q:Int)+3*(2:Int)^w+(w:Int)+3 := by
    dsimp [m]
    exact_mod_cast hp
  have hpowInt : (2:Int)^m=2*(2:Int)^w := by dsimp [m]; rw [Int.pow_succ,Int.mul_comm]
  have hdiv : denominator m∣2*(b:Int)+5-2*(m:Int) := by
    refine ⟨2*(q:Int)+3,?_⟩
    unfold denominator
    dsimp [m] at *
    grind
  have hdivL : denominator m∣(L:Int)*(2*(b:Int)+5-2*(m:Int)) := Int.dvd_mul_of_dvd_right hdiv
  have he : c*2^a*(P:Int)+C=(L:Int)*(2*(b:Int)+5-2*(m:Int)) := by dsimp [c,C]; grind
  rw [←he] at hdivL
  have hdivA : denominator m∣((2:Int)^a+3)*(c*2^a*(P:Int)+C) := Int.dvd_mul_of_dvd_right hdivL
  have hE : (2:Int)^((2*r+1)*a)=((2:Int)^a)^(2*r)*(2:Int)^a := by
    rw [Nat.add_mul,Nat.one_mul,Int.pow_add,Nat.mul_comm (2*r),Int.pow_mul]
  have heA : ((2:Int)^a+3)*(c*2^a*(P:Int)+C)=value [(c,(2*r+1)*a),(C-c*(N:Int),a),(3*C,0)] := by
    simp only [value,Int.pow_zero,Int.mul_one,Int.add_zero,hE]
    grind
  rw [heA] at hdivA
  have hcle : c.natAbs<2^(x+1) := by
    change ((2:Int)^x).natAbs<2^(x+1)
    rw [Int.natAbs_pow,Nat.pow_succ]
    change 2^x<2^x*2
    have hp := Nat.two_pow_pos x
    omega
  have h := affine_even_quadratic_or_divisors m ((2*r+1)*a) a x (x+1) H₂ H₃ (N:Int) C
    hm hx (by simpa using Nat.mul_le_mul_right a (show 1≤2*r+1 by omega)) hCodd hcle hmid hconst hdivA
  exact h

#print axioms generic_affine_source_quadratic
end NeedleRotation.Asymmetric
