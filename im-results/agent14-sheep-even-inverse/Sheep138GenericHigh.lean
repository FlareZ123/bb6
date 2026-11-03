import Sheep138Gateway
import SheepOddGap
import HighBound

namespace Sheep138GenericHigh

private theorem gap_from_integral_nat (a n D K v : Nat)
    (hK : 1<K) (hodd : K%2=1) (hhigh : K<2^a)
    (heq : (2^(a+1)+1)*(D*v)+K=2^n) : False := by
  have hKi : (1:Int)<(K:Int) := by exact_mod_cast hK
  have hOddi : (K:Int)%2=1 := by exact_mod_cast hodd
  have hHighi : (K:Int)<(2:Int)^a := by exact_mod_cast hhigh
  have hgap := (SheepOddGap.no_power_signed_small_odd a (K:Int)
    hKi hOddi hHighi n).1
  have hcast : ((2:Int)^(a+1)+1)*(D*v:Int)+(K:Int)=(2:Int)^n := by
    exact_mod_cast heq
  have hdiv : ((2:Int)^(a+1)+1) ∣ (2:Int)^n-(K:Int) := by
    refine ⟨(D*v:Int),?_⟩
    omega
  exact hgap hdiv

/-- All r=138 root generic h=0 parents with a>=2 are impossible. -/
theorem high_h0 (j a v u : Nat) (ha : 2≤a)
    (hy : 2^j=1+u)
    (hz : 2*(1+u)+1=(2^(a+1)+1)*v+2*a) : False := by
  have heq : (2^(a+1)+1)*v+(2*a-1)=2^(j+1) := by
    have hp : 2^(j+1)=2*2^j := by rw [Nat.pow_succ]; omega
    omega
  have hb := SheepEvenBound.node0_h0_high a ha
  have hQ : SheepEvenBound.Q 1 (-1) a=(2*a-1:Int) := by
    simp [SheepEvenBound.Q]
    omega
  have hK : 1<2*a-1 ∧ 2*a-1<2^a := by
    rw [hQ] at hb
    omega
  have hodd : (2*a-1)%2=1 := by omega
  exact gap_from_integral_nat a (j+1) 1 (2*a-1) v hK.1 hodd hK.2
    (by simpa using heq)

/-- All r=138 root generic h=1 parents with a>=5 are impossible. -/
theorem high_h1 (j a v u : Nat) (ha : 5≤a)
    (hy : 2^j=1+3*u)
    (hz : 2*(1+2*u)+1=(2^(a+1)+1)*v+2*a) : False := by
  have heq : (2^(a+1)+1)*(3*v)+(6*a-5)=2^(j+2) := by
    have hp : 2^(j+2)=4*2^j := by
      rw [show j+2=j+1+1 by omega,Nat.pow_succ,Nat.pow_succ]
      omega
    have hm : 3*((2^(a+1)+1)*v)=(2^(a+1)+1)*(3*v) := by ac_rfl
    omega
  have hb := SheepEvenBound.node0_h1_high a ha
  have hQ : SheepEvenBound.Q 3 (-5) a=(6*a-5:Int) := by
    simp [SheepEvenBound.Q]
    omega
  have hK : 1<6*a-5 ∧ 6*a-5<2^a := by
    rw [hQ] at hb
    omega
  have hodd : (6*a-5)%2=1 := by omega
  exact gap_from_integral_nat a (j+2) 3 (6*a-5) v hK.1 hodd hK.2 heq

/-- All r=138 root generic h=2 parents with a>=7 are impossible. -/
theorem high_h2 (j a v u : Nat) (ha : 7≤a)
    (hy : 2^j=1+9*u)
    (hz : 2*(1+4*u)+1=(2^(a+1)+1)*v+2*a) : False := by
  have heq : (2^(a+1)+1)*(9*v)+(18*a-19)=2^(j+3) := by
    have hp : 2^(j+3)=8*2^j := by
      rw [show j+3=j+1+1+1 by omega,Nat.pow_succ,Nat.pow_succ,Nat.pow_succ]
      omega
    have hm : 9*((2^(a+1)+1)*v)=(2^(a+1)+1)*(9*v) := by ac_rfl
    omega
  have hb := SheepEvenBound.node0_h2_high a ha
  have hQ : SheepEvenBound.Q 9 (-19) a=(18*a-19:Int) := by
    simp [SheepEvenBound.Q]
    omega
  have hK : 1<18*a-19 ∧ 18*a-19<2^a := by
    rw [hQ] at hb
    omega
  have hodd : (18*a-19)%2=1 := by omega
  exact gap_from_integral_nat a (j+3) 9 (18*a-19) v hK.1 hodd hK.2 heq

/-- Genuine blank-root r138 last parent: h=0 => a<=1,
h=1 => a<=4, and h=2 => a<=6. -/
theorem blank_root_finite_a (k : Nat)
    (hr : SheepEven.EvenReach 10 (2^(138+4860*k))) :
    ∃ x a h v u : Nat,
      SheepEven.EvenReach 10 x ∧
      1 ≤ a ∧ 5 ≤ v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧
      2^(138+4860*k)=1+3^h*u ∧
      2*(1+2^h*u)+1=(2^(a+1)+1)*v+2*a ∧
      ((h=0∧a≤1)∨(h=1∧a≤4)∨(h=2∧a≤6)) := by
  obtain ⟨x,a,h,v,u,hreach,hedge,ha,hh,hv,hvodd,hu,hx,hformula,hout⟩ :=
    Sheep138Gateway.blank_root_generic_predecessor k hr
  have cases : h=0∨h=1∨h=2 := by omega
  rcases cases with h0|h1|h2
  · subst h
    have hal : a≤1 := by
      by_cases hq : a≤1
      · exact hq
      · exact False.elim (high_h0 (138+4860*k) a v u (by omega)
          (by simpa using hout) (by simpa using hformula))
    exact ⟨x,a,0,v,u,hreach,ha,hv,hvodd,hu,hx,hout,hformula,Or.inl ⟨rfl,hal⟩⟩
  · subst h
    have hal : a≤4 := by
      by_cases hq : a≤4
      · exact hq
      · exact False.elim (high_h1 (138+4860*k) a v u (by omega) hout hformula)
    exact ⟨x,a,1,v,u,hreach,ha,hv,hvodd,hu,hx,hout,hformula,Or.inr (Or.inl ⟨rfl,hal⟩)⟩
  · subst h
    have hal : a≤6 := by
      by_cases hq : a≤6
      · exact hq
      · exact False.elim (high_h2 (138+4860*k) a v u (by omega) hout hformula)
    exact ⟨x,a,2,v,u,hreach,ha,hv,hvodd,hu,hx,hout,hformula,Or.inr (Or.inr ⟨rfl,hal⟩)⟩

#print axioms blank_root_finite_a
end Sheep138GenericHigh
