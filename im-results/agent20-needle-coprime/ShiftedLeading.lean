import GenericHistory

namespace NeedleRotation.Asymmetric

/-- Absorb the leading binary power into its exponent before sizing the
    forbidden intervals. Beyond the quadratic cutoff we get both a residue
    collision and a ternary divisibility restriction, not a disjunction
    between the two. -/
theorem shifted_leading_cutoff (m E a H₂ H₃ : Nat) (B C : Int)
    (hm : 0<m) (ha : a≤E) (hBodd : B%2=1) (hCodd : C%2=1)
    (hB : B.natAbs<2^H₂) (hC : (3*C).natAbs<2^H₃)
    (hd : denominator m∣value [(1,E),(B,a),(3*C,0)]) :
    5*(m*m)≤5*(H₂+H₃+23)*m+8*(E+a) ∨
      ((m∣E-a ∨ m∣E ∨ m∣a) ∧ (3:Int)^(a/m)∣3*C) := by
  by_cases hsmall : m≤width m E 1+width m a H₂+width m 0 H₃
  · left
    have h:=width_quadratic m E a 1 H₂ H₃ hm hsmall
    simpa only [show 1+H₂+H₃+22=H₂+H₃+23 by omega] using h
  · right
    have hsize : width m E 1+width m a H₂+width m 0 H₃<m := by omega
    have hodd : (3*C)%2=1 := by rw [Int.mul_emod,hCodd]; decide
    have h := asymmetric_resonance_or_small m E a 0 0 0 1 H₂ H₃ 1 B (3*C)
      (by decide) hBodd hodd (by decide) (by simpa using hB) (by simpa using hC)
      (by simpa using hd)
    refine ⟨?_,constant_dvd_of_width_sum m a E a 1 H₂ H₃ 1 B (3*C) ha (by omega) (by decide) hB hC hsize hd⟩
    rcases h with h|h|h|h
    · omega
    · exact Or.inl (residue_dvd_sub m E a ha (by simpa using h))
    · exact Or.inr (Or.inl (Nat.dvd_of_mod_eq_zero (by simpa using h)))
    · exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero (by simpa using h)))

/-- A large ordinary-cutoff exception below a/(2r+1) must meet the unique
    N=9^r congruence (when the affine denominator is coprime to 3). -/
theorem ternary_low_exception (r a m : Nat) (C : Int)
    (hsmall : 2*r+1≤a/m) (hdiv : (3:Int)^(a/m)∣3*C) :
    (9:Int)^r∣C := by
  have hp : (3:Int)^(2*r+1)∣(3:Int)^(a/m) := by
    refine ⟨(3:Int)^(a/m-(2*r+1)),?_⟩
    rw [←Int.pow_add,show 2*r+1+(a/m-(2*r+1))=a/m by omega]
  have hh := Int.dvd_trans hp hdiv
  obtain ⟨k,hk⟩:=hh
  refine ⟨k,?_⟩
  rw [Int.pow_succ,Int.pow_mul] at hk
  change 3*C=((3:Int)^2)^r*3*k at hk
  change C=((3:Int)^2)^r*k
  rw [show ((3:Int)^2)^r*3*k=3*(((3:Int)^2)^r*k) by grind] at hk
  omega

/-- The low-side resonance is one residue class modulo N: any two m
    passing it differ by a multiple of N, as gcd(2L,N)=1. -/
theorem low_exception_unique (N L m n : Nat) (d : Int) (_hN : 0<N)
    (hc : Nat.Coprime (2*L) N) (hm : m<N) (hn : n<N)
    (h₁ : (N:Int)∣d+(L:Int)*(5-2*(m:Int)))
    (h₂ : (N:Int)∣d+(L:Int)*(5-2*(n:Int))) : m=n := by
  have hd := Int.dvd_sub h₁ h₂
  have he : (d+(L:Int)*(5-2*(m:Int)))-(d+(L:Int)*(5-2*(n:Int))) = (2*(L:Int))*((n:Int)-(m:Int)) := by grind
  rw [he] at hd
  have hnat := Int.natAbs_dvd_natAbs.mpr hd
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at hnat
  change N∣2*L*((n:Int)-(m:Int)).natAbs at hnat
  have hdif := hc.symm.dvd_of_dvd_mul_left hnat
  have hlt : ((n:Int)-(m:Int)).natAbs<N := by omega
  have hz : ((n:Int)-(m:Int)).natAbs=0 := by
    by_cases h:((n:Int)-(m:Int)).natAbs=0
    · exact h
    · have hle:=Nat.le_of_dvd (by omega : 0<((n:Int)-(m:Int)).natAbs) hdif
      omega
  omega

#print axioms shifted_leading_cutoff
#print axioms ternary_low_exception
#print axioms low_exception_unique
end NeedleRotation.Asymmetric
