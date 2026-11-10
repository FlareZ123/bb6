import NeedleGrowth
import Lean.Elab.Tactic.Omega
namespace NeedleGrowth

private theorem dyadic_increment_divisor (v w r R t : Nat)
    (ht : 0 < t) (hlt : t < 2^v)
    (heq : 2^v*r+t=2^w*R) : 2^w ≤ t := by
  by_cases h : w ≤ v
  · have hd : 2^w ∣ 2^v := Nat.pow_dvd_pow 2 h
    obtain ⟨u,hu⟩ := hd
    have hm : 2^w ∣ 2^v*r := by
      refine ⟨u*r,?_⟩
      rw [hu]
      simp only [Nat.mul_assoc]
    have hr : 2^w ∣ 2^v*r+t := by
      rw [heq]
      exact Nat.dvd_mul_right (2^w) R
    have htdiv : 2^w ∣ t := (Nat.dvd_add_iff_right hm).mpr hr
    exact Nat.le_of_dvd ht htdiv
  · have hv : v ≤ w := by omega
    have hd : 2^v ∣ 2^w := Nat.pow_dvd_pow 2 hv
    obtain ⟨u,hu⟩ := hd
    have hm : 2^v ∣ 2^v*r := Nat.dvd_mul_right _ _
    have hr : 2^v ∣ 2^v*r+t := by
      rw [heq,hu]
      refine ⟨u*R,?_⟩
      simp only [Nat.mul_assoc]
    have htdiv : 2^v ∣ t := (Nat.dvd_add_iff_right hm).mpr hr
    have hge := Nat.le_of_dvd ht htdiv
    omega

/-- Every pair of successful updates gains at least the square root
    of the initial shifted counter, in square form. -/
theorem two_step_square_gain {b c d : Nat}
    (hbc : Edge b c) (hcd : Edge c d) :
    b ≤ (d-b)^2 := by
  rcases hbc with ⟨q,v,hb,hc⟩
  rcases hcd with ⟨Q,w,hc2,hd⟩
  let a := 2^v
  let A := 2^w
  let r := 2*q+3
  let R := 2*Q+3
  let t := v+3*(q+1)
  let s := w+3*(Q+1)
  have ha : 0 < a := Nat.pow_pos (by omega)
  have hA : 0 < A := Nat.pow_pos (by omega)
  have ht : 0 < t := by dsimp [t]; omega
  have hs : 0 < s := by dsimp [s]; omega
  have hrt : r ≤ t := by dsimp [r,t]; omega
  have hRs : R ≤ s := by dsimp [R,s]; omega
  have hb' : b=a*r := by simpa [a,r] using hb
  have hc' : c=b+t := by dsimp [t]; omega
  have hc2' : c=A*R := by simpa [A,R] using hc2
  have hd' : d=c+s := by dsimp [s]; omega
  have hg : d-b = t+s := by omega
  by_cases hta : a ≤ t
  · have hbar : b ≤ t*t := by
      calc
        b = a*r := hb'
        _ ≤ t*t := Nat.mul_le_mul hta hrt
    rw [hg]
    have hts : t≤t+s := by omega
    have hsq := Nat.mul_le_mul hts hts
    calc
      b ≤ t*t := hbar
      _ ≤ (t+s)*(t+s) := hsq
      _ = (t+s)^2 := by simp [Nat.pow_succ]
  · have hlt : t < a := by omega
    have hh : a*r+t = A*R := by omega
    have hAt : A ≤ t := dyadic_increment_divisor v w r R t ht hlt hh
    have hbar : b ≤ t*s := by
      calc
        b ≤ c := by omega
        _ = A*R := hc2'
        _ ≤ t*s := Nat.mul_le_mul hAt hRs
    rw [hg]
    have hts : t ≤ t+s := by omega
    have hss : s ≤ t+s := by omega
    have hsq := Nat.mul_le_mul hts hss
    calc
      b ≤ t*s := hbar
      _ ≤ (t+s)*(t+s) := hsq
      _ = (t+s)^2 := by simp [Nat.pow_succ]

#print axioms NeedleGrowth.two_step_square_gain
end NeedleGrowth
