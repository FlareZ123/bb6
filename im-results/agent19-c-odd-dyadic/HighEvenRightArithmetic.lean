import Lean.Elab.Tactic.Omega

namespace BB6.Agent19HighEvenRight

/-- The exact high stopping right coordinate. -/
def highK (j m : Nat) : Nat :=
  2^(2*m+2)*(j+3) - (j+3*m+5)

private theorem power_linear_bound (m : Nat) : 4*m+4 ≤ 2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+2 = (2*m+2)+2 := by omega
      rw [he, Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem high_score_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hN : 4*m+4 ≤ 2^(2*m+2) := power_linear_bound m
  have hNpos : 1 ≤ 2^(2*m+2) := by omega
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hNpos
  have h3 : 3*(4*m+4) ≤ 3*2^(2*m+2) := Nat.mul_le_mul_left 3 hN
  have hmul : 2^(2*m+2)*(j+3) = 2^(2*m+2)*j+3*2^(2*m+2) := by
    rw [Nat.mul_add]
    omega
  rw [hmul]
  omega

/-- Exact arithmetic of the first even-right predecessor for the
    previously uncovered high stopping residue class. -/
theorem high_even_right_parent_arithmetic (j m : Nat)
    (hm : 3≤m) (hm4 : m%4=3) (hj8 : j%8=(m+3)%8) :
    let k := highK j m
    let x := 2*j+3
    k%2=0 ∧ 6≤k ∧ (x+k)%8=3 ∧
    let x1 := x+k-2
    let y1 := (k-2)/2
    5≤y1 ∧ y1%2=1 ∧ (x1+y1)%4=2 := by
  let N : Nat := 2^(2*m+2)
  let k : Nat := N*(j+3)-(j+3*m+5)
  let x : Nat := 2*j+3
  let x1 : Nat := x+k-2
  let y1 : Nat := (k-2)/2
  change k%2=0 ∧ 6≤k ∧ (x+k)%8=3 ∧
    5≤y1 ∧ y1%2=1 ∧ (x1+y1)%4=2
  have hNbound : 4*m+4 ≤ N := by dsimp [N]; exact power_linear_bound m
  have hN1 : (2:Nat)^1 ∣ N := by
    dsimp [N]
    exact Nat.pow_dvd_pow (a:=2) (m:=1) (n:=2*m+2) (by omega)
  have hN2 : (2:Nat)^2 ∣ N := by
    dsimp [N]
    exact Nat.pow_dvd_pow (a:=2) (m:=2) (n:=2*m+2) (by omega)
  have hN3 : (2:Nat)^3 ∣ N := by
    dsimp [N]
    exact Nat.pow_dvd_pow (a:=2) (m:=3) (n:=2*m+2) (by omega)
  have hNmod2 : N%2=0 := by
    have h := Nat.mod_eq_zero_of_dvd hN1
    simpa only [show (2:Nat)^1=2 by decide] using h
  have hNmod4 : N%4=0 := by
    have h := Nat.mod_eq_zero_of_dvd hN2
    simpa only [show (2:Nat)^2=4 by decide] using h
  have hNmod8 : N%8=0 := by
    have h := Nat.mod_eq_zero_of_dvd hN3
    simpa only [show (2:Nat)^3=8 by decide] using h
  have hprod2 : (N*(j+3))%2=0 := by
    rw [Nat.mul_mod, hNmod2]
    simp
  have hprod4 : (N*(j+3))%4=0 := by
    rw [Nat.mul_mod, hNmod4]
    simp
  have hprod8 : (N*(j+3))%8=0 := by
    rw [Nat.mul_mod, hNmod8]
    simp
  have hscore : j+3*m+5 ≤ N*(j+3) := by
    dsimp [N]
    exact high_score_bound j m
  have hstop : k+j+3*m+5=N*(j+3) := by
    dsimp [k]
    omega
  have hm8 : m%8=3 ∨ m%8=7 := by omega
  have hj8' : j%8=6 ∨ j%8=2 := by
    rcases hm8 with h|h
    · have hplus : (m+3)%8=6 := by omega
      rw [hplus] at hj8
      omega
    · have hplus : (m+3)%8=2 := by omega
      rw [hplus] at hj8
      omega
  have hj2 : j%2=0 := by omega
  have hm2 : m%2=1 := by omega
  have hterm2 : (j+3*m+5)%2=0 := by omega
  have hk2 : k%2=0 := by omega
  have hterm4 : (j+3*m+5)%4=0 := by omega
  have hk4 : k%4=0 := by omega
  have hstopmod8 : (k+j+3*m+5)%8=0 := by
    rw [hstop]
    exact hprod8
  have hk6 : 6≤k := by
    have hNpos : 1≤N := by omega
    have hjmul : j≤N*j := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hNpos
    have h3mul : 3*(4*m+4)≤3*N := Nat.mul_le_mul_left 3 hNbound
    have hmul : N*(j+3)=N*j+3*N := by
      rw [Nat.mul_add]
      omega
    rw [hmul] at hstop
    omega
  have hxk8 : (x+k)%8=3 := by
    dsimp [x]
    omega
  have hdivmod : (k-2)%2=0 := by omega
  have hdiv : 2*y1=k-2 := by
    dsimp [y1]
    have h := Nat.mod_add_div (k-2) 2
    rw [hdivmod] at h
    omega
  have hy5 : 5≤y1 := by omega
  have hyodd : y1%2=1 := by omega
  have htwosum : (2*(x1+y1))%8=4 := by
    have hsum : 2*(x1+y1)=4*j+3*k := by
      dsimp [x1,x]
      omega
    rw [hsum]
    omega
  have hsum4 : (x1+y1)%4=2 := by omega
  exact ⟨hk2, hk6, hxk8, hy5, hyodd, hsum4⟩

end BB6.Agent19HighEvenRight
