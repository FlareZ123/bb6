import HighEvenRightArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19HighEvenRight

/-- Residues of the high target cylinder with x+y = 7 (mod 8). -/
theorem sum7_target_residues (q r : Nat) :
    let j := 32*q+8
    let m := 32*r+5
    let k := highK j m
    let x := 2*j+3
    12≤k ∧ k%8=4 ∧ (x+k)%8=7 ∧ (x+k+1)%32=24 ∧ x%4=3 := by
  let j : Nat := 32*q+8
  let m : Nat := 32*r+5
  let N : Nat := 2^(2*m+2)
  let k : Nat := N*(j+3)-(j+3*m+5)
  let x : Nat := 2*j+3
  change 12≤k ∧ k%8=4 ∧ (x+k)%8=7 ∧ (x+k+1)%32=24 ∧ x%4=3
  have hNbound : 4*m+4≤N := by dsimp [N]; exact power_linear_bound m
  have hN8 : 8∣N := by
    dsimp [N]
    change (2:Nat)^3 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow (a:=2) (m:=3) (n:=2*m+2) (by omega)
  have hN32 : 32∣N := by
    dsimp [N]
    change (2:Nat)^5 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow (a:=2) (m:=5) (n:=2*m+2) (by omega)
  have hNpos : 1≤N := by omega
  have hscore : j+3*m+5≤N*(j+3) := by
    dsimp [N]
    exact high_score_bound j m
  have hstop : k+j+3*m+5=N*(j+3) := by
    dsimp [k]
    omega
  have hmul : N*(j+3)=N*j+3*N := by
    rw [Nat.mul_add]
    omega
  have hjmul : j≤N*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hNpos
  have h3mul : 3*(4*m+4)≤3*N := Nat.mul_le_mul_left 3 hNbound
  have hk12 : 12≤k := by
    rw [hmul] at hstop
    omega
  have hNmod8 : N%8=0 := Nat.mod_eq_zero_of_dvd hN8
  have hNmod32 : N%32=0 := Nat.mod_eq_zero_of_dvd hN32
  have hprod8 : (N*(j+3))%8=0 := by
    rw [Nat.mul_mod,hNmod8]
    simp
  have hprod32 : (N*(j+3))%32=0 := by
    rw [Nat.mul_mod,hNmod32]
    simp
  have hstopmod8 : (k+j+3*m+5)%8=0 := by rw [hstop]; exact hprod8
  have hterm8 : (j+3*m+5)%8=4 := by dsimp [j,m]; omega
  have hk8 : k%8=4 := by omega
  have hj8 : j%8=0 := by dsimp [j]; omega
  have hxk8 : (x+k)%8=7 := by dsimp [x]; omega
  have hS : x+k+1=(N*(j+3)+j)-(3*m+1) := by
    dsimp [x]
    omega
  have hAmod : (N*(j+3)+j)%32=8 := by
    rw [Nat.add_mod,hprod32]
    dsimp [j]
    omega
  have hBmod : (3*m+1)%32=16 := by dsimp [m]; omega
  have hAdiv : 32*((N*(j+3)+j)/32)+8=N*(j+3)+j := by
    have h := Nat.mod_add_div (N*(j+3)+j) 32
    rw [hAmod] at h
    omega
  have hBdiv : 32*((3*m+1)/32)+16=3*m+1 := by
    have h := Nat.mod_add_div (3*m+1) 32
    rw [hBmod] at h
    omega
  have hS32 : (x+k+1)%32=24 := by
    rw [hS,←hAdiv,←hBdiv]
    omega
  have hx4 : x%4=3 := by dsimp [x,j]; omega
  exact ⟨hk12,hk8,hxk8,hS32,hx4⟩

/-- If a target has the displayed sum-seven residues, both its direct
    even-right predecessor and its exceptional odd-bounce predecessor
    have odd right coordinate and sum 2 modulo 4. -/
theorem sum7_parent_coordinates (x y : Nat) (hy12 : 12≤y)
    (hy8 : y%8=4) (hx4 : x%4=3)
    (hS32 : (x+y+1)%32=24) :
    let d := (y-2)/2
    let a := (x+y+1-12)/4
    let b := (3*a+y+1)/2
    5≤d ∧ d%2=1 ∧ (x+y-2+d)%4=2 ∧
    3≤a ∧ a%8=3 ∧ 5≤b ∧ b%4=3 ∧ (a+b)%4=2 := by
  let S := x+y+1
  let d := (y-2)/2
  let a := (S-12)/4
  let b := (3*a+y+1)/2
  have hS16 : S%16=8 := by dsimp [S] at *; omega
  have hSge : 12≤S := by dsimp [S]; omega
  have hSmod4 : S%4=0 := by omega
  have hdmod : (y-2)%2=0 := by omega
  have hddiv : 2*d=y-2 := by
    dsimp [d]
    have h:=Nat.mod_add_div (y-2) 2
    rw [hdmod] at h
    omega
  have hd5 : 5≤d := by
    dsimp [d]
    apply (Nat.le_div_iff_mul_le (k:=2) (x:=5) (y:=y-2) (by decide)).2
    omega
  have hdodd : d%2=1 := by omega
  have hdSum : (x+y-2+d)%4=2 := by omega
  have hdivA : (S-12)%4=0 := by omega
  have hAdiv : 4*a=S-12 := by
    dsimp [a]
    have h:=Nat.mod_add_div (S-12) 4
    rw [hdivA] at h
    omega
  have hAeq : S=4*a+12 := by omega
  have ha3 : 3≤a := by
    dsimp [a]
    apply (Nat.le_div_iff_mul_le (k:=4) (x:=3) (y:=S-12) (by decide)).2
    omega
  have ha8 : a%8=3 := by omega
  have hbmod2 : (3*a+y+1)%2=0 := by omega
  have hBdiv : 2*b=3*a+y+1 := by
    dsimp [b]
    have h:=Nat.mod_add_div (3*a+y+1) 2
    rw [hbmod2] at h
    omega
  have hb5 : 5≤b := by
    dsimp [b]
    apply (Nat.le_div_iff_mul_le (k:=2) (x:=5) (y:=3*a+y+1) (by decide)).2
    omega
  have hb4 : b%4=3 := by omega
  have hsum : (a+b)%4=2 := by omega
  exact ⟨hd5,hdodd,hdSum,ha3,ha8,hb5,hb4,hsum⟩

end BB6.Agent19HighEvenRight
