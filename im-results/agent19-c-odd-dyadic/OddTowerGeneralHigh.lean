import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Tower

private theorem pow_three_linear (m:Nat) : 3*m+3≤2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hp : 2^(2*(m+1)+2) = 4*2^(2*m+2) := by
      calc
        2^(2*(m+1)+2)=2^((2*m+2)+2) := by congr 1 <;> omega
        _=2^(2*m+2)*2^2 := Nat.pow_add ..
        _=4*2^(2*m+2) := by omega
    rw [hp]
    omega

private theorem complement_mod (z s d:Nat) (hd:0<d)
    (hs:s%(4*d)=d) (hzero:(z+s)%(4*d)=0) : z%(4*d)=3*d := by
  have hadd:(z%(4*d)+s%(4*d))%(4*d)=0 := by
    rw [←Nat.add_mod]
    exact hzero
  rw [hs] at hadd
  have hzlt : z%(4*d)<4*d := Nat.mod_lt _ (by omega)
  by_cases hsmall : z%(4*d)+d < 4*d
  · have hh : (z%(4*d)+d)%(4*d)=z%(4*d)+d := Nat.mod_eq_of_lt hsmall
    rw [hh] at hadd
    omega
  · have hlarge : 4*d≤z%(4*d)+d := by omega
    rw [Nat.mod_eq_sub_mod hlarge] at hadd
    have hsub : z%(4*d)+d-4*d<4*d := by omega
    rw [Nat.mod_eq_of_lt hsub] at hadd
    omega

/-- Exact high stopping modular arithmetic, uniformly in the exponent. -/
theorem high_all_depth_arithmetic (n j m k:Nat)
    (hm : n+4≤2*m+2)
    (hpair : (j+3*m+3)%2^(n+4)=2^(n+2))
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ∃w, 7≤w ∧ w%4=3 ∧ k=2^(n+2)*w-2 := by
  let d := 2^(n+2)
  let q := 2^(n+4)
  let b := 2^(2*m+2)
  let s := j+3*m+3
  let z := k+2
  have hd : 0<d := Nat.pow_pos (by decide)
  have hq : q=4*d := by
    dsimp [q,d]
    simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm]; omega
  have hsq : s%q=d := hpair
  have hdiv : q∣b := Nat.pow_dvd_pow 2 hm
  have hpdiv : q∣b*(j+3) := by
    rcases hdiv with ⟨t,ht⟩
    refine ⟨t*(j+3),?_⟩
    rw [ht]
    ac_rfl
  have hzsum : z+s=b*(j+3) := by
    dsimp [z,s,b] at *
    omega
  have hzmod0 : (z+s)%q=0 := by
    rw [hzsum]
    exact Nat.mod_eq_zero_of_dvd hpdiv
  have hzmod : z%(4*d)=3*d := by
    rw [hq] at hsq hzmod0
    exact complement_mod z s d hd hsq hzmod0
  have hrecon : z=3*d+(4*d)*(z/(4*d)) := by
    have hr := Nat.mod_add_div z (4*d)
    rw [hzmod] at hr
    omega
  let w := 4*(z/(4*d))+3
  have hwmod : w%4=3 := by dsimp [w]; omega
  have hzw : z=d*w := by
    calc
      z = 3*d+(4*d)*(z/(4*d)) := hrecon
      _ = d*w := by
        dsimp [w]
        simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        omega
  have hBbound : 4*d≤b := by
    have hp := Nat.pow_le_pow_right (by decide : 0<2) hm
    change q≤b at hp
    rw [hq] at hp
    exact hp
  have hbpositive : 0<b := Nat.pow_pos (by decide)
  have hjbound : j≤b*j := by
    have hh := Nat.mul_le_mul_right j (show 1≤b by omega)
    omega
  have hlin :3*m+3≤b := pow_three_linear m
  have hprod : b*(j+3)=b*j+3*b := by simp [Nat.mul_add,Nat.mul_comm]
  have hzlower : 7*d≤z := by
    rw [hprod] at hzsum
    dsimp [z,s] at hzsum
    omega
  have hwlower : 7≤w := by
    by_cases hh : 7≤w
    · exact hh
    · have hsmall : w≤6 := by omega
      have hscaled := Nat.mul_le_mul_left d hsmall
      omega
  refine ⟨w,hwlower,hwmod,?_⟩
  dsimp [z,d] at hzw
  omega

#print axioms high_all_depth_arithmetic
end BB6.Agent19Tower
