import AffineDepthM8
import OddDepthGeneric
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11
open BB6.Agent15

/-- A family of second-branch Machine C stopping candidates excluded
    at arbitrary 2-adic inverse depth. The equality on j,m fixes the
    valuation and odd part of the forced affine predecessor; unlike
    any finite-modulus sieve, r has no upper bound. -/
theorem second_halt_arbitrary_depth (m k r j q : Nat)
    (hm : m%4=3) (hr : r+2≤m) (hqj : q≤j)
    (hX : j+3*m+3=2^(2*r+1)*(4*q+1))
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ CReach (2*j+3) k := by
  have hjEven : j%2=0 := by
    have hpow : 2∣2^(2*r+1) := by
      refine ⟨2^(2*r),?_⟩
      rw [Nat.pow_succ]
      ac_rfl
    have hmod : (j+3*m+3)%2=0 := by
      rw [hX]
      have hmul : 2 ∣ 2^(2*r+1)*(4*q+1) := by
        rcases hpow with ⟨z,hz⟩
        refine ⟨z*(4*q+1),?_⟩
        rw [hz]
        ac_rfl
      exact Nat.mod_eq_zero_of_dvd hmul
    omega
  have ha : (2*j+3)%4=3 := by omega
  have hpower4 : 4 ∣ 2^(2*m+2) := by
    have h : 2^2∣2^(2*m+2) := Nat.pow_dvd_pow 2 (by omega)
    simpa using h
  have hmod8 : ((2*j+3)+2*k)%8=7 := by
    have h2 : 4∣2^(2*m+2)*(j+3) := by
      rcases hpower4 with ⟨z,hz⟩
      refine ⟨z*(j+3),?_⟩
      rw [hz]
      ac_rfl
    have hprod : (2^(2*m+2)*(j+3))%4=0 := Nat.mod_eq_zero_of_dvd h2
    have hE : (k+j+3*m+5)%4=0 := by rw [hk]; exact hprod
    omega
  let P : Nat := 2^(2*r+1)
  let R : Nat := 2^(2*m-2*r-1)
  let T : Nat := R*(j+3)
  have hp : 2^(2*m+2)=P*(4*R) := by
    have he : 2*m+2=(2*r+3)+(2*m-2*r-1) := by omega
    have hP : 2^(2*r+3)=P*4 := by
      have hpExp : 2*r+3=(2*r+1)+2 := by omega
      rw [hpExp,Nat.pow_add]
    rw [he,Nat.pow_add,hP]
    change (P*4)*R=P*(4*R)
    ac_rfl
  have hT : q+2≤T := by
    have hRpos : 0<R := Nat.pow_pos (by decide)
    have hmul : j+3 ≤ R*(j+3) :=
      Nat.le_mul_of_pos_left (j+3) hRpos
    dsimp [T]
    omega
  have hpFact : 2^(2*m+2)*(j+3)=P*(4*T) := by
    rw [hp]
    dsimp [T]
    ac_rfl
  have hX' : j+3*m+3=P*(4*q+1) := hX
  have hEq : (k+2)+P*(4*q+1)=P*(4*T) := by
    rw [←hX',←hpFact]
    omega
  let Q : Nat := T-q-1
  have hQpos : 1≤Q := by dsimp [Q]; omega
  have hQeq : 4*Q+3+4*q+1=4*T := by dsimp [Q]; omega
  have hPpos : 0<P := Nat.pow_pos (by decide)
  have hK : k+2=P*(4*Q+3) := by
    have hsum : P*(4*Q+3)+P*(4*q+1)=P*(4*T) := by
      have hh := congrArg (fun v : Nat => P*v) hQeq
      have hrw : 4*Q+3+4*q+1=4*T := hQeq
      calc
        P*(4*Q+3)+P*(4*q+1) = P*((4*Q+3)+(4*q+1)) :=
          (Nat.mul_add P (4*Q+3) (4*q+1)).symm
        _ = P*(4*T) := by rw [show (4*Q+3)+(4*q+1)=4*T by omega]
    omega
  have hkEq : k=2^(2*r+1)*(4*Q+3)-2 := by
    change k= P*(4*Q+3)-2
    omega
  have hdepth : oddDepth k=2*r := by
    rw [hkEq]
    have hodd : 4*Q+3=2*(2*Q+1)+1 := by omega
    have hqraw : (2*Q+1)≥1 := by omega
    have he : (2*r+1)=(2*r)+1 := rfl
    have hh : 2^(2*r+1)*(4*Q+3)-2 =
        2^((2*r)+1)*(2*(2*Q+1)+1)-2 := by rw [hodd]
    rw [hh]
    exact oddDepth_odd_term (2*r) (2*Q+1) hqraw
  have hfact : ∃z, k+2=2^(oddDepth k)*(8*z+6) := by
    refine ⟨Q,?_⟩
    rw [hdepth]
    have hPower : P = 2^(2*r)*2 := Nat.pow_succ 2 (2*r)
    rw [hK,hPower]
    have hbr : 2*(4*Q+3)=8*Q+6 := by omega
    rw [Nat.mul_assoc,hbr]
  exact normalize_even_depth_m8_forbidden (2*j+3) k ha hmod8
    (by rw [hdepth]; omega) hfact

#print axioms second_halt_arbitrary_depth
end BB6.Agent11
