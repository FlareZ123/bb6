import CancellationTopConstructive
import Lean.Elab.Tactic.Omega

/-! An all-parameter residue-cylinder non-parent theorem for the
Space Needle cancellation family. The proof is purely symbolic and
excludes four of every twenty valuation residues, for all r >= 1. -/

namespace CancellationModFive
open CancellationNat CancellationGap CancellationStrip CancellationConstructive

theorem pow9_mod8 (r:Nat) : 9^r%8=1 := by
  induction r with
  |zero => decide
  |succ r ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem valuation_mod4 (r:Nat) : valuationA r%4=3 := by
  have h := valuationA_double r
  have hp := pow9_mod8 r
  omega

theorem pow2_mod5_four_plus_three (k:Nat) : 2^(4*k+3)%5=3 := by
  induction k with
  |zero => decide
  |succ k ih =>
    have hh : 4*(k+1)+3=(4*k+3)+4 := by omega
    rw [hh,Nat.pow_add,Nat.mul_mod,ih]

theorem pow2_mod5_four_plus_one (k:Nat) : 2^(4*k+1)%5=2 := by
  induction k with
  |zero => decide
  |succ k ih =>
    have hh : 4*(k+1)+1=(4*k+1)+4 := by omega
    rw [hh,Nat.pow_add,Nat.mul_mod,ih]

theorem A_mod5 (r:Nat) : 2^(valuationA r)%5=3 := by
  have h := valuation_mod4 r
  have hrepr : valuationA r=4*(valuationA r/4)+3 := by omega
  rw [hrepr]
  exact pow2_mod5_four_plus_three _

theorem P_mod5 (A r:Nat) (hA:3≤A) (hm:A%5=3) : P A r%5=0 := by
  have hsub : (A-3)%5=0 := by omega
  induction r with
  |zero => simp [P]
  |succ r ih =>
    have hfirst : (A*A*P A r)%5=0 := by
      rw [Nat.mul_mod,ih]
      simp
    have hsecond : (9^r*(A-3))%5=0 := by
      rw [Nat.mul_mod,hsub]
      simp
    change (A*A*P A r+9^r*(A-3))%5=0
    rw [Nat.add_mod,hfirst,hsecond]

theorem uniform_inverse_mod5 (r u:Nat) (hr:1≤r)
    (hupper : u+1≤2*r*valuationA r)
    (hfour : u%4=0) (hfive : u%5≠4) :
    ¬ (2^(u+1)+3) ∣
      (2^(valuationA r)*P (2^(valuationA r)) r+3-2*u) := by
  let a:=valuationA r
  let A:=2^a
  let Q:=P A r
  have ha:=valuationA_linear r
  have hA8:8≤A := by
    have hpow := exp_mono 3 a (by omega)
    dsimp [A]
    omega
  have hA3:3≤A := by omega
  have hA5:A%5=3 := A_mod5 r
  have hQ5:Q%5=0 := P_mod5 A r hA3 hA5
  have hQpos:0<Q := CancellationStrip.P_pos A r (by omega : 4≤A) hr
  have hAP:A≤A*Q := Nat.le_mul_of_pos_right A hQpos
  have h2u:2*u≤A := by
    have hmul:2*(u+1)≤4*r*a := by
      calc
        2*(u+1)≤2*(2*r*a) := Nat.mul_le_mul_left 2 hupper
        _ = 4*r*a := by simp [Nat.mul_left_comm, Nat.mul_comm]
    have hlin : (4*r+2)*a = 4*r*a+2*a := Nat.add_mul (4*r) 2 a
    have hdomin : (4*r+2)*a≤A := power_dominates_linear r
    omega
  have hAQP : (A*Q)%5=0 := by
    rw [Nat.mul_mod,hQ5]
    simp
  have hD5 : (2^(u+1)+3)%5=0 := by
    have hu : u=4*(u/4) := by omega
    rw [hu]
    have hh:4*(u/4)+1 = u+1 := by omega
    have hp:=pow2_mod5_four_plus_one (u/4)
    omega
  intro hd
  have hfiveD : 5∣ 2^(u+1)+3 := Nat.dvd_of_mod_eq_zero hD5
  have hfiveN : 5∣ A*Q+3-2*u := Nat.dvd_trans hfiveD hd
  have hN5:(A*Q+3-2*u)%5=0 := Nat.mod_eq_zero_of_dvd hfiveN
  have hnoTrunc:2*u≤A*Q+3 := by omega
  have hsum:(A*Q+3-2*u)+2*u=A*Q+3 := Nat.sub_add_cancel hnoTrunc
  have hAm5:(A*Q+3)%5=3 := by omega
  have hUres:u%5=4 := by omega
  exact hfive hUres

theorem constructed_inverse_mod5 (r u : Nat) (hr : 1≤r)
    (hupper : u+1≤2*r*valuationA r)
    (hfour : u%4=0) (hfive : u%5≠4) :
    ¬ (2^(u+1)+3) ∣
      (2^(valuationA r)*(2*feederQ r+3)+3-2*u) := by
  rw [feederQ_spec r hr]
  exact uniform_inverse_mod5 r u hr hupper hfour hfive

#print axioms constructed_inverse_mod5
#print axioms uniform_inverse_mod5
end CancellationModFive
