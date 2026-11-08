import CancellationTopStrip
import Lean.Elab.Tactic.Omega

namespace CancellationConstructive
open CancellationNat CancellationGap CancellationStrip

def feederQ (r : Nat) : Nat :=
  (P (2^(valuationA r)) r-3)/2

theorem P_odd (A r : Nat) (hA : 4≤A) (hEven : A%2=0) (hr : 1≤r) :
    P A r %2=1 := by
  cases r with
  | zero => omega
  | succ r =>
    have hsub : (A-3)%2=1 := by omega
    have h9 : 9^r%2=1 := nine_pow_odd r
    have hfirst : (A*A*P A r)%2=0 := by
      have hAA : (A*A)%2=0 := by rw [Nat.mul_mod,hEven]
      rw [Nat.mul_mod,hAA]
      simp
    have hsecond : (9^r*(A-3))%2=1 := by
      rw [Nat.mul_mod,h9,hsub]
    change (A*A*P A r+9^r*(A-3))%2=1
    rw [Nat.add_mod,hfirst,hsecond]

theorem P_ge_three (A r : Nat) (hA : 8≤A) (hr : 1≤r) :
    3≤P A r := by
  cases r with
  | zero => omega
  | succ r =>
    have hp : 1≤9^r := Nat.pow_pos (by decide)
    have hmul : (A-3) ≤ 9^r*(A-3) := by
      simpa using Nat.mul_le_mul_right (A-3) hp
    simp only [P]
    omega

theorem feederQ_spec (r : Nat) (hr : 1≤r) :
    2*feederQ r+3=P (2^(valuationA r)) r := by
  let A:=2^(valuationA r)
  have ha := valuationA_linear r
  have hA : 8≤A := by
    have hp := exp_mono 3 (valuationA r) (by omega)
    dsimp [A]
    omega
  have hEven : A%2=0 := by
    dsimp [A]
    rw [show valuationA r=(valuationA r-1)+1 by omega]
    rw [Nat.pow_succ,Nat.mul_mod]
    omega
  have hPodd := P_odd A r (by omega) hEven hr
  have hP3 := P_ge_three A r hA hr
  dsimp [feederQ]
  change 2*((P A r-3)/2)+3=P A r
  omega

theorem feeder_equation (r : Nat) (hr : 1≤r) :
    (2^(valuationA r)+3)*(2*feederQ r+3)+9^r =
      (2^(valuationA r))^(2*r) := by
  rw [feederQ_spec r hr]
  have ha := valuationA_linear r
  exact CancellationNat.exact (2^(valuationA r)) r
    (by have hp:=exp_mono 3 (valuationA r) (by omega); omega)

/-- The constructed cancellation odd-part exists for every positive r,
and its highest-valuation inverse-parent strip is empty. -/
theorem constructed_all_r_top_no_parent (r u : Nat) (hr : 1≤r)
    (hlow : (2*r-1)*valuationA r+3 ≤ u+1)
    (hhigh : u+1 ≤ (2*r)*valuationA r) :
    ¬ (2^(u+1)+3) ∣
      (2^(valuationA r)*(2*feederQ r+3)+3-2*u) := by
  exact cancellation_top_no_parent_source_equation r u (feederQ r)
    hr hlow hhigh (feeder_equation r hr)

#print axioms constructed_all_r_top_no_parent
#print axioms feeder_equation
end CancellationConstructive
