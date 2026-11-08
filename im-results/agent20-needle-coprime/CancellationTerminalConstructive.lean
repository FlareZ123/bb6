import CancellationTopConstructive
import Lean.Elab.Tactic.Omega

namespace CancellationTerminalConstructive
open CancellationNat CancellationGap CancellationStrip CancellationConstructive

def feederV (r : Nat) : Nat := valuationA r - 1
def feederK (r : Nat) : Nat := 2*r*(valuationA r)-1

/-- An exact synthetic terminal feeder exists for every positive r, with
v=(9^r+3)/2 and K+1=r*(9^r+5), and the entire top inverse strip is excluded
by CancellationConstructive.constructed_all_r_top_no_parent. -/
theorem exact_terminal_feeder (r : Nat) (hr : 1 ≤ r) :
    2^(feederK r) =
      (2^(feederV r+1)+3)*feederQ r +
      3*2^(feederV r)+feederV r+3 := by
  let a := valuationA r
  let v := feederV r
  let K := feederK r
  let A := 2^a
  let q := feederQ r
  have ha := valuationA_linear r
  have ha1 : 1≤a := by omega
  have hv : v+1=a := by dsimp [v,feederV]; omega
  have hval : 2*v=9^r+3 := by
    have h := valuationA_double r
    dsimp [v,feederV]
    omega
  have hKpos : 1≤2*r*a := by
    have hrpos : 0 < 2*r := by omega
    have hapos : 0 < a := by omega
    have hmul : 0 < (2*r)*a := Nat.mul_pos hrpos hapos
    omega
  have hK : K+1=2*r*a := by
    dsimp [K,feederK]
    exact Nat.sub_add_cancel hKpos
  have hpow : 2^(K+1)=A^(2*r) := by
    rw [hK]
    dsimp [A]
    rw [←Nat.pow_mul]
    congr 1
    exact Nat.mul_comm _ _
  have hA : A=2*2^v := by
    dsimp [A]
    rw [←hv, Nat.pow_succ]
    omega
  have he : (A+3)*(2*q+3)+9^r=A^(2*r) :=
    feeder_equation r hr
  have hsource2 :
      2*((A+3)*q+3*2^v+v+3)=(A+3)*(2*q+3)+9^r := by
    have hmul : (A+3)*(2*q)=2*((A+3)*q) := by
      simp only [Nat.mul_left_comm]
    rw [Nat.mul_add (A+3) (2*q) 3, hmul]
    simp only [Nat.mul_add]
    omega
  have htwo : 2^(K+1)=2*(2^K) := by
    rw [Nat.pow_succ]
    omega
  change 2^K=(2^(v+1)+3)*q+3*2^v+v+3
  rw [hv]
  change 2^K=(A+3)*q+3*2^v+v+3
  omega

#print axioms exact_terminal_feeder
end CancellationTerminalConstructive
