import Lean.Elab.Tactic.Omega
import EExceptionalAppend

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000
set_option linter.unusedSimpArgs false

namespace BB6.EExceptionalTimed
open CryptidBoundary BB6.BoundaryPadding BB6.DRegularShift
open BB6.DRegularTimedShift

/-- Exact source E-double packet duration, with the special zero-pair case. -/
def eCost (m q : Nat) : Nat :=
  12*m*m+49*m+(if q=0 then 96 else 60+4*q)

theorem e_cost_source (m q : Nat) :
    eCost m q = BB6.Agent32EAll.duration m q := by
  cases q with
  | zero => simp [eCost,BB6.Agent32EAll.duration]
  | succ q =>
    simp [eCost,BB6.Agent32EAll.duration]
    omega

private theorem quad (m p c : Nat) :
    12*(m+p)*(m+p)+49*(m+p)+c =
      12*m*m+49*m+c+(24*m+49)*p+12*p*p := by
  have hm : p*m=m*p := Nat.mul_comm p m
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  omega

theorem eCost_shift (m q p : Nat) :
    eCost (m+p) q = eCost m q + (24*m+49)*p + 12*p*p := by
  unfold eCost
  simpa [Nat.add_assoc] using
    (quad m p (if q=0 then 96 else 60+4*q))

private theorem eight_square (k : Nat) : 8^k*8^k=64^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc
      8^(k+1)*8^(k+1) = (8^k*8^k)*(8*8) := by
        simp only [Nat.pow_succ]
        ac_rfl
      _ = 64^(k+1) := by rw [ih]; simp only [Nat.pow_succ]

private theorem combine (D E L Q M B p : Nat) :
    (D+L*(3*p)+Q*(3*p)*(3*p)) +
      (E+B*(M*p)+12*(M*p)*(M*p)) =
    (D+E)+(3*L+M*B)*p+(9*Q+12*M*M)*p*p := by
  have h1 : Q*(3*p)*(3*p)=(9*Q)*p*p := by
    calc
      Q*(3*p)*(3*p)=(3*3*Q)*p*p := by ac_rfl
      _=(9*Q)*p*p := by rfl
  have h2 : 12*(M*p)*(M*p)=(12*M*M)*p*p := by ac_rfl
  have h3 : L*(3*p)=(3*L)*p := by ac_rfl
  have h4 : B*(M*p)=(M*B)*p := by ac_rfl
  rw [h1,h2,h3,h4]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  omega
