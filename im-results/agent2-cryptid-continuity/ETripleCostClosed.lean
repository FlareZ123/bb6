import Lean.Elab.Tactic.Omega
import ETripleLadderIndex
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

namespace BB6.ETripleCostClosed
open BB6.ETripleLadderSource
open BB6.ETripleLadderIndex

def a : Nat → Nat
  | 0 => 0
  | m+1 => 108*9^m + 64*a m

def b : Nat → Nat
  | 0 => 0
  | m+1 => 75*3^m + 8*b m

theorem a_closed (m : Nat) : 55*a m+108*9^m=108*64^m := by
  induction m with
  | zero => decide
  | succ m ih =>
    change 55*(108*9^m+64*a m)+108*9^(m+1)=108*64^(m+1)
    rw [Nat.pow_succ', Nat.pow_succ']
    omega

theorem b_closed (m : Nat) : b m+15*3^m=15*8^m := by
  induction m with
  | zero => decide
  | succ m ih =>
    change (75*3^m+8*b m)+15*3^(m+1)=15*8^(m+1)
    rw [Nat.pow_succ',Nat.pow_succ']
    omega

theorem cost_shift (k q : Nat) :
    cost k q = 12*(k+1)*(k+1)+25*(k+1)+21+6*q := by
  unfold cost
  calc
    _ = (12*k*k+24*k+12)+(25*k+25)+21+6*q := by omega
    _ = 12*(k+1)*(k+1)+25*(k+1)+21+6*q := by
      simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
      omega

theorem poly_step (A B m q P x : Nat) :
    (12*P*P*x*x+25*P*x+21+6*q) +
      (A*(8*x)*(8*x)+B*(8*x)+6*m*m+(6*(q+2)+15)*m)
    = (12*P*P+64*A)*x*x+(25*P+8*B)*x
       +6*(m+1)*(m+1)+(6*q+15)*(m+1) := by
  simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  omega

def poly (m u q : Nat) :=
  a m*(u+1)*(u+1)+b m*(u+1)+6*m*m+(6*q+15)*m

private theorem sq3 (m : Nat) : 3^m*3^m=9^m := by
  change 3^m*3^m=(3*3)^m
  rw [Nat.mul_pow]

theorem total_poly (m u q : Nat) : totalCost m u q = poly m u q := by
  induction m generalizing u q with
  | zero => simp [totalCost, poly, a, b]
  | succ m ih =>
    change cost (kIndex (m+1) u) q + totalCost m (8*u+7) (q+2) = poly (m+1) u q
    rw [ih (8*u+7) (q+2)]
    rw [cost_shift, index_plus_one]
    dsimp [poly,a,b]
    have hP2 : 12*(3^(m+1))*(3^(m+1)) = 108*9^m := by
      calc
        _ = 12*(3^(m+1)*3^(m+1)) := by ac_rfl
        _ = 12*9^(m+1) := by rw [sq3]
        _ = 108*9^m := by rw [Nat.pow_succ']; omega
    have hP1 : 25*3^(m+1)=75*3^m := by
      rw [Nat.pow_succ']
      omega
    have hU : 8*u+7+1=8*(u+1) := by omega
    rw [hU]
    rw [← hP2, ← hP1]
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (poly_step (a m) (b m) m q (3^(m+1)) (u+1))


/-- Exact closed form after clearing its denominator 55. -/
theorem total_closed (m u q : Nat) :
    55*totalCost m u q + 108*(u+1)*(u+1)*9^m + 825*(u+1)*3^m =
    108*(u+1)*(u+1)*64^m + 825*(u+1)*8^m +
      330*m*m + (330*q+825)*m := by
  rw [total_poly]
  have ha := congrArg (fun z : Nat => z*(u+1)*(u+1)) (a_closed m)
  have hb := congrArg (fun z : Nat => 55*z*(u+1)) (b_closed m)
  dsimp [poly]
  simp only [Nat.mul_add, Nat.add_mul] at ha hb ⊢
  simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at ha hb ⊢
  omega

#print axioms total_closed
#print axioms total_poly
#print axioms a_closed
#print axioms b_closed
end BB6.ETripleCostClosed
