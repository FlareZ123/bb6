import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

/-!
Uniform original source-counter Far-branch accelerator for F321.
One exact numeric exponential guard certifies j arbitrary consecutive
Far steps, without inspecting the intermediate counter pairs.
-/
namespace BB6.Agent2F321Bulk
open BB6.Agent31F321Density

def farA (a:Nat) : Nat → Nat
  | 0 => a
  | j+1 => 4*farA a j+6

def farCost (a:Nat) : Nat → Nat
  | 0 => 0
  | j+1 => farCost a j+3*farA a j

theorem farA_closed (a j:Nat) :
    farA a j+2=(a+2)*4^j := by
  induction j with
  | zero => simp [farA]
  | succ j ih =>
    have hpow : (a+2)*4^(j+1)=4*((a+2)*4^j) := by
      simp [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [hpow]
    change 4*farA a j+6+2=4*((a+2)*4^j)
    omega

/-- Closed cumulative cost of the first j Far branches, with natural
arithmetic and no truncating subtraction in the certificate statement. -/
theorem farCost_closed (a j:Nat) :
    farCost a j+6*j+a+2=(a+2)*4^j := by
  induction j with
  | zero => simp [farCost]
  | succ j ih =>
    have hpow : (a+2)*4^(j+1)=4*((a+2)*4^j) := by
      simp [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    have ha:=farA_closed a j
    rw [hpow]
    change (farCost a j+3*farA a j)+6*(j+1)+a+2 =
      4*((a+2)*4^j)
    omega

theorem far_guard_iff (a d j:Nat) :
    farCost a j+1≤d ↔
      (a+2)*4^j≤a+d+6*j+1 := by
  have hc:=farCost_closed a j
  omega

/-- Uniform exact original-source Far return block. The guard is
both a lower-bound certificate for every intermediate second counter
and a proof that the Far branch is selected at each step. -/
theorem far_bulk (a d j:Nat)
    (h:farCost a j+1≤d) :
    CounterReach a d j (farA a j) (d-farCost a j) := by
  induction j with
  | zero =>
    simpa [farA,farCost] using
      (CounterReach.nil : CounterReach a d 0 a d)
  | succ j ih =>
    have hstep : farCost a (j+1)=farCost a j+3*farA a j := rfl
    have hprev : farCost a j+1≤d := by omega
    have hr:=ih hprev
    have hg : 3*farA a j+1≤d-farCost a j := by omega
    have hlt : farA a j<d-farCost a j := by omega
    have hm : CounterMove (farA a j) (d-farCost a j)
      (4*farA a j+6) ((d-farCost a j)-3*farA a j) :=
      CounterMove.far _ _ hlt hg
    have hs:=CounterReach.step hr hm
    have hA : 4*farA a j+6=farA a (j+1) := rfl
    have hD : (d-farCost a j)-3*farA a j =
        d-farCost a (j+1) := by omega
    simpa only [hA,hD] using hs

/-- Single-power-of-four guard yielding a complete genuine source
Far block, with closed expressions for both output counters. -/
theorem far_bulk_closed (a d j:Nat)
    (h:(a+2)*4^j≤a+d+6*j+1) :
    CounterReach a d j
      ((a+2)*4^j-2)
      (a+d+6*j+2-(a+2)*4^j) := by
  have hc:=farCost_closed a j
  have hh:=far_bulk a d j ((far_guard_iff a d j).mpr h)
  have hA : farA a j=(a+2)*4^j-2 := by
    have he:=farA_closed a j
    omega
  have hD : d-farCost a j =
      a+d+6*j+2-(a+2)*4^j := by omega
  simpa only [hA,hD] using hh

#print axioms farA_closed
#print axioms farCost_closed
#print axioms far_guard_iff
#print axioms far_bulk
#print axioms far_bulk_closed
end BB6.Agent2F321Bulk
