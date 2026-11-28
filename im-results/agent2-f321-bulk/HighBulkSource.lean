import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

/-!
Uniform source-counter high-branch accelerator for F321.
Single exact numeric guard (d+3)*2^j ≤ a+j+d+3 suffices to certify
j consecutive real CounterMove.high steps from arbitrary starting a,d.
No sampled traces, no original six-state blank liveness claim.
-/

namespace BB6.Agent2F321Bulk
open BB6.Agent31F321Density

def highD (d:Nat) : Nat → Nat
  | 0 => d
  | j+1 => 2*highD d j+3

def highCost (d:Nat) : Nat → Nat
  | 0 => 0
  | j+1 => highCost d j+highD d j+2

theorem highD_closed (d j:Nat) :
    highD d j+3=(d+3)*2^j := by
  induction j with
  | zero => simp [highD]
  | succ j ih =>
    have hpow : (d+3)*2^(j+1)=2*((d+3)*2^j) := by
      simp [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [hpow]
    change 2*highD d j+3+3=2*((d+3)*2^j)
    omega

/-- The high-run cost has a closed form without any potentially truncated
Nat subtraction; it is the difference of an exponential and its index. -/
theorem highCost_closed (d j:Nat) :
    highCost d j+j+d+3=(d+3)*2^j := by
  induction j with
  | zero => simp [highCost]
  | succ j ih =>
    have hpow : (d+3)*2^(j+1)=2*((d+3)*2^j) := by
      simp [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    have hd := highD_closed d j
    rw [hpow]
    change (highCost d j+highD d j+2)+(j+1)+d+3=2*((d+3)*2^j)
    omega

/-- Exact enough high cost in the starting a-counter is NECESSARY
and SUFFICIENT for the entire j-step high-run macro. -/
theorem high_guard_iff (a d j:Nat) :
    highCost d j≤a ↔ (d+3)*2^j≤a+j+d+3 := by
  have hc := highCost_closed d j
  omega

/-- Every sufficiently funded high run is source-certified at all j
without inspecting any intermediate counter pair. -/
theorem high_bulk (a d j:Nat)
    (h:highCost d j≤a) :
    CounterReach a d j (a-highCost d j) (highD d j) := by
  induction j with
  | zero =>
    simpa [highCost,highD] using
      (CounterReach.nil : CounterReach a d 0 a d)
  | succ j ih =>
    have hstep : highCost d (j+1)=highCost d j+highD d j+2 := by
      rfl
    have hprev : highCost d j≤a := by omega
    have hr:=ih hprev
    have hg : highD d j+2≤a-highCost d j := by omega
    have hm:CounterMove (a-highCost d j) (highD d j)
       ((a-highCost d j)-highD d j-2) (2*highD d j+3) :=
      CounterMove.high _ _ hg
    have hs:=CounterReach.step hr hm
    have heqA :
        (a-highCost d j)-highD d j-2 =
        a-highCost d (j+1) := by omega
    have heqD :
        2*highD d j+3=highD d (j+1) := rfl
    simpa only [heqA,heqD] using hs

/-- The paper-level closed expression gives a one-line original-source
CounterReach certificate. The guard is itself a single comparison
involving a power of two, not a length-j list of guard hypotheses. -/
theorem high_bulk_closed (a d j:Nat)
    (h:(d+3)*2^j≤a+j+d+3) :
    CounterReach a d j (a-highCost d j) ((d+3)*2^j-3) := by
  have hh := high_bulk a d j ((high_guard_iff a d j).mpr h)
  have hd:=highD_closed d j
  have hD' : highD d j=(d+3)*2^j-3 := by omega
  simpa only [hD'] using hh

#print axioms highD_closed
#print axioms highCost_closed
#print axioms high_guard_iff
#print axioms high_bulk
#print axioms high_bulk_closed

end BB6.Agent2F321Bulk
