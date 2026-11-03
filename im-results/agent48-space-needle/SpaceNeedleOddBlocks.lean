import SpaceNeedleSourceMirror
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- Every high-level counter of the shape 2a−1 (a>0) makes a safe
odd-branch transition and has exact next counter 5a−1. -/
theorem odd_step (a : Nat) (ha : 0<a) :
    highLevelNext (.N (2*a-1))= some (.N (5*a-1)) := by
  have ho : (2*a-1)%2=1 := by omega
  have hf : (2*a-1)/2=a-1 := by omega
  by_cases h : a=1
  · subst a
    simp [highLevelNext,scanEven]
  · have hd : 2*a-1≠1 := by omega
    change scanEven (2*a-1) 0 = some (.N (5*a-1))
    rw [scanEven]
    simp only [ho, show ¬(1=0) by decide, ite_false, hd]
    rw [hf]
    simp only [Option.some.injEq, HighLevelState.N.injEq]
    omega

def runHigh : Nat → Option HighLevelState → Option HighLevelState
  | 0, x => x
  | n+1, x => runHigh n (x.bind highLevelNext)

/-- An entire block of t consecutive odd high-level counters is
compressed into one exact symbolic return. -/
theorem odd_block (t m : Nat) (hm : 0<m) :
    runHigh t (some (.N (2^t*m-1))) =
      some (.N (5^t*m-1)) := by
  induction t generalizing m with
  | zero => simp [runHigh]
  | succ t ih =>
      have hp : 0 < 2^t*m := by
        have hpow : 0 < 2^t := Nat.pow_pos (n:=t) (by omega : 0<2)
        exact Nat.mul_pos hpow hm
      change runHigh t ((some (.N (2^(t+1)*m-1))).bind highLevelNext) =
        some (.N (5^(t+1)*m-1))
      have hbase : 2^(t+1)*m=2*(2^t*m) := by
        simp [Nat.pow_succ', Nat.mul_assoc]
      rw [hbase]
      change runHigh t (highLevelNext (.N (2*(2^t*m)-1))) = _
      rw [odd_step (2^t*m) hp]
      have hi := ih (5*m) (by omega)
      simpa [Nat.pow_succ', Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hi

/-- A finite prefix of the odd block, with s remaining powers of two. -/
theorem odd_block_prefix (j s m : Nat) (hm : 0<m) :
    runHigh j (some (.N (2^(j+s)*m-1))) =
      some (.N (5^j*2^s*m-1)) := by
  have hp : 0 < 2^s*m := by
    exact Nat.mul_pos (Nat.pow_pos (n:=s) (by omega : 0<2)) hm
  have h := odd_block j (2^s*m) hp
  simpa [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

private theorem five_pow_odd (t : Nat) : 5^t%2=1 := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [Nat.pow_succ, Nat.mul_mod,ih]

/-- For odd m, the full t-step odd-state block exits at an even counter. -/
theorem odd_block_exits_even (t m : Nat) (hm : m%2=1) :
    (5^t*m-1)%2=0 := by
  have ho : (5^t*m)%2=1 := by
    rw [Nat.mul_mod,five_pow_odd,hm]
  have hp : 0 < 5^t*m := by
    have hpow : 0 < 5^t := Nat.pow_pos (n:=t) (by omega : 0<5)
    have hpos : 0<m := by omega
    exact Nat.mul_pos hpow hpos
  omega

/-- During an odd block, any proper prefix (with at least one remaining
factor of two) ends in an odd counter. -/
theorem odd_block_prefix_odd (j s m : Nat) (hm : 0<m) :
    (5^j*2^(s+1)*m-1)%2=1 := by
  have hp : 0 < 5^j*2^(s+1)*m := by
    have ha : 0 < 5^j := Nat.pow_pos (n:=j) (by omega :0<5)
    have hb : 0 < 2^(s+1) := Nat.pow_pos (n:=s+1) (by omega :0<2)
    exact Nat.mul_pos (Nat.mul_pos ha hb) hm
  have heven : (5^j*2^(s+1)*m)%2=0 := by
    rw [show 2^(s+1)=2*2^s by simp [Nat.pow_succ']]
    rw [show 5^j*(2*2^s)*m=2*(5^j*2^s*m) by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]]
    omega
  omega

end BB6.Agent48.SpaceNeedle
#print axioms BB6.Agent48.SpaceNeedle.odd_step
#print axioms BB6.Agent48.SpaceNeedle.odd_block
#print axioms BB6.Agent48.SpaceNeedle.odd_block_prefix
#print axioms BB6.Agent48.SpaceNeedle.odd_block_exits_even
#print axioms BB6.Agent48.SpaceNeedle.odd_block_prefix_odd
