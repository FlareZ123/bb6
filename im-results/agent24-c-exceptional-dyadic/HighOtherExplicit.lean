import HighOtherBranch
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- An explicit recurrence indexing indefinitely deep Branch B stopping
    targets with fixed left stopping parameter j=28. -/
def exceptionalIndexB : Nat → Nat
  | 0 => 1099
  | n+1 => 256*exceptionalIndexB n+2635

theorem exceptionalIndexB_power (n : Nat) :
    3*exceptionalIndexB n+31=13*2^(8*(n+1)) := by
  induction n with
  | zero => decide
  | succ n ih =>
      change 3*(256*exceptionalIndexB n+2635)+31=
        13*2^(8*((n+1)+1))
      have he : 8*((n+1)+1)=8*(n+1)+8 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^8=256 by decide]
      omega

theorem exceptionalIndexB_width (n : Nat) :
    8*(n+1)+4 ≤ 2*exceptionalIndexB n+2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      change 8*((n+1)+1)+4 ≤ 2*(256*exceptionalIndexB n+2635)+2
      omega

theorem exceptionalIndexB_strict (n : Nat) :
    exceptionalIndexB n < exceptionalIndexB (n+1) := by
  change exceptionalIndexB n < 256*exceptionalIndexB n+2635
  omega

/-- The entire second explicit index tower is genuinely blank-unreachable
    whenever the exact, original high stopping equation holds. -/
theorem explicit_high_other_unreachable (n k : Nat)
    (hstop : k+28+3*exceptionalIndexB n+5=
      2^(2*exceptionalIndexB n+2)*(28+3)) :
    ¬ BB6.Agent3.CReach 59 k := by
  let r := 8*(n+1)
  let m := exceptionalIndexB n
  have hr : 8≤r := by dsimp [r]; omega
  have hrmod : r%8=0 := by dsimp [r]; omega
  have hwidth : r+4≤2*m+2 := exceptionalIndexB_width n
  have hpow : 28+3*m+3=13*2^r := by
    dsimp [m,r]
    have h:=exceptionalIndexB_power n
    omega
  have hparam : (28+3*m+3)%2^(r+4)=13*2^r := by
    rw [hpow]
    have hbase : 0<(2:Nat)^r := Nat.pow_pos (by decide)
    have he : 2^(r+4)=16*2^r := by
      rw [Nat.pow_add]
      omega
    rw [he]
    apply Nat.mod_eq_of_lt
    omega
  have h := high_all_depth_other_no_blank r 28 m k
    hr hrmod hwidth (by decide) hparam (by simpa [m] using hstop)
  simpa using h

#print axioms exceptionalIndexB_power
#print axioms exceptionalIndexB_strict
#print axioms explicit_high_other_unreachable
end BB6.Agent46
