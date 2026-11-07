import HighAllDepth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- An explicit infinite sequence of authentic high stopping indices. -/
def exceptionalIndex (r : Nat) : Nat := 3*2^r-1

private theorem exponential_width (r : Nat) : r+4 ≤ 6*2^r := by
  induction r with
  | zero => decide
  | succ r ih =>
      rw [Nat.pow_succ]
      omega

private theorem exceptionalIndex_plus (r : Nat) :
    exceptionalIndex r+1=3*2^r := by
  dsimp [exceptionalIndex]
  have hp : 1 ≤ (2:Nat)^r := Nat.pow_pos (by decide)
  omega

/-- Every r >= 8 divisible by eight gives a new forbidden authentic high
    stopping index m = 3*2^r-1. The exact stopping equation is preserved,
    and all-time blank nonreachability follows without time cutoffs. -/
theorem explicit_high_unreachable (r k : Nat)
    (hr : 8≤r) (hr0 : r%8=0)
    (hstop : k+3*(exceptionalIndex r)+5 =
      2^(2*exceptionalIndex r+2)*3) :
    ¬ BB6.Agent3.CReach 3 k := by
  let Q := 2^r
  let m := exceptionalIndex r
  have hq : 1 ≤ Q := Nat.pow_pos (by decide)
  have hmp : m+1=3*Q := exceptionalIndex_plus r
  have hwidth : r+4 ≤ 2*m+2 := by
    have hb := exponential_width r
    omega
  have hP : 3*m+3=9*Q := by omega
  have hmod : (3*m+3)%2^(r+4)=9*Q := by
    rw [hP]
    have hpow : 2^(r+4)=Q*16 := by
      dsimp [Q]
      rw [Nat.pow_add]
    rw [hpow]
    apply Nat.mod_eq_of_lt
    omega
  have ht := high_all_depth_eight_no_blank r 0 m k
    hr hr0 hwidth (by decide) (by simpa using hmod)
    (by simpa [m] using hstop)
  simpa only [Nat.zero_mul, Nat.zero_add, Nat.reduceAdd] using ht

/-- Distinct parameters of the infinite forbidden family are strictly
    increasing. -/
theorem exceptionalIndex_strict (r : Nat) :
    exceptionalIndex r < exceptionalIndex (r+1) := by
  have hp : 0 < (2:Nat)^r := Nat.pow_pos (by decide)
  have hpplus : 2^(r+1)=2^r*2 := Nat.pow_succ 2 r
  dsimp [exceptionalIndex]
  rw [hpplus]
  omega

#print axioms explicit_high_unreachable
#print axioms exceptionalIndex_strict
end BB6.Agent46
