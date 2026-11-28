import Lean.Elab.Tactic.Omega

namespace BB6.Agent1Raw56.LE17557RightLevel

/-- Three one-runs and the two internal zero-runs at an epoch checkpoint. -/
structure Right3 where
  a1 : Nat
  z1 : Nat
  a2 : Nat
  z2 : Nat
  a3 : Nat
  deriving DecidableEq, Repr

/-- Fixed right-side level map observed in the triad relation for m=3:
    first one-run 2a+2, first/second zeros 2z-1, middle one-run 2a+3,
    and final one-run 2a+1. -/
def level (x : Right3) : Right3 :=
  ⟨2*x.a1+2, 2*x.z1-1, 2*x.a2+3, 2*x.z2-1, 2*x.a3+1⟩

/-- Checkpoint right shape parameterized by q=2^n. -/
def checkpointQ (q : Nat) : Right3 :=
  ⟨q-2, 1, 2*q-3, 1, 2*q-1⟩

/-- The fixed right-side level map exactly doubles the checkpoint parameter. -/
theorem level_checkpointQ (q : Nat) (hq : 4 ≤ q) :
    level (checkpointQ q) = checkpointQ (2*q) := by
  simp [level, checkpointQ]
  omega

def checkpointRight (n : Nat) : Right3 := checkpointQ (2^n)

/-- Hence the right-side component alone maps C_n to the C_(n+1) right
    run-length vector for every actual epoch n>=2. -/
theorem level_checkpointRight (n : Nat) (hn : 2 ≤ n) :
    level (checkpointRight n) = checkpointRight (n+1) := by
  have hpow : 4 ≤ 2^n := by
    have hp : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
    simpa using hp
  simpa [checkpointRight, Nat.pow_succ, Nat.mul_comm] using
    level_checkpointQ (2^n) hpow

#print axioms level_checkpointQ
#print axioms level_checkpointRight

end BB6.Agent1Raw56.LE17557RightLevel
