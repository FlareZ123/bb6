import JointAllRoot
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Prior

/-- Exact arithmetic separation from the complete original Agent19
    high stopping-parameter sieve: every j = 10 modulo 32 at m=1
    passes all its filters, including its unbounded dyadic quantifier.
    This says the prior sieve admits the PARAMETER; it does not say
    that the true blank orbit reaches the corresponding stopping input. -/
theorem all_j_mod32_ten_prior_allowed (j : Nat) (hj32 : j%32=10) :
    BB6.Agent19Joint.highAllowed j 1 := by
  have hj16 : (j+6)%16=0 := by omega
  unfold BB6.Agent19Joint.highAllowed
    BB6.Agent3.jointHighRectAllowed BB6.Agent3.jointHighAllowed
  constructor
  · simp [hj32]
  constructor
  · intro n h
    have hn : n=0 := by omega
    subst n
    have hz : (j+6)%16=4 := by simpa using h.2.1
    omega
  · constructor
    · omega
    constructor
    · omega
    constructor <;> omega

#print axioms all_j_mod32_ten_prior_allowed
end BB6.Agent29Prior
