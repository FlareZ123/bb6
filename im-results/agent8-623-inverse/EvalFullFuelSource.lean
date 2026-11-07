import Agent8DrainLogDepthSource

/-!
Source-certified complete finite recursion realization of the exact
#623 evaluator and B-drain. Unlike source `evalA`, the new interpreter's
recursive fuel does not depend on potentially huge first counter a.

For every k and every (a,b,d) with b<3^k, the fully bounded
`drainBFullyFuel (k+1)` agrees exactly with unmodified `drainB`
including failure. The finite fuel bound grows with the ternary
digit length of b, so the recursive interpreter uses at most
O((log(b+1))^2) calls in both nested phases. This asymptotic
description is explanatory and is not a separate formal time theorem.

This is an all-input computation theorem, not a blank-root decision.
-/

namespace BB6.Agent8EvalFullFuelSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- Fuel the A evaluator by ternary input digit depth. -/
def evalAfuel : Nat → Nat → Nat → Nat → Option (Nat × Nat × Nat)
  | 0, _, _, _ => none
  | fuel+1, a, k, m =>
    if k % 3=2 then some (a+1,k/3,m)
    else if a=0 then (if k%3=0 then none else some (0,k/3,m))
    else if k%3=0 then some (a-1,k/3,m+2)
    else evalAfuel fuel (a-1) (k/3) (m+2*(k/3)+3)

/-- Full original source evaluator agrees with the digit-length
fuelled counterpart for every first and third counter. -/
theorem evalA_fuel_log_bound (n : Nat) :
    ∀ a k m : Nat, k < 3^n →
      evalAfuel (n+1) a k m = evalA a k m := by
  induction n with
  | zero =>
    intro a k m hk
    have hkzero : k=0 := by simpa using hk
    subst k
    cases a with
    | zero => simp [evalAfuel,evalA]
    | succ a => simp [evalAfuel,evalA]
  | succ n ih =>
    intro a k m hk
    by_cases h2 : k%3=2
    · simp [evalAfuel,evalA,h2]
    · by_cases ha : a=0
      · subst a
        by_cases h0 : k%3=0
        · simp [evalAfuel,evalA,h2,h0]
        · simp [evalAfuel,evalA,h2,h0]
      · by_cases h0 : k%3=0
        · simp [evalAfuel,evalA,h2,ha,h0]
        · have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
          have hsmall : k/3 < 3^n := by omega
          have hsrc : evalA a k m =
              evalA (a-1) (k/3) (m+2*(k/3)+3) := by
            rw [evalA]
            simp [h2,ha,h0]
          have hfuel : evalAfuel (n+1+1) a k m =
              evalAfuel (n+1) (a-1) (k/3) (m+2*(k/3)+3) := by
            rw [evalAfuel]
            simp [h2,ha,h0]
          rw [hfuel,hsrc]
          exact ih (a-1) (k/3) (m+2*(k/3)+3) hsmall

/-- The whole recursive B-drain with both recursive functions fuelled
by ternary input length, and a single decreasing fuel argument. -/
def drainBFullyFuel : Nat → Nat → Nat → Nat → Option HighLevelState
  | 0, _, _, _ => none
  | f+1,a,b,d =>
    if b=0 then some (.D a d)
    else (evalAfuel (f+1) a (b-1) (d+2*b+3)).bind fun p =>
      if p.2.1 < b then drainBFullyFuel f p.1 p.2.1 p.2.2 else none

/-- The *fully* fuelled interpreter is extensionally identical to
the real unmodified source B-drain whenever b<3^k. Both successful
results and genuine source failure states are preserved. -/
theorem drainB_fully_fuel_log_bound (k : Nat) :
    ∀ a b d : Nat, b<3^k →
      drainBFullyFuel (k+1) a b d = drainB a b d := by
  induction k with
  | zero =>
    intro a b d hb
    have hzero : b=0 := by simpa using hb
    subst b
    simp [drainBFullyFuel,drainB]
  | succ k ih =>
    intro a b d hb
    by_cases hb0 : b=0
    · subst b
      simp [drainBFullyFuel,drainB]
    · rw [drainBFullyFuel,drainB]
      simp only [if_neg hb0]
      have hbelow : b-1 < 3^(k+1) := by omega
      rw [evalA_fuel_log_bound (k+1) a (b-1) (d+2*b+3) hbelow]
      cases he : evalA a (b-1) (d+2*b+3) with
      | none => simp [he]
      | some p =>
        rcases p with ⟨aa,bb,dd⟩
        simp only [he,Option.bind_some]
        have hbound := BB6.Agent8DrainLogDepthSource.evalA_second_le_quotient
          a (b-1) (d+2*b+3) aa bb dd he
        have hpow : 3^(k+1)=3*3^k := by rw [Nat.pow_succ]; omega
        have hsmall : bb < 3^k := by omega
        have hlt : bb < b := by omega
        simp only [if_pos hlt]
        exact ih aa bb dd hsmall

#print axioms evalA_fuel_log_bound
#print axioms drainB_fully_fuel_log_bound
end BB6.Agent8EvalFullFuelSource
