import Agent8ThirdCounterAffineSource

/-!
An unbounded, original-source exact logarithmic recursion bound on the
#623 ternary B-drain.  Every complete evaluator call contracts its
secondary counter by at least a factor of three (up to a constant).
Therefore a drain with input b<3^k is exactly evaluated by k+1
recursive B-drain calls, for arbitrary first and third counters.

This is a structural result for the unmodified original-source
function `drainB` and does not classify the genuine blank-root orbit.
-/

namespace BB6.Agent8DrainLogDepthSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- The evaluator's secondary coordinate never exceeds floor(k/3),
including the arbitrarily long ternary-one recursive branch. -/
theorem evalA_second_le_quotient (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa,bb,dd) →
      bb ≤ k / 3 := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
      · simp [h2,h0] at h
        cases h
        omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
        cases h
        omega
      · simp [h2,h0] at h
        have hi := ih (k/3) (m+2*(k/3)+3) aa bb dd h
        have hquot : k/3/3 ≤ k/3 := Nat.div_le_self _ _
        omega

/-- Resource-bounded exact interpreter.  Source `evalA` is unchanged.
This function limits only the number of *B-drain* recursion rounds. -/
def drainBfuel : Nat → Nat → Nat → Nat → Option HighLevelState
  | 0, _, _, _ => none
  | fuel+1, a, b, d =>
      if b=0 then some (.D a d)
      else (evalA a (b-1) (d+2*b+3)).bind fun p =>
        if p.2.1 < b then drainBfuel fuel p.1 p.2.1 p.2.2 else none

/-- Exact all-input recursion depth certificate, with no finite
input bound: if b<3^k, the fuelled and original full B-drain agree. -/
theorem drainB_fuel_log_bound (k : Nat) :
    ∀ a b d : Nat, b < 3^k →
      drainBfuel (k+1) a b d = drainB a b d := by
  induction k with
  | zero =>
    intro a b d hb
    have hbzero : b=0 := by simpa using hb
    subst b
    simp [drainBfuel,drainB]
  | succ k ih =>
    intro a b d hb
    by_cases hbzero : b=0
    · subst b
      simp [drainBfuel,drainB]
    · rw [drainBfuel,drainB]
      simp only [if_neg hbzero]
      cases he : evalA a (b-1) (d+2*b+3) with
      | none => simp [he]
      | some p =>
        rcases p with ⟨aa,bb,dd⟩
        simp only [he,Option.bind_some]
        have hbound := evalA_second_le_quotient a (b-1) (d+2*b+3) aa bb dd he
        have hpow : 3^(k+1) = 3*3^k := by
          rw [Nat.pow_succ]
          omega
        have hsmall : bb < 3^k := by omega
        have hlt : bb < b := by omega
        simp only [if_pos hlt]
        exact ih aa bb dd hsmall

#print axioms evalA_second_le_quotient
#print axioms drainB_fuel_log_bound
end BB6.Agent8DrainLogDepthSource
