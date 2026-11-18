import TM63RootQ4Attainable
import CostRecurrence
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent42OuterLCInc

open BB6Coverage.Agent42RootAttainable
open BB6ChampionArithmetic

private theorem nextRight_pos_odd (b : Nat) (hb : 0 < b) :
    0 < nextRight b ∧ nextRight b % 2 = 1 := by
  have hpow : 2 ≤ 2^b := by
    cases b with
    | zero => omega
    | succ b =>
        have hp : 0 < 2^b := Nat.pow_pos (by decide)
        have hmul : 2 ≤ 2^b * 2 := by omega
        simpa [Nat.pow_succ] using hmul
  have hmod : 2^b % 2 = 0 := by
    cases b with
    | zero => omega
    | succ b => simp [Nat.pow_succ, Nat.mul_mod]
  constructor
  · unfold nextRight
    omega
  · unfold nextRight
    omega

/-- The seven-stage first-section exponent is odd, without evaluating the
tower-sized right counters. -/
theorem tm63FirstSection_exponent_odd :
    tm63FirstSection.exponent % 2 = 1 := by
  have hb1 := nextRight_pos_odd 63 (by omega)
  have hb2 := nextRight_pos_odd (nextRight 63) hb1.1
  have hb3 := nextRight_pos_odd (nextRight (nextRight 63)) hb2.1
  have hb4 := nextRight_pos_odd (nextRight (nextRight (nextRight 63))) hb3.1
  have hb5 := nextRight_pos_odd
    (nextRight (nextRight (nextRight (nextRight 63)))) hb4.1
  have hb6 := nextRight_pos_odd
    (nextRight (nextRight (nextRight (nextRight (nextRight 63))))) hb5.1
  simp [tm63FirstSection, sectionResult, nextMarker, nextExponent]
  omega

/-- The middle-34 terminal marker-1 length is even. -/
theorem tm63Length1_even : tm63Length1 % 2 = 0 := by
  rw [tm63Length1]
  have h := tm63FirstSection_exponent_odd
  omega

end BB6Coverage.Agent42OuterLCInc
