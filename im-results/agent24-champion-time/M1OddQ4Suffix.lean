import Q4RightEndpoint
import M1OddQ4Prefix
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Source composition of the m=1,n=3 odd q4 branch

This module composes the new 29-step finite bridge and its counted sweep
with the generic q4 suffix endpoint.  It proves the full reset-prefix
source run and then attaches the all-ones counted drain.  The prefix
module and this composition remain intermediate until compiled and
axiom-audited in CI.
-/

namespace BB6Coverage.Agent24M1OddSuffix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent24M1OddQ4Prefix
open BB6ChampionArithmetic

/-- The 29-step m=1,n=3 prefix ends four E-on-one moves into the
ordinary q4 suffix.  Splitting the generic 39+3b suffix at those four
moves leaves 35+3b transitions from the prefix endpoint. -/
theorem m1Odd_q4_reset_prefix_source (a b : Nat) (h : Int) :
    run tm2 (resetPrefixCost 1 3 a b)
      (s1Config 3 3 1 a 0 b h) =
      some (s1Config 3 2 0 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  let T := m1OddQ4CutTape a b h
  have hshape : q4RightShape T h b :=
    m1Odd_q4_prefix_rightShape a b h
  have hleft := m1Odd_q4_prefix_leftFacing a b h
  have htail : ∀ i, 9+3*b ≤ i → T (h+1+(i:Int)) = false := by
    simpa [T] using m1Odd_q4_prefix_far_tail a b h
  have happend := m1OddQ4SuffixTargetLeft a b
  have hq4 :=
    q4_suffix_run_to_s1Config T h b 3 2 0 (a+b+2) (2^b-1)
      (m1OddQ4LeftFacing a) hshape htail hleft happend
  have hfirst : run tm2 4 ⟨4,h,T⟩ = some ⟨4,h+4,T⟩ := by
    have hlinear : linearRightOnes T h 4 := by
      intro i hi
      exact hshape.1 i (by omega)
    exact E_scan T h 4 hlinear
  have hsplit : 39+3*b = 4+(35+3*b) := by omega
  rw [hsplit,run_append,hfirst] at hq4
  simp only [Option.bind_some] at hq4
  have hprefix := m1Odd_q4_prefix_run a b h
  have hnum : resetPrefixCost 1 3 a b =
      (32+12*a)+(35+3*b) := by
    rw [m1Odd_resetPrefixCost_eq]
    omega
  rw [hnum,run_append,hprefix]
  simp only [Option.bind_some]
  exact hq4

/-- Complete source-level counted increment for the odd m=1,n=3 reset.
The drain changes the active binary counter 2^b-1 into the right unary
counter without changing the marker, exponent, or head. -/
theorem m1Odd_q4_counted_increment_source
    (a b : Nat) (h : Int) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 1 3 a b)
      (s1Config 3 3 1 a 0 b h) =
      some (s1Config 3 2 0 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m1Odd_q4_reset_prefix_source a b h
  have hbound := resetDrainBound a b 1 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    3 2 0 (a+b+2) b (h+5+3*b)
    (s1Config 3 3 1 a 0 b h) (resetPrefixCost 1 3 a b)
    hp (by simpa [resetDelta] using hbound)
  simpa [proposedIncrementCost_decomp] using hrun

/-- Keep the successor exponent/counter symbolic for root composition.
The explicit power is exposed only by the generic rewrite lemmas, so
instantiating this theorem at a huge root counter does not normalize it. -/
private theorem m1OddNextExponent_one_eq (a b : Nat) :
    nextExponent 1 a b = a+b+2 := by
  rfl

private theorem m1OddNextRight_eq (b : Nat) :
    nextRight b = 2^b-1 := by
  rfl

theorem m1Odd_q4_counted_increment_source_symbolic
    (a b : Nat) (h : Int) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 1 3 a b)
      (s1Config 3 3 1 a 0 b h) =
      some (s1Config 3 2 0 (nextExponent 1 a b) 0
        (nextRight b) (h+5+3*b)) := by
  simpa only [m1OddNextExponent_one_eq,m1OddNextRight_eq] using
    m1Odd_q4_counted_increment_source a b h ha

#print axioms m1Odd_q4_reset_prefix_source
#print axioms m1Odd_q4_counted_increment_source
#print axioms m1Odd_q4_counted_increment_source_symbolic

end BB6Coverage.Agent24M1OddSuffix
