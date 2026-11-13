import Q4RightEndpoint
import M0EvenQ4Prefix
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Source composition of the m=0,n=2 even q4 branch

The q4 prefix reaches state 4 at the original head, so the generic
39+3b suffix is applied directly.  The resulting reset-prefix endpoint
is then extended by the exact all-ones counted drain.
-/

namespace BB6Coverage.Agent24M0EvenSuffix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent24M0EvenQ4Prefix
open BB6ChampionArithmetic

/-- Complete source-level reset-prefix run for the m=0,n=2 even stage. -/
theorem m0Even_q4_reset_prefix_source
    (a b : Nat) (h : Int) (ha : 0 < a) :
    run tm2 (resetPrefixCost 0 2 a b)
      (s1Config 3 2 0 a 0 b h) =
      some (s1Config 3 1 2 (a+b+1) (2^b-1) 0
        (h+5+3*b)) := by
  let T := m0EvenQ4CutTape a b h
  have hshape : q4RightShape T h b :=
    m0Even_q4_prefix_rightShape a b h ha
  have hleft := m0Even_q4_prefix_leftFacing a b h ha
  have htail : ∀ i, 9+3*b ≤ i → T (h+1+(i:Int)) = false := by
    intro i hi
    exact hshape.2.2.2.2 i (by omega)
  have happend := m0EvenQ4SuffixTargetLeft a b ha
  have hq4 :=
    q4_suffix_run_to_s1Config T h b 3 1 2 (a+b+1) (2^b-1)
      (m0EvenQ4LeftFacing a) hshape htail hleft happend
  have hprefix := m0Even_q4_prefix_run a b h ha
  have hnum : resetPrefixCost 0 2 a b =
      (36+12*a)+(39+3*b) := by
    rw [m0Even_resetPrefixCost_eq]
    omega
  rw [hnum,run_append,hprefix]
  simp only [Option.bind_some]
  exact hq4

/-- Complete counted increment, including the exact drain of
the binary counter 2^b-1 into the right unary counter. -/
theorem m0Even_q4_counted_increment_source
    (a b : Nat) (h : Int) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 0 2 a b)
      (s1Config 3 2 0 a 0 b h) =
      some (s1Config 3 1 2 (a+b+1) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m0Even_q4_reset_prefix_source a b h ha
  have hbound := resetDrainBound a b 0 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    3 1 2 (a+b+1) b (h+5+3*b)
    (s1Config 3 2 0 a 0 b h) (resetPrefixCost 0 2 a b)
    hp (by simpa [resetDelta] using hbound)
  simpa [proposedIncrementCost_decomp] using hrun

private theorem m0EvenNextExponent_zero_eq (a b : Nat) :
    nextExponent 0 a b = a+b+1 := by
  rfl

private theorem m0EvenNextRight_eq (b : Nat) :
    nextRight b = 2^b-1 := by
  rfl

/-- Symbolic successor endpoint for composing at the large BB(6) root. -/
theorem m0Even_q4_counted_increment_source_symbolic
    (a b : Nat) (h : Int) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 0 2 a b)
      (s1Config 3 2 0 a 0 b h) =
      some (s1Config 3 1 2 (nextExponent 0 a b) 0
        (nextRight b) (h+5+3*b)) := by
  simpa only [m0EvenNextExponent_zero_eq,m0EvenNextRight_eq] using
    m0Even_q4_counted_increment_source a b h ha

#print axioms m0Even_q4_reset_prefix_source
#print axioms m0Even_q4_counted_increment_source
#print axioms m0Even_q4_counted_increment_source_symbolic

end BB6Coverage.Agent24M0EvenSuffix
