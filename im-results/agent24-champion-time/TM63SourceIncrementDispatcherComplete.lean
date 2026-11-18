import TM63SourceIncrementDispatcherM2
import M0EvenEightValuationCountedSource

/-!
# Complete source-level TM63 section countdown

This module supplies the remaining marker-0 all-q residue-zero source
family to the existing dispatcher, which already supplies marker 2.
Together with the other 22 source families, this yields a fully quantified
original-TM2 run for the complete SectionResult countdown.

This is a source-level composition only until the exact import closure and
transitive axiom profiles are compiled and checked.
-/

namespace BB6Coverage.Agent24ChampionTime

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent44SectionResultRunSource
open BB6Coverage.Agent8S1Encoder
open BB6ChampionArithmetic
open BB6Coverage.Agent48M0EvenEightValuationCountedSource

/-- Every one-step residue/marker class is now discharged by a concrete
counted-source theorem, assuming the imported 22 rows and the M2 zero-row
closure are themselves accepted. -/
theorem tm63_source_increment_dispatch_complete
    (L : Nat) (hL : 4 ≤ L) :
    ∀ (k mm aa bb : Nat) (hh : Int),
      0 < k → k < 2^L → 0 < aa →
      run tm2 (proposedIncrementCost (mm%3) k aa bb)
        (s1Config L k (mm%3) aa 0 bb hh) =
      some (s1Config L (k-1) (nextMarker mm)
        (nextExponent mm aa bb) 0 (nextRight bb) (hh+5+3*bb)) := by
  apply tm63_source_increment_dispatch_m2 L hL
  intro q aa bb hh hq hLq hbound haa
  exact m0EvenEight_valuation_counted_increment_source
    L q aa bb hh hLq hq hbound haa

/-- The complete SectionResult stage is an original-TM2 run, conditional
only on acceptance of the exact source imports used by this dispatcher. -/
/-- Run every source increment except the final one, leaving the
counter at one for a terminal counted-reset prefix. -/
theorem sectionResult_run_to_index_one_of_source_macro
    (L k m a b : Nat) (head : Int)
    (hbound : k+1 < 2^L) (ha : 0 < a)
    (hmacro : ∀ (n mm aa bb : Nat) (hh : Int),
      0 < n → n < 2^L → 0 < aa →
      run tm2 (proposedIncrementCost (mm%3) n aa bb)
        (s1Config L n (mm%3) aa 0 bb hh) =
      some (s1Config L (n-1) (nextMarker mm)
        (nextExponent mm aa bb) 0 (nextRight bb) (hh+5+3*bb))) :
    run tm2 (sectionResult k m a b).cost
      (s1Config L (k+1) (m%3) a 0 b head) =
    some (s1Config L 1
      (sectionResult k m a b).marker
      (sectionResult k m a b).exponent 0
      (sectionResult k m a b).right
      (sectionHeadAfter k b head)) := by
  induction k generalizing m a b head with
  | zero =>
      simp [sectionResult, sectionHeadAfter]
  | succ k ih =>
      have hstep := hmacro (k+2) m a b head (by omega) (by omega) ha
      have hbound' : k+1 < 2^L := by omega
      have ha' : 0 < nextExponent m a b := by
        unfold nextExponent
        omega
      have hrest := ih (nextMarker m) (nextExponent m a b)
        (nextRight b) (head+5+3*b) hbound' ha'
      have hnorm : (nextMarker m)%3 = nextMarker m := by
        simp [nextMarker]
      have hrest' :
          run tm2
            (sectionResult k (nextMarker m) (nextExponent m a b)
              (nextRight b)).cost
            (s1Config L (k+1) (nextMarker m) (nextExponent m a b)
              0 (nextRight b) (head+5+3*b)) =
          some (s1Config L 1
            (sectionResult k (nextMarker m) (nextExponent m a b)
              (nextRight b)).marker
            (sectionResult k (nextMarker m) (nextExponent m a b)
              (nextRight b)).exponent
            0
            (sectionResult k (nextMarker m) (nextExponent m a b)
              (nextRight b)).right
            (sectionHeadAfter k (nextRight b) (head+5+3*b))) := by
        simpa [hnorm] using hrest
      have htotal := run_compose_local hstep hrest'
      simpa [sectionResult, sectionHeadAfter] using htotal

/-- The complete dispatcher proves the SectionResult countdown down to
index one, so the final reset prefix can be handled separately. -/
theorem sectionResult_run_to_index_one_complete
    (L k m a b : Nat) (head : Int)
    (hL : 4 ≤ L) (hbound : k+1 < 2^L) (ha : 0 < a) :
    run tm2 (sectionResult k m a b).cost
      (s1Config L (k+1) (m%3) a 0 b head) =
    some (s1Config L 1
      (sectionResult k m a b).marker
      (sectionResult k m a b).exponent 0
      (sectionResult k m a b).right
      (sectionHeadAfter k b head)) := by
  apply sectionResult_run_to_index_one_of_source_macro
    L k m a b head hbound ha
  intro n mm aa bb hh hn hbound' haa
  exact tm63_source_increment_dispatch_complete
    L hL n mm aa bb hh hn hbound' haa

theorem sectionResult_run_complete
    (L n m a b : Nat) (head : Int)
    (hL : 4 ≤ L) (hbound : n < 2^L) (ha : 0 < a) :
    run tm2 (sectionResult n m a b).cost
      (s1Config L n (m%3) a 0 b head) =
    some (s1Config L 0
      (sectionResult n m a b).marker
      (sectionResult n m a b).exponent 0
      (sectionResult n m a b).right
      (sectionHeadAfter n b head)) := by
  apply sectionResult_run_of_m0_zero_source
    L n m a b head hL hbound ha
  intro q aa bb hh hq hLq hboundq haa
  exact m0EvenEight_valuation_counted_increment_source
    L q aa bb hh hLq hq hboundq haa

#print axioms tm63_source_increment_dispatch_complete
#print axioms sectionResult_run_to_index_one_complete
#print axioms sectionResult_run_complete

end BB6Coverage.Agent24ChampionTime
