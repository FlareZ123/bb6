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
#print axioms sectionResult_run_complete

end BB6Coverage.Agent24ChampionTime
