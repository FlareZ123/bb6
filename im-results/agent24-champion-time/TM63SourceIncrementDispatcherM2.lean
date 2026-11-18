import TM63SourceIncrementDispatcher
import M2EvenResidueZeroCounted

namespace BB6Coverage.Agent24ChampionTime

open BB6Coverage.Agent44SectionResultRunSource
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6ChampionArithmetic
open BB6Coverage.Agent24M2EvenCounted

/-- Discharge the marker-2 residue-zero hypothesis of the 24-class
source dispatcher using the all-q M2 counted-source draft.  The only
remaining source-family hypothesis is marker 0 at n=8*q. -/
theorem tm63_source_increment_dispatch_m2
    (L : Nat) (hL : 4 ≤ L)
    (hm0zero : ∀ (q aa bb : Nat) (hh : Int),
      0 < q → 4 ≤ L → 8*q < 2^L → 0 < aa →
      run tm2 (proposedIncrementCost 0 (8*q) aa bb)
        (s1Config L (8*q) 0 aa 0 bb hh) =
      some (s1Config L (8*q-1) 2 (aa+bb+1) 0 (2^bb-1)
        (hh+5+3*bb))) :
    ∀ (k mm aa bb : Nat) (hh : Int),
      0 < k → k < 2^L → 0 < aa →
      run tm2 (proposedIncrementCost (mm%3) k aa bb)
        (s1Config L k (mm%3) aa 0 bb hh) =
      some (s1Config L (k-1) (nextMarker mm)
        (nextExponent mm aa bb) 0 (nextRight bb) (hh+5+3*bb)) := by
  apply tm63_source_increment_dispatch L hL hm0zero
  intro q aa bb hh hq hLq hbound haa
  exact m2Even_residue0_counted_increment_source
    L q aa bb hh hLq hq hbound haa

/-- Conditional full section countdown with only the marker-0
residue-zero all-q source family still assumed. -/
theorem sectionResult_run_of_m0_zero_source
    (L n m a b : Nat) (head : Int)
    (hL : 4 ≤ L) (hbound : n < 2^L) (ha : 0 < a)
    (hm0zero : ∀ (q aa bb : Nat) (hh : Int),
      0 < q → 4 ≤ L → 8*q < 2^L → 0 < aa →
      run tm2 (proposedIncrementCost 0 (8*q) aa bb)
        (s1Config L (8*q) 0 aa 0 bb hh) =
      some (s1Config L (8*q-1) 2 (aa+bb+1) 0 (2^bb-1)
        (hh+5+3*bb))) :
    run tm2 (sectionResult n m a b).cost
      (s1Config L n (m%3) a 0 b head) =
    some (s1Config L 0
      (sectionResult n m a b).marker
      (sectionResult n m a b).exponent 0
      (sectionResult n m a b).right
      (sectionHeadAfter n b head)) := by
  apply sectionResult_run_of_source_macro L n m a b head hbound ha
  exact tm63_source_increment_dispatch_m2 L hL hm0zero

#print axioms tm63_source_increment_dispatch_m2
#print axioms sectionResult_run_of_m0_zero_source

end BB6Coverage.Agent24ChampionTime
