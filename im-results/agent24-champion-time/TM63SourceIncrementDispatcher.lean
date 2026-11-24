import SectionResultRunSource
import M0OddGenericSource
import M1EvenValuationSource
import M0EvenResidueTwo
import M0EvenResidueFour
import M0EvenSixGenericSource
import M2OddGenericStage
import M2EvenResidueTwoCounted
import M2EvenResidueFour
import M2EvenSixGenericCounted
import Lean.Elab.Tactic.Omega

/-!
# Total one-step source dispatcher for the TM63 section countdown

All 24 (index mod 8, marker mod 3) branches are discharged by existing
counted source theorems except the two all-q residue-zero families.  Those
two families are explicit hypotheses here, so this theorem isolates the
exact remaining source obligations needed by SectionResultRunSource.
-/

namespace BB6Coverage.Agent24ChampionTime

open BB6Coverage.Agent44SectionResultRunSource
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48M0OddGenericSource
open BB6Coverage.Agent48M1EvenValuationCountedSource
open BB6Coverage.Agent24M0EvenResidueTwo
open BB6Coverage.Agent48M0EvenResidueFour
open BB6Coverage.Agent42M0EvenSixGenericSource
open BB6Coverage.Agent42M2OddGeneric
open BB6Coverage.Agent42M2EvenResidueTwoCounted
open BB6Coverage.Agent48M2EvenResidueFour
open BB6Coverage.Agent44M2EvenSixGenericCounted
open BB6ChampionArithmetic

/-- If the two residue-zero all-q source families are supplied, all 24
one-step classes dispatch to the original TM2 counted-increment source. -/
theorem tm63_source_increment_dispatch_ge3
    (L : Nat) (hL : 3 ≤ L)
    (hm0zero : ∀ (q aa bb : Nat) (hh : Int),
      0 < q → 4 ≤ L → 8*q < 2^L → 0 < aa →
      run tm2 (proposedIncrementCost 0 (8*q) aa bb)
        (s1Config L (8*q) 0 aa 0 bb hh) =
      some (s1Config L (8*q-1) 2 (aa+bb+1) 0 (2^bb-1)
        (hh+5+3*bb)))
    (hm2zero : ∀ (q aa bb : Nat) (hh : Int),
      0 < q → 4 ≤ L → 8*q < 2^L → 0 < aa →
      run tm2 (proposedIncrementCost 2 (8*q) aa bb)
        (s1Config L (8*q) 2 aa 0 bb hh) =
      some (s1Config L (8*q-1) 1 (aa+bb+2) 0 (2^bb-1)
        (hh+5+3*bb))) :
    ∀ (k mm aa bb : Nat) (hh : Int),
      0 < k → k < 2^L → 0 < aa →
      run tm2 (proposedIncrementCost (mm%3) k aa bb)
        (s1Config L k (mm%3) aa 0 bb hh) =
      some (s1Config L (k-1) (nextMarker mm)
        (nextExponent mm aa bb) 0 (nextRight bb) (hh+5+3*bb)) := by
  intro k mm aa bb hh hk hbound haa
  have hL3 : 3 ≤ L := by omega
  have hLpos : 0 < L := by omega
  have hdecomp : k = 8*(k/8) + k%8 := by omega
  have hres :
      k%8=0 ∨ k%8=1 ∨ k%8=2 ∨ k%8=3 ∨
      k%8=4 ∨ k%8=5 ∨ k%8=6 ∨ k%8=7 := by omega
  have hmarker : mm%3=0 ∨ mm%3=1 ∨ mm%3=2 := by omega
  rcases hmarker with hm0 | hm1 | hm2
  · rcases hres with hr0 | hr1 | hr2 | hr3 | hr4 | hr5 | hr6 | hr7
    · have hq : 0 < k/8 := by omega
      have hboundq : 8*(k/8) < 2^L := by omega
      have hL4 : 4 ≤ L := by
        by_cases h4 : 4 ≤ L
        · exact h4
        · have heq : L = 3 := by omega
          rw [heq] at hboundq
          omega
      have hsrc := hm0zero (k/8) aa bb hh hq hL4 hboundq haa
      have heq : 8*(k/8) = k := by omega
      rw [← heq]
      simpa [hm0, nextMarker, show (mm+2)%3 = 2 by omega, nextExponent, nextRight] using hsrc
    · have hsrc := m0Odd_counted_increment_source
        L k aa bb hh hLpos (by omega) hbound haa
      simpa [hm0, nextMarker, show (mm+2)%3 = 2 by omega, nextExponent, nextRight] using hsrc
    · have hboundr : 8*(k/8)+2 < 2^L := by omega
      have hsrc := m0Even_residue2_counted_increment_source
        L (k/8) aa bb hh hL3 hboundr haa
      have heq : 8*(k/8)+2 = k := by omega
      rw [← heq]
      simpa [hm0, nextMarker, show (mm+2)%3 = 2 by omega, nextExponent, nextRight] using hsrc
    · have hsrc := m0Odd_counted_increment_source
        L k aa bb hh hLpos (by omega) hbound haa
      simpa [hm0, nextMarker, show (mm+2)%3 = 2 by omega, nextExponent, nextRight] using hsrc
    · have hboundr : 8*(k/8)+4 < 2^L := by omega
      have hsrc := m0Even_residue4_counted_increment_source
        L (k/8) aa bb hh hL3 hboundr haa
      have heq : 8*(k/8)+4 = k := by omega
      rw [← heq]
      simpa [hm0, nextMarker, show (mm+2)%3 = 2 by omega, nextExponent, nextRight] using hsrc
    · have hsrc := m0Odd_counted_increment_source
        L k aa bb hh hLpos (by omega) hbound haa
      simpa [hm0, nextMarker, show (mm+2)%3 = 2 by omega, nextExponent, nextRight] using hsrc
    · have hboundr : 8*(k/8)+6 < 2^L := by omega
      have hsrc := m0EvenSix_counted_increment_source
        L (k/8) aa bb hh hL3 hboundr haa
      have heq : 8*(k/8)+6 = k := by omega
      rw [← heq]
      simpa [hm0, nextMarker, show (mm+2)%3 = 2 by omega, nextExponent, nextRight] using hsrc
    · have hsrc := m0Odd_counted_increment_source
        L k aa bb hh hLpos (by omega) hbound haa
      simpa [hm0, nextMarker, show (mm+2)%3 = 2 by omega, nextExponent, nextRight] using hsrc
  · have hsrc := m1EvenValuation_counted_increment_source
      L k aa bb hh hk hbound haa
    simpa [hm1, nextMarker, show (mm+2)%3 = 0 by omega, nextExponent, nextRight] using hsrc
  · rcases hres with hr0 | hr1 | hr2 | hr3 | hr4 | hr5 | hr6 | hr7
    · have hq : 0 < k/8 := by omega
      have hboundq : 8*(k/8) < 2^L := by omega
      have hL4 : 4 ≤ L := by
        by_cases h4 : 4 ≤ L
        · exact h4
        · have heq : L = 3 := by omega
          rw [heq] at hboundq
          omega
      have hsrc := hm2zero (k/8) aa bb hh hq hL4 hboundq haa
      have heq : 8*(k/8) = k := by omega
      rw [← heq]
      simpa [hm2, nextMarker, show (mm+2)%3 = 1 by omega, nextExponent, nextRight] using hsrc
    · have hsrc := m2Odd_counted_increment_source
        L k aa bb hh (by omega) hbound
      simpa [hm2, nextMarker, show (mm+2)%3 = 1 by omega, nextExponent, nextRight] using hsrc
    · have hboundr : 8*(k/8)+2 < 2^L := by omega
      have hsrc := m2Even_residue2_counted_increment_source
        L (k/8) aa bb hh hL3 hboundr haa
      have heq : 8*(k/8)+2 = k := by omega
      rw [← heq]
      simpa [hm2, nextMarker, show (mm+2)%3 = 1 by omega, nextExponent, nextRight] using hsrc
    · have hsrc := m2Odd_counted_increment_source
        L k aa bb hh (by omega) hbound
      simpa [hm2, nextMarker, show (mm+2)%3 = 1 by omega, nextExponent, nextRight] using hsrc
    · have hboundr : 8*(k/8)+4 < 2^L := by omega
      have hsrc := m2Even_residue4_counted_increment_source
        L (k/8) aa bb hh hL3 hboundr haa
      have heq : 8*(k/8)+4 = k := by omega
      rw [← heq]
      simpa [hm2, nextMarker, show (mm+2)%3 = 1 by omega, nextExponent, nextRight] using hsrc
    · have hsrc := m2Odd_counted_increment_source
        L k aa bb hh (by omega) hbound
      simpa [hm2, nextMarker, show (mm+2)%3 = 1 by omega, nextExponent, nextRight] using hsrc
    · have hboundr : 8*(k/8)+6 < 2^L := by omega
      have hsrc := m2EvenSix_generic_counted_increment_source
        L (k/8) aa bb hh hL3 hboundr haa
      have heq : 8*(k/8)+6 = k := by omega
      rw [← heq]
      simpa [hm2, nextMarker, show (mm+2)%3 = 1 by omega, nextExponent, nextRight] using hsrc
    · have hsrc := m2Odd_counted_increment_source
        L k aa bb hh (by omega) hbound
      simpa [hm2, nextMarker, show (mm+2)%3 = 1 by omega, nextExponent, nextRight] using hsrc

theorem tm63_source_increment_dispatch
    (L : Nat) (hL : 4 ≤ L)
    (hm0zero : ∀ (q aa bb : Nat) (hh : Int),
      0 < q → 4 ≤ L → 8*q < 2^L → 0 < aa →
      run tm2 (proposedIncrementCost 0 (8*q) aa bb)
        (s1Config L (8*q) 0 aa 0 bb hh) =
      some (s1Config L (8*q-1) 2 (aa+bb+1) 0 (2^bb-1)
        (hh+5+3*bb)))
    (hm2zero : ∀ (q aa bb : Nat) (hh : Int),
      0 < q → 4 ≤ L → 8*q < 2^L → 0 < aa →
      run tm2 (proposedIncrementCost 2 (8*q) aa bb)
        (s1Config L (8*q) 2 aa 0 bb hh) =
      some (s1Config L (8*q-1) 1 (aa+bb+2) 0 (2^bb-1)
        (hh+5+3*bb))) :
    ∀ (k mm aa bb : Nat) (hh : Int),
      0 < k → k < 2^L → 0 < aa →
      run tm2 (proposedIncrementCost (mm%3) k aa bb)
        (s1Config L k (mm%3) aa 0 bb hh) =
      some (s1Config L (k-1) (nextMarker mm)
        (nextExponent mm aa bb) 0 (nextRight bb) (hh+5+3*bb)) :=
  tm63_source_increment_dispatch_ge3 L (by omega) hm0zero hm2zero

/-- Conditional full section countdown: the two all-q residue-zero source
families are the only hypotheses beyond the 22 existing source families. -/
theorem sectionResult_run_of_two_zero_sources
    (L n m a b : Nat) (head : Int)
    (hL : 4 ≤ L) (hbound : n < 2^L) (ha : 0 < a)
    (hm0zero : ∀ (q aa bb : Nat) (hh : Int),
      0 < q → 4 ≤ L → 8*q < 2^L → 0 < aa →
      run tm2 (proposedIncrementCost 0 (8*q) aa bb)
        (s1Config L (8*q) 0 aa 0 bb hh) =
      some (s1Config L (8*q-1) 2 (aa+bb+1) 0 (2^bb-1)
        (hh+5+3*bb)))
    (hm2zero : ∀ (q aa bb : Nat) (hh : Int),
      0 < q → 4 ≤ L → 8*q < 2^L → 0 < aa →
      run tm2 (proposedIncrementCost 2 (8*q) aa bb)
        (s1Config L (8*q) 2 aa 0 bb hh) =
      some (s1Config L (8*q-1) 1 (aa+bb+2) 0 (2^bb-1)
        (hh+5+3*bb))) :
    run tm2 (sectionResult n m a b).cost
      (s1Config L n (m%3) a 0 b head) =
    some (s1Config L 0
      (sectionResult n m a b).marker
      (sectionResult n m a b).exponent 0
      (sectionResult n m a b).right
      (sectionHeadAfter n b head)) := by
  apply sectionResult_run_of_source_macro L n m a b head hbound ha
  exact tm63_source_increment_dispatch_ge3 L (by omega) hm0zero hm2zero

#print axioms tm63_source_increment_dispatch_ge3
#print axioms sectionResult_run_of_two_zero_sources

end BB6Coverage.Agent24ChampionTime
