import M2OddGenericStage
import M1EvenResidueSix
import M0OddResidueFive
import M2EvenResidueFour
import CostRecurrence
import S1Encoder
import Lean.Elab.Tactic.Omega

/-!
# Four source-verified stages at the head of the TM63 middle section

For an outer index n = 8*k+7 and marker 2, the first four exact source
increments have residue/marker pairs (7,2), (6,1), (5,0), (4,2).
This module composes the already quantified original-TM2 theorems for
those four rows. The resulting endpoint is the next middle-section
source configuration (n-4, marker 1); it is not a proof of the remaining
15 rows or of the complete middle section.
-/

namespace BB6Coverage.Agent42MiddleSectionPrefix4

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6ChampionArithmetic
open BB6Coverage.Agent42M2OddGeneric
open BB6Coverage.Agent42M1EvenResidueSix
open BB6Coverage.Agent24M0OddResidueFive
open BB6Coverage.Agent48M2EvenResidueFour

set_option maxHeartbeats 3000000

def middleAfter1A (a b : Nat) : Nat := nextExponent 2 a b
def middleAfter1B (b : Nat) : Nat := nextRight b

def middleAfter2A (a b : Nat) : Nat :=
  nextExponent 1 (middleAfter1A a b) (middleAfter1B b)
def middleAfter2B (b : Nat) : Nat := nextRight (middleAfter1B b)

def middleAfter3A (a b : Nat) : Nat :=
  nextExponent 0 (middleAfter2A a b) (middleAfter2B b)
def middleAfter3B (b : Nat) : Nat := nextRight (middleAfter2B b)

def middleAfter4A (a b : Nat) : Nat :=
  nextExponent 2 (middleAfter3A a b) (middleAfter3B b)
def middleAfter4B (b : Nat) : Nat := nextRight (middleAfter3B b)

/-- Exact proposed-cost contribution of the first four middle-section rows. -/
def middleFirst4Cost (k a b : Nat) : Nat :=
  proposedIncrementCost 2 (8*k+7) a b +
  proposedIncrementCost 1 (8*k+6) (middleAfter1A a b) (middleAfter1B b) +
  proposedIncrementCost 0 (8*k+5) (middleAfter2A a b) (middleAfter2B b) +
  proposedIncrementCost 2 (8*k+4) (middleAfter3A a b) (middleAfter3B b)

/-- Total head displacement across the same four exact source increments. -/
def middleFirst4HeadShift (b : Nat) : Nat :=
  (5+3*b) +
  (5+3*middleAfter1B b) +
  (5+3*middleAfter2B b) +
  (5+3*middleAfter3B b)

private theorem run_compose
    {c d e : Config} {t u : Nat}
    (h1 : run tm2 t c = some d)
    (h2 : run tm2 u d = some e) :
    run tm2 (t+u) c = some e := by
  rw [run_add, h1]
  simpa using h2

/-- The sectionResult arithmetic cost splits at the exact same four-row
boundary used by the source-run composition below. -/
theorem sectionResult_first4_cost (k a b : Nat) :
    (sectionResult (8*k+7) 2 a b).cost =
      middleFirst4Cost k a b +
        (sectionResult (8*k+3) 1
          (middleAfter4A a b) (middleAfter4B b)).cost := by
  change proposedIncrementCost 2 (8*k+7) a b +
    (sectionResult (8*k+6) 1
      (middleAfter1A a b) (middleAfter1B b)).cost = _
  change proposedIncrementCost 2 (8*k+7) a b +
    (proposedIncrementCost 1 (8*k+6)
      (middleAfter1A a b) (middleAfter1B b) +
      (sectionResult (8*k+5) 0
        (middleAfter2A a b) (middleAfter2B b)).cost) = _
  change proposedIncrementCost 2 (8*k+7) a b +
    (proposedIncrementCost 1 (8*k+6)
      (middleAfter1A a b) (middleAfter1B b) +
      (proposedIncrementCost 0 (8*k+5)
        (middleAfter2A a b) (middleAfter2B b) +
        (sectionResult (8*k+4) 2
          (middleAfter3A a b) (middleAfter3B b)).cost)) = _
  change proposedIncrementCost 2 (8*k+7) a b +
    (proposedIncrementCost 1 (8*k+6)
      (middleAfter1A a b) (middleAfter1B b) +
      (proposedIncrementCost 0 (8*k+5)
        (middleAfter2A a b) (middleAfter2B b) +
        (proposedIncrementCost 2 (8*k+4)
          (middleAfter3A a b) (middleAfter3B b) +
          (sectionResult (8*k+3) 1
            (middleAfter4A a b) (middleAfter4B b)).cost))) = _
  simp [middleFirst4Cost, Nat.add_assoc]

/-- Four consecutive original-TM2 middle-section increments, for every
admissible n=8*k+7 source input. This composes:
* generic m=2 odd n;
* generalized m=1, n=8*k+6;
* generalized m=0, n=8*k+5;
* generalized m=2, n=8*k+4.

The output is exactly S1(L,n-4,1,a_4,0,b_4,h+shift), so the next
unresolved row is (n mod 8, marker)=(3,1). -/
theorem tm63_middle_first4_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+7 < 2^L) (ha : 0 < a) :
    run tm2 (middleFirst4Cost k a b)
      (s1Config L (8*k+7) 2 a 0 b h) =
      some (s1Config L (8*k+3) 1
        (middleAfter4A a b) 0 (middleAfter4B b)
        (h + (middleFirst4HeadShift b : Int))) := by
  let a1 := middleAfter1A a b
  let b1 := middleAfter1B b
  let a2 := middleAfter2A a b
  let b2 := middleAfter2B b
  let a3 := middleAfter3A a b
  let b3 := middleAfter3B b
  let a4 := middleAfter4A a b
  let b4 := middleAfter4B b
  let h1 : Int := h+5+3*b
  let h2 : Int := h1+5+3*b1
  let h3 : Int := h2+5+3*b2
  let h4 : Int := h3+5+3*b3

  have h0 :
      run tm2 (proposedIncrementCost 2 (8*k+7) a b)
        (s1Config L (8*k+7) 2 a 0 b h) =
      some (s1Config L (8*k+6) 1 a1 0 b1 h1) := by
    have hn : (8*k+7)%2 = 1 := by omega
    simpa [a1,b1,h1,middleAfter1A,middleAfter1B,nextExponent,nextRight] using
      m2Odd_counted_increment_source L (8*k+7) a b h hn hbound

  have ha1 : 0 < a1 := by
    dsimp [a1,middleAfter1A,nextExponent]
    omega
  have h1run :
      run tm2 (proposedIncrementCost 1 (8*k+6) a1 b1)
        (s1Config L (8*k+6) 1 a1 0 b1 h1) =
      some (s1Config L (8*k+5) 0 a2 0 b2 h2) := by
    simpa [a2,b2,h2,middleAfter2A,middleAfter2B,
      a1,b1,middleAfter1A,middleAfter1B,nextExponent,nextRight] using
      m1Even_residue6_counted_increment_source
        L k a1 b1 h1 hL (by omega) ha1

  have ha2 : 0 < a2 := by
    dsimp [a2,middleAfter2A,a1,b1,middleAfter1A,middleAfter1B,
      nextExponent,nextRight]
    omega
  have h2run :
      run tm2 (proposedIncrementCost 0 (8*k+5) a2 b2)
        (s1Config L (8*k+5) 0 a2 0 b2 h2) =
      some (s1Config L (8*k+4) 2 a3 0 b3 h3) := by
    simpa [a3,b3,h3,middleAfter3A,middleAfter3B,
      a2,b2,middleAfter2A,middleAfter2B,
      a1,b1,middleAfter1A,middleAfter1B,nextExponent,nextRight] using
      m0Odd_residue5_counted_increment_source
        L k a2 b2 h2 hL (by omega) ha2

  have ha3 : 0 < a3 := by
    dsimp [a3,middleAfter3A,a2,b2,middleAfter2A,middleAfter2B,
      a1,b1,middleAfter1A,middleAfter1B,nextExponent,nextRight]
    omega
  have h3run :
      run tm2 (proposedIncrementCost 2 (8*k+4) a3 b3)
        (s1Config L (8*k+4) 2 a3 0 b3 h3) =
      some (s1Config L (8*k+3) 1 a4 0 b4 h4) := by
    simpa [a4,b4,h4,middleAfter4A,middleAfter4B,
      a3,b3,middleAfter3A,middleAfter3B,
      a2,b2,middleAfter2A,middleAfter2B,
      a1,b1,middleAfter1A,middleAfter1B,nextExponent,nextRight] using
      m2Even_residue4_counted_increment_source
        L k a3 b3 h3 hL (by omega) ha3

  have h01 := run_compose h0 h1run
  have h012 := run_compose h01 h2run
  have h0123 := run_compose h012 h3run
  have hhead : h + (middleFirst4HeadShift b : Int) = h4 := by
    dsimp [middleFirst4HeadShift,h4,h3,h2,h1,
      middleAfter1B,middleAfter2B,middleAfter3B,b1,b2,b3,nextRight]
    omega
  rw [hhead]
  simpa [middleFirst4Cost,a1,b1,a2,b2,a3,b3,a4,b4,
    middleAfter1A,middleAfter1B,middleAfter2A,middleAfter2B,
    middleAfter3A,middleAfter3B,middleAfter4A,middleAfter4B,
    h1,h2,h3,h4,nextExponent,nextRight] using h0123

#print axioms sectionResult_first4_cost
#print axioms tm63_middle_first4_source

end BB6Coverage.Agent42MiddleSectionPrefix4
