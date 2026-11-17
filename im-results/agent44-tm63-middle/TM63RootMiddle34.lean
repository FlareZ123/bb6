import TM63RootMiddle26
import M0OddGenericSource
import M2EvenResidueFour
import M1OddResidueThree
import M0EvenResidueTwo
import M2OddGenericStage
import M2EvenSixGenericCounted
import M1EvenValuationSource
import Lean.Elab.Tactic.Omega

/-!
Unconditional TM63 root continuation through middle row 34.

Rows 27--31 use the established source increment theorems. Row 32 is
now discharged by the valuation-parametric M1 source theorem, which
covers every positive bounded binary counter. The all-odd M0 theorem
supplies row 33, and the generic M2-even-six theorem supplies row 34.
-/

namespace BB6Coverage.Agent44TM63RootMiddle34

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent49TM63RootResidueSixteen
open BB6Coverage.Agent42TM63RootMiddle26
open BB6Coverage.Agent48M0OddGenericSource
open BB6Coverage.Agent48M2EvenResidueFour
open BB6Coverage.Agent8M1OddResidueThree
open BB6Coverage.Agent24M0EvenResidueTwo
open BB6Coverage.Agent42M2OddGeneric
open BB6Coverage.Agent44M2EvenSixGenericCounted
open BB6Coverage.Agent48M1EvenValuationCountedSource
open BB6ChampionArithmetic

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

private theorem tm63_root_residue_six_k_ge_61 :
    61 ≤ tm63RootResidueSixK := by
  have hA : 5 ≤ tm63FirstSection.exponent :=
    tm63FirstSection_exponent_ge_five
  have hsub : 2 ≤ tm63FirstSection.exponent-3 := by omega
  have hpow : 4 ≤ 2^(tm63FirstSection.exponent-3) := by
    calc
      4 = 2^2 := by decide
      _ ≤ 2^(tm63FirstSection.exponent-3) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) hsub
  have hK : 123 ≤ tm63RootMiddleK := by
    unfold tm63RootMiddleK
    omega
  unfold tm63RootResidueSixK
  omega

def tm63MiddleAfter27A : Nat :=
  tm63MiddleAfter26A+tm63MiddleAfter26B+1

def tm63MiddleAfter27B : Nat :=
  2^tm63MiddleAfter26B-1

def tm63MiddleAfter27Head : Int :=
  tm63MiddleAfter26Head+5+3*tm63MiddleAfter26B

def tm63MiddleAfter28A : Nat :=
  tm63MiddleAfter27A+tm63MiddleAfter27B+2

def tm63MiddleAfter28B : Nat :=
  2^tm63MiddleAfter27B-1

def tm63MiddleAfter28Head : Int :=
  tm63MiddleAfter27Head+5+3*tm63MiddleAfter27B

def tm63MiddleAfter29A : Nat :=
  tm63MiddleAfter28A+tm63MiddleAfter28B+2

def tm63MiddleAfter29B : Nat :=
  2^tm63MiddleAfter28B-1

def tm63MiddleAfter29Head : Int :=
  tm63MiddleAfter28Head+5+3*tm63MiddleAfter28B

def tm63MiddleAfter30A : Nat :=
  tm63MiddleAfter29A+tm63MiddleAfter29B+1

def tm63MiddleAfter30B : Nat :=
  2^tm63MiddleAfter29B-1

def tm63MiddleAfter30Head : Int :=
  tm63MiddleAfter29Head+5+3*tm63MiddleAfter29B

def tm63MiddleAfter31A : Nat :=
  tm63MiddleAfter30A+tm63MiddleAfter30B+2

def tm63MiddleAfter31B : Nat :=
  2^tm63MiddleAfter30B-1

def tm63MiddleAfter31Head : Int :=
  tm63MiddleAfter30Head+5+3*tm63MiddleAfter30B

def tm63MiddleAfter32A : Nat :=
  tm63MiddleAfter31A+tm63MiddleAfter31B+2

def tm63MiddleAfter32B : Nat :=
  2^tm63MiddleAfter31B-1

def tm63MiddleAfter32Head : Int :=
  tm63MiddleAfter31Head+5+3*tm63MiddleAfter31B

def tm63MiddleAfter33A : Nat :=
  tm63MiddleAfter32A+tm63MiddleAfter32B+1

def tm63MiddleAfter33B : Nat :=
  2^tm63MiddleAfter32B-1

def tm63MiddleAfter33Head : Int :=
  tm63MiddleAfter32Head+5+3*tm63MiddleAfter32B

def tm63MiddleAfter34A : Nat :=
  tm63MiddleAfter33A+tm63MiddleAfter33B+2

def tm63MiddleAfter34B : Nat :=
  2^tm63MiddleAfter33B-1

def tm63MiddleAfter34Head : Int :=
  tm63MiddleAfter33Head+5+3*tm63MiddleAfter33B

def tm63MiddleFirst27Moves : Nat :=
  tm63MiddleFirst26Moves+
    proposedIncrementCost 0 (16*tm63RootResidueSixK-11)
      tm63MiddleAfter26A tm63MiddleAfter26B

def tm63MiddleFirst28Moves : Nat :=
  tm63MiddleFirst27Moves+
    proposedIncrementCost 2 (16*tm63RootResidueSixK-12)
      tm63MiddleAfter27A tm63MiddleAfter27B

def tm63MiddleFirst29Moves : Nat :=
  tm63MiddleFirst28Moves+
    proposedIncrementCost 1 (16*tm63RootResidueSixK-13)
      tm63MiddleAfter28A tm63MiddleAfter28B

def tm63MiddleFirst30Moves : Nat :=
  tm63MiddleFirst29Moves+
    proposedIncrementCost 0 (16*tm63RootResidueSixK-14)
      tm63MiddleAfter29A tm63MiddleAfter29B

def tm63MiddleFirst31Moves : Nat :=
  tm63MiddleFirst30Moves+
    proposedIncrementCost 2 (16*tm63RootResidueSixK-15)
      tm63MiddleAfter30A tm63MiddleAfter30B

def tm63MiddleFirst32Moves : Nat :=
  tm63MiddleFirst31Moves+
    proposedIncrementCost 1 (16*tm63RootResidueSixK-16)
      tm63MiddleAfter31A tm63MiddleAfter31B

def tm63MiddleFirst33Moves : Nat :=
  tm63MiddleFirst32Moves+
    proposedIncrementCost 0 (16*tm63RootResidueSixK-17)
      tm63MiddleAfter32A tm63MiddleAfter32B

def tm63MiddleFirst34Moves : Nat :=
  tm63MiddleFirst33Moves+
    proposedIncrementCost 2 (16*tm63RootResidueSixK-18)
      tm63MiddleAfter33A tm63MiddleAfter33B

/-- Compose rows 27--34 from the authentic blank-root middle-26 endpoint.
The only remaining hypothesis is the exact arbitrary-valuation M1-even
source increment at row 32, input n=16*r-16=32*((r-1)/2). -/
theorem tm63_blank_reaches_after_middle34 :
    run tm2 tm63MiddleFirst34Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-19) 1
        tm63MiddleAfter34A 0 tm63MiddleAfter34B
        tm63MiddleAfter34Head) := by
  have hrGe := tm63_root_residue_six_k_ge_61
  have hindex :
      tm63Index1 = 16*tm63RootResidueSixK+15 := by
    simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15
  have hroot := tm63_index1_lt_pow_length1
  rw [hindex] at hroot
  have hL : 3 ≤ tm63Length1 := by
    have hL4 := tm63_root_length_ge_four
    omega
  have hLpos : 0 < tm63Length1 := by omega
  have ha26 : 0 < tm63MiddleAfter26A := by
    unfold tm63MiddleAfter26A
    omega

  have hn27 : (16*tm63RootResidueSixK-11)%2=1 := by omega
  have hbound27 :
      16*tm63RootResidueSixK-11 < 2^tm63Length1 := by omega
  have h27 := m0Odd_counted_increment_source
    tm63Length1 (16*tm63RootResidueSixK-11)
    tm63MiddleAfter26A tm63MiddleAfter26B tm63MiddleAfter26Head
    hLpos hn27 hbound27 ha26
  have htarget27 :
      (16*tm63RootResidueSixK-11)-1 =
        16*tm63RootResidueSixK-12 := by omega
  have h27' :
      run tm2
        (proposedIncrementCost 0 (16*tm63RootResidueSixK-11)
          tm63MiddleAfter26A tm63MiddleAfter26B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-11) 0
          tm63MiddleAfter26A 0 tm63MiddleAfter26B
          tm63MiddleAfter26Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-12) 2
        tm63MiddleAfter27A 0 tm63MiddleAfter27B
        tm63MiddleAfter27Head) := by
    simpa [htarget27,tm63MiddleAfter27A,tm63MiddleAfter27B,
      tm63MiddleAfter27Head] using h27

  have hinput28 :
      8*(2*tm63RootResidueSixK-2)+4 =
        16*tm63RootResidueSixK-12 := by omega
  have htarget28 :
      8*(2*tm63RootResidueSixK-2)+3 =
        16*tm63RootResidueSixK-13 := by omega
  have hbound28 :
      8*(2*tm63RootResidueSixK-2)+4 < 2^tm63Length1 := by
    rw [hinput28]
    omega
  have ha27 : 0 < tm63MiddleAfter27A := by
    unfold tm63MiddleAfter27A
    omega
  have h28 := m2Even_residue4_counted_increment_source
    tm63Length1 (2*tm63RootResidueSixK-2)
    tm63MiddleAfter27A tm63MiddleAfter27B tm63MiddleAfter27Head
    hL hbound28 ha27
  have h28' :
      run tm2
        (proposedIncrementCost 2
          (16*tm63RootResidueSixK-12)
          tm63MiddleAfter27A tm63MiddleAfter27B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-12) 2
          tm63MiddleAfter27A 0 tm63MiddleAfter27B
          tm63MiddleAfter27Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-13) 1
        tm63MiddleAfter28A 0 tm63MiddleAfter28B
        tm63MiddleAfter28Head) := by
    simpa [hinput28,htarget28,tm63MiddleAfter28A,
      tm63MiddleAfter28B,tm63MiddleAfter28Head] using h28

  have hinput29 :
      8*(2*tm63RootResidueSixK-2)+3 =
        16*tm63RootResidueSixK-13 := by omega
  have htarget29 :
      8*(2*tm63RootResidueSixK-2)+2 =
        16*tm63RootResidueSixK-14 := by omega
  have hbound29 :
      8*(2*tm63RootResidueSixK-2)+3 < 2^tm63Length1 := by
    rw [hinput29]
    omega
  have ha28 : 0 < tm63MiddleAfter28A := by
    unfold tm63MiddleAfter28A
    omega
  have h29 := m1OddResidueThree_counted_increment_source
    tm63Length1 (2*tm63RootResidueSixK-2)
    tm63MiddleAfter28A tm63MiddleAfter28B tm63MiddleAfter28Head
    hL hbound29 ha28
  have h29' :
      run tm2
        (proposedIncrementCost 1
          (16*tm63RootResidueSixK-13)
          tm63MiddleAfter28A tm63MiddleAfter28B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-13) 1
          tm63MiddleAfter28A 0 tm63MiddleAfter28B
          tm63MiddleAfter28Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-14) 0
        tm63MiddleAfter29A 0 tm63MiddleAfter29B
        tm63MiddleAfter29Head) := by
    simpa [hinput29,htarget29,tm63MiddleAfter29A,
      tm63MiddleAfter29B,tm63MiddleAfter29Head] using h29

  have hinput30 :
      8*(2*tm63RootResidueSixK-2)+2 =
        16*tm63RootResidueSixK-14 := by omega
  have htarget30 :
      8*(2*tm63RootResidueSixK-2)+1 =
        16*tm63RootResidueSixK-15 := by omega
  have hbound30 :
      8*(2*tm63RootResidueSixK-2)+2 < 2^tm63Length1 := by
    rw [hinput30]
    omega
  have ha29 : 0 < tm63MiddleAfter29A := by
    unfold tm63MiddleAfter29A
    omega
  have h30 := m0Even_residue2_counted_increment_source
    tm63Length1 (2*tm63RootResidueSixK-2)
    tm63MiddleAfter29A tm63MiddleAfter29B tm63MiddleAfter29Head
    hL hbound30 ha29
  have h30' :
      run tm2
        (proposedIncrementCost 0
          (16*tm63RootResidueSixK-14)
          tm63MiddleAfter29A tm63MiddleAfter29B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-14) 0
          tm63MiddleAfter29A 0 tm63MiddleAfter29B
          tm63MiddleAfter29Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-15) 2
        tm63MiddleAfter30A 0 tm63MiddleAfter30B
        tm63MiddleAfter30Head) := by
    simpa [hinput30,htarget30,tm63MiddleAfter30A,
      tm63MiddleAfter30B,tm63MiddleAfter30Head] using h30

  have hn31 : (16*tm63RootResidueSixK-15)%2=1 := by omega
  have hbound31 :
      16*tm63RootResidueSixK-15 < 2^tm63Length1 := by omega
  have h31 := m2Odd_counted_increment_source
    tm63Length1 (16*tm63RootResidueSixK-15)
    tm63MiddleAfter30A tm63MiddleAfter30B tm63MiddleAfter30Head
    hn31 hbound31
  have hn32 : 0 < 16*tm63RootResidueSixK-16 := by omega
  have hbound32 :
      16*tm63RootResidueSixK-16 < 2^tm63Length1 := by omega
  have ha31 : 0 < tm63MiddleAfter31A := by
    unfold tm63MiddleAfter31A
    omega
  have h32raw := m1EvenValuation_counted_increment_source
    tm63Length1 (16*tm63RootResidueSixK-16)
    tm63MiddleAfter31A tm63MiddleAfter31B tm63MiddleAfter31Head
    hn32 hbound32 ha31
  have h32 :
      run tm2
        (proposedIncrementCost 1 (16*tm63RootResidueSixK-16)
          tm63MiddleAfter31A tm63MiddleAfter31B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-16) 1
          tm63MiddleAfter31A 0 tm63MiddleAfter31B
          tm63MiddleAfter31Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-17) 0
        tm63MiddleAfter32A 0 tm63MiddleAfter32B
        tm63MiddleAfter32Head) := by
    simpa [tm63MiddleAfter32A,tm63MiddleAfter32B,
      tm63MiddleAfter32Head] using h32raw

  have htarget31 :
      (16*tm63RootResidueSixK-15)-1 =
        16*tm63RootResidueSixK-16 := by omega
  have h31' :
      run tm2
        (proposedIncrementCost 2
          (16*tm63RootResidueSixK-15)
          tm63MiddleAfter30A tm63MiddleAfter30B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-15) 2
          tm63MiddleAfter30A 0 tm63MiddleAfter30B
          tm63MiddleAfter30Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-16) 1
        tm63MiddleAfter31A 0 tm63MiddleAfter31B
        tm63MiddleAfter31Head) := by
    simpa [htarget31,tm63MiddleAfter31A,tm63MiddleAfter31B,
      tm63MiddleAfter31Head] using h31

  have hn33 :
      (16*tm63RootResidueSixK-17)%2=1 := by omega
  have hbound33 :
      16*tm63RootResidueSixK-17 < 2^tm63Length1 := by omega
  have ha32 : 0 < tm63MiddleAfter32A := by
    unfold tm63MiddleAfter32A
    omega
  have h33 := m0Odd_counted_increment_source
    tm63Length1 (16*tm63RootResidueSixK-17)
    tm63MiddleAfter32A tm63MiddleAfter32B tm63MiddleAfter32Head
    hLpos hn33 hbound33 ha32
  have htarget33 :
      (16*tm63RootResidueSixK-17)-1 =
        16*tm63RootResidueSixK-18 := by omega
  have h33' :
      run tm2
        (proposedIncrementCost 0
          (16*tm63RootResidueSixK-17)
          tm63MiddleAfter32A tm63MiddleAfter32B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-17) 0
          tm63MiddleAfter32A 0 tm63MiddleAfter32B
          tm63MiddleAfter32Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-18) 2
        tm63MiddleAfter33A 0 tm63MiddleAfter33B
        tm63MiddleAfter33Head) := by
    simpa [htarget33,tm63MiddleAfter33A,tm63MiddleAfter33B,
      tm63MiddleAfter33Head] using h33

  have hinput34 :
      8*(2*tm63RootResidueSixK-3)+6 =
        16*tm63RootResidueSixK-18 := by omega
  have htarget34 :
      8*(2*tm63RootResidueSixK-3)+5 =
        16*tm63RootResidueSixK-19 := by omega
  have hbound34 :
      8*(2*tm63RootResidueSixK-3)+6 < 2^tm63Length1 := by
    rw [hinput34]
    omega
  have ha33 : 0 < tm63MiddleAfter33A := by
    unfold tm63MiddleAfter33A
    omega
  have h34 := m2EvenSix_generic_counted_increment_source
    tm63Length1 (2*tm63RootResidueSixK-3)
    tm63MiddleAfter33A tm63MiddleAfter33B tm63MiddleAfter33Head
    hL hbound34 ha33
  have h34' :
      run tm2
        (proposedIncrementCost 2
          (16*tm63RootResidueSixK-18)
          tm63MiddleAfter33A tm63MiddleAfter33B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-18) 2
          tm63MiddleAfter33A 0 tm63MiddleAfter33B
          tm63MiddleAfter33Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-19) 1
        tm63MiddleAfter34A 0 tm63MiddleAfter34B
        tm63MiddleAfter34Head) := by
    simpa [hinput34,htarget34,tm63MiddleAfter34A,
      tm63MiddleAfter34B,tm63MiddleAfter34Head] using h34

  have hcomp27 := run_compose_local
    tm63_blank_reaches_after_middle26 h27'
  have hcomp28 := run_compose_local hcomp27 h28'
  have hcomp29 := run_compose_local hcomp28 h29'
  have hcomp30 := run_compose_local hcomp29 h30'
  have hcomp31 := run_compose_local hcomp30 h31'
  have hcomp32 := run_compose_local hcomp31 h32
  have hcomp33 := run_compose_local hcomp32 h33'
  have hcomp34 := run_compose_local hcomp33 h34'
  simpa [tm63MiddleFirst34Moves] using hcomp34

/-- Backwards-compatible conditional wrapper; the premise is no
longer needed because the row-32 source theorem is proved above. -/
theorem tm63_blank_reaches_after_middle34_of_m1even32
    (_h32 :
      run tm2
        (proposedIncrementCost 1 (16*tm63RootResidueSixK-16)
          tm63MiddleAfter31A tm63MiddleAfter31B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-16) 1
          tm63MiddleAfter31A 0 tm63MiddleAfter31B
          tm63MiddleAfter31Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-17) 0
        tm63MiddleAfter32A 0 tm63MiddleAfter32B
        tm63MiddleAfter32Head)) :
    run tm2 tm63MiddleFirst34Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-19) 1
        tm63MiddleAfter34A 0 tm63MiddleAfter34B
        tm63MiddleAfter34Head) :=
  tm63_blank_reaches_after_middle34

#print axioms tm63_blank_reaches_after_middle34
#print axioms tm63_blank_reaches_after_middle34_of_m1even32

end BB6Coverage.Agent44TM63RootMiddle34
