import TM63RootMiddle34
import M1OddResidueFive
import M0EvenResidueFour
import M2OddGenericStage
import Lean.Elab.Tactic.Omega

/-!
# Authentic TM63 blank-root continuation through middle row 37

This appends the next three exact source increments after the row-34
endpoint: marker 1 at n=16*r-19 (residue 5), marker 0 at n=16*r-20
(residue 4), and marker 2 at n=16*r-21 (odd).  The source modules are
kept in im-results until the focused original-source Lean closure and
transitive axiom audit pass.
-/

namespace BB6Coverage.Agent44TM63RootMiddle37

open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent49TM63RootResidueSixteen
open BB6Coverage.Agent42TM63RootMiddle26
open BB6Coverage.Agent44TM63RootMiddle34
open BB6Coverage.Agent24M1ResidueFive
open BB6Coverage.Agent48M0EvenResidueFour
open BB6Coverage.Agent42M2OddGeneric
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6ChampionArithmetic

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

def tm63MiddleAfter35A : Nat :=
  tm63MiddleAfter34A+tm63MiddleAfter34B+2

def tm63MiddleAfter35B : Nat :=
  2^tm63MiddleAfter34B-1

def tm63MiddleAfter35Head : Int :=
  tm63MiddleAfter34Head+5+3*tm63MiddleAfter34B

def tm63MiddleAfter36A : Nat :=
  tm63MiddleAfter35A+tm63MiddleAfter35B+1

def tm63MiddleAfter36B : Nat :=
  2^tm63MiddleAfter35B-1

def tm63MiddleAfter36Head : Int :=
  tm63MiddleAfter35Head+5+3*tm63MiddleAfter35B

def tm63MiddleAfter37A : Nat :=
  tm63MiddleAfter36A+tm63MiddleAfter36B+2

def tm63MiddleAfter37B : Nat :=
  2^tm63MiddleAfter36B-1

def tm63MiddleAfter37Head : Int :=
  tm63MiddleAfter36Head+5+3*tm63MiddleAfter36B

def tm63MiddleFirst35Moves : Nat :=
  tm63MiddleFirst34Moves+
    proposedIncrementCost 1 (16*tm63RootResidueSixK-19)
      tm63MiddleAfter34A tm63MiddleAfter34B

def tm63MiddleFirst36Moves : Nat :=
  tm63MiddleFirst35Moves+
    proposedIncrementCost 0 (16*tm63RootResidueSixK-20)
      tm63MiddleAfter35A tm63MiddleAfter35B

def tm63MiddleFirst37Moves : Nat :=
  tm63MiddleFirst36Moves+
    proposedIncrementCost 2 (16*tm63RootResidueSixK-21)
      tm63MiddleAfter36A tm63MiddleAfter36B

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Source row 35: marker 1, n=16*r-19=8*(2*r-3)+5. -/
theorem tm63_middle35_source :
    run tm2
      (proposedIncrementCost 1 (16*tm63RootResidueSixK-19)
        tm63MiddleAfter34A tm63MiddleAfter34B)
      (s1Config tm63Length1
        (16*tm63RootResidueSixK-19) 1
        tm63MiddleAfter34A 0 tm63MiddleAfter34B
        tm63MiddleAfter34Head) =
    some (s1Config tm63Length1
      (16*tm63RootResidueSixK-20) 0
      tm63MiddleAfter35A 0 tm63MiddleAfter35B
      tm63MiddleAfter35Head) := by
  have hrGe := tm63_root_residue_six_k_ge_61
  have hindex :
      tm63Index1 = 16*tm63RootResidueSixK+15 := by
    simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15
  have hroot := tm63_index1_lt_pow_length1
  rw [hindex] at hroot
  have hL : 3 ≤ tm63Length1 := by
    have hL4 := tm63_root_length_ge_four
    omega
  have hbound :
      8*(2*tm63RootResidueSixK-3)+5 < 2^tm63Length1 := by
    omega
  have ha : 0 < tm63MiddleAfter34A := by
    unfold tm63MiddleAfter34A
    omega
  have hraw := m1ResidueFive_counted_increment_source
    tm63Length1 (2*tm63RootResidueSixK-3)
    tm63MiddleAfter34A tm63MiddleAfter34B tm63MiddleAfter34Head
    hL hbound ha
  have hinput :
      8*(2*tm63RootResidueSixK-3)+5 =
        16*tm63RootResidueSixK-19 := by omega
  have htarget :
      8*(2*tm63RootResidueSixK-3)+4 =
        16*tm63RootResidueSixK-20 := by omega
  simpa [hinput,htarget,tm63MiddleAfter35A,
    tm63MiddleAfter35B,tm63MiddleAfter35Head] using hraw

/-- Source row 36: marker 0, n=16*r-20=8*(2*r-3)+4. -/
theorem tm63_middle36_source :
    run tm2
      (proposedIncrementCost 0 (16*tm63RootResidueSixK-20)
        tm63MiddleAfter35A tm63MiddleAfter35B)
      (s1Config tm63Length1
        (16*tm63RootResidueSixK-20) 0
        tm63MiddleAfter35A 0 tm63MiddleAfter35B
        tm63MiddleAfter35Head) =
    some (s1Config tm63Length1
      (16*tm63RootResidueSixK-21) 2
      tm63MiddleAfter36A 0 tm63MiddleAfter36B
      tm63MiddleAfter36Head) := by
  have hrGe := tm63_root_residue_six_k_ge_61
  have hindex :
      tm63Index1 = 16*tm63RootResidueSixK+15 := by
    simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15
  have hroot := tm63_index1_lt_pow_length1
  rw [hindex] at hroot
  have hL : 3 ≤ tm63Length1 := by
    have hL4 := tm63_root_length_ge_four
    omega
  have hbound :
      8*(2*tm63RootResidueSixK-3)+4 < 2^tm63Length1 := by
    omega
  have ha : 0 < tm63MiddleAfter35A := by
    unfold tm63MiddleAfter35A
    omega
  have hraw := m0Even_residue4_counted_increment_source
    tm63Length1 (2*tm63RootResidueSixK-3)
    tm63MiddleAfter35A tm63MiddleAfter35B tm63MiddleAfter35Head
    hL hbound ha
  have hinput :
      8*(2*tm63RootResidueSixK-3)+4 =
        16*tm63RootResidueSixK-20 := by omega
  have htarget :
      8*(2*tm63RootResidueSixK-3)+3 =
        16*tm63RootResidueSixK-21 := by omega
  simpa [hinput,htarget,tm63MiddleAfter36A,
    tm63MiddleAfter36B,tm63MiddleAfter36Head] using hraw

/-- Source row 37: marker 2, odd n=16*r-21. -/
theorem tm63_middle37_source :
    run tm2
      (proposedIncrementCost 2 (16*tm63RootResidueSixK-21)
        tm63MiddleAfter36A tm63MiddleAfter36B)
      (s1Config tm63Length1
        (16*tm63RootResidueSixK-21) 2
        tm63MiddleAfter36A 0 tm63MiddleAfter36B
        tm63MiddleAfter36Head) =
    some (s1Config tm63Length1
      (16*tm63RootResidueSixK-22) 1
      tm63MiddleAfter37A 0 tm63MiddleAfter37B
      tm63MiddleAfter37Head) := by
  have hrGe := tm63_root_residue_six_k_ge_61
  have hindex :
      tm63Index1 = 16*tm63RootResidueSixK+15 := by
    simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15
  have hroot := tm63_index1_lt_pow_length1
  rw [hindex] at hroot
  have hn : (16*tm63RootResidueSixK-21)%2=1 := by omega
  have hbound :
      16*tm63RootResidueSixK-21 < 2^tm63Length1 := by omega
  have hraw := m2Odd_counted_increment_source
    tm63Length1 (16*tm63RootResidueSixK-21)
    tm63MiddleAfter36A tm63MiddleAfter36B
    tm63MiddleAfter36Head hn hbound
  simpa [tm63MiddleAfter37A,tm63MiddleAfter37B,
    tm63MiddleAfter37Head] using hraw

/-- Authentic blank-root source run through rows 27--37. -/
theorem tm63_blank_reaches_after_middle37 :
    run tm2 tm63MiddleFirst37Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-22) 1
        tm63MiddleAfter37A 0 tm63MiddleAfter37B
        tm63MiddleAfter37Head) := by
  have h35 := tm63_middle35_source
  have h36 := tm63_middle36_source
  have h37 := tm63_middle37_source
  have hcomp35 := run_compose_local
    tm63_blank_reaches_after_middle34 h35
  have hcomp36 := run_compose_local hcomp35 h36
  have hcomp37 := run_compose_local hcomp36 h37
  simpa [tm63MiddleFirst37Moves] using hcomp37

#print axioms tm63_middle35_source
#print axioms tm63_middle36_source
#print axioms tm63_middle37_source
#print axioms tm63_blank_reaches_after_middle37

end BB6Coverage.Agent44TM63RootMiddle37
