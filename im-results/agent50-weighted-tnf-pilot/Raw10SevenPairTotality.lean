import Frontier
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw10SevenPairTotality

open BB6Coverage

/-- A total six-state transition table cannot halt under the repository's
    standard semantics: every attempted transition has a successor. -/
theorem neverHalts_of_total (m : Machine)
    (htotal : ∀ s, m s ≠ none) : NeverHalts m := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hrun : run m n blank with
    | none => simp [hrun] at ih
    | some c =>
      simp [run, hrun, rawStep, htotal (readSlot c)]

/-- The fixed ten-transition prefix from the Raw10 two-hole residual:
    A0=1RB, A1=0RD, B0=1LC, B1=1LB, C0=0LE, C1=1RA,
    D0=0LC, D1=0RA, E0=1LF, E1=1LD. F0 and F1 are the two holes. -/
def raw10Prefix : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true  => some (some ⟨false, true, 3⟩)
  | 1, false => some (some ⟨true, false, 2⟩)
  | 1, true  => some (some ⟨true, false, 1⟩)
  | 2, false => some (some ⟨false, false, 4⟩)
  | 2, true  => some (some ⟨true, true, 0⟩)
  | 3, false => some (some ⟨false, false, 2⟩)
  | 3, true  => some (some ⟨false, true, 0⟩)
  | 4, false => some (some ⟨true, false, 5⟩)
  | 4, true  => some (some ⟨true, false, 3⟩)
  | 5, false => none
  | 5, true  => none

/-- Fill F0/F1 using the repository's 25-choice ordering. -/
def fillF (f0 f1 : Move) : Machine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true  => some ⟨false, true, 3⟩
  | 1, false => some ⟨true, false, 2⟩
  | 1, true  => some ⟨true, false, 1⟩
  | 2, false => some ⟨false, false, 4⟩
  | 2, true  => some ⟨true, true, 0⟩
  | 3, false => some ⟨false, false, 2⟩
  | 3, true  => some ⟨false, true, 0⟩
  | 4, false => some ⟨true, false, 5⟩
  | 4, true  => some ⟨true, false, 3⟩
  | 5, false => some f0
  | 5, true  => some f1

/-- The code indices are the positions in `choices`: 0 is the genuine
    halting outcome, and every positive code is an ordinary move. -/
theorem code12_is_1RC :
    choices.get? 12 = some (some ⟨true, true, 2⟩) := by decide
theorem code1_is_0LA :
    choices.get? 1 = some (some ⟨false, false, 0⟩) := by decide
theorem code14_is_0RD :
    choices.get? 14 = some (some ⟨false, true, 3⟩) := by decide
theorem code15_is_1LD :
    choices.get? 15 = some (some ⟨true, false, 3⟩) := by decide
theorem code22_is_0RF :
    choices.get? 22 = some (some ⟨false, true, 5⟩) := by decide
theorem code2_is_0RA :
    choices.get? 2 = some (some ⟨false, true, 0⟩) := by decide
theorem code24_is_1RF :
    choices.get? 24 = some (some ⟨true, true, 5⟩) := by decide
theorem code3_is_1LA :
    choices.get? 3 = some (some ⟨true, false, 0⟩) := by decide

/-- Seven singleton completions left by the two-hole crosswalk. -/
def pair12_1 : Machine :=
  fillF ⟨true, true, 2⟩ ⟨false, false, 0⟩
def pair12_14 : Machine :=
  fillF ⟨true, true, 2⟩ ⟨false, true, 3⟩
def pair12_15 : Machine :=
  fillF ⟨true, true, 2⟩ ⟨true, false, 3⟩
def pair12_22 : Machine :=
  fillF ⟨true, true, 2⟩ ⟨false, true, 5⟩
def pair22_2 : Machine :=
  fillF ⟨false, true, 5⟩ ⟨false, true, 0⟩
def pair24_2 : Machine :=
  fillF ⟨true, true, 5⟩ ⟨false, true, 0⟩
def pair24_3 : Machine :=
  fillF ⟨true, true, 5⟩ ⟨true, false, 0⟩

theorem pair12_1_extends_prefix : compatible raw10Prefix pair12_1 := by decide
theorem pair12_14_extends_prefix : compatible raw10Prefix pair12_14 := by decide
theorem pair12_15_extends_prefix : compatible raw10Prefix pair12_15 := by decide
theorem pair12_22_extends_prefix : compatible raw10Prefix pair12_22 := by decide
theorem pair22_2_extends_prefix : compatible raw10Prefix pair22_2 := by decide
theorem pair24_2_extends_prefix : compatible raw10Prefix pair24_2 := by decide
theorem pair24_3_extends_prefix : compatible raw10Prefix pair24_3 := by decide

/-- Each singleton completion has all twelve transitions defined. -/
theorem pair12_1_total : ∀ s, pair12_1 s ≠ none := by decide
theorem pair12_14_total : ∀ s, pair12_14 s ≠ none := by decide
theorem pair12_15_total : ∀ s, pair12_15 s ≠ none := by decide
theorem pair12_22_total : ∀ s, pair12_22 s ≠ none := by decide
theorem pair22_2_total : ∀ s, pair22_2 s ≠ none := by decide
theorem pair24_2_total : ∀ s, pair24_2 s ≠ none := by decide
theorem pair24_3_total : ∀ s, pair24_3 s ≠ none := by decide

/-- Hence all seven are nonhalting without any cycle or growth argument. -/
theorem pair12_1_neverHalts : NeverHalts pair12_1 :=
  neverHalts_of_total pair12_1 pair12_1_total
theorem pair12_14_neverHalts : NeverHalts pair12_14 :=
  neverHalts_of_total pair12_14 pair12_14_total
theorem pair12_15_neverHalts : NeverHalts pair12_15 :=
  neverHalts_of_total pair12_15 pair12_15_total
theorem pair12_22_neverHalts : NeverHalts pair12_22 :=
  neverHalts_of_total pair12_22 pair12_22_total
theorem pair22_2_neverHalts : NeverHalts pair22_2 :=
  neverHalts_of_total pair22_2 pair22_2_total
theorem pair24_2_neverHalts : NeverHalts pair24_2 :=
  neverHalts_of_total pair24_2 pair24_2_total
theorem pair24_3_neverHalts : NeverHalts pair24_3 :=
  neverHalts_of_total pair24_3 pair24_3_total

#print axioms neverHalts_of_total
#print axioms code12_is_1RC
#print axioms code1_is_0LA
#print axioms code14_is_0RD
#print axioms code15_is_1LD
#print axioms code22_is_0RF
#print axioms code2_is_0RA
#print axioms code24_is_1RF
#print axioms code3_is_1LA
#print axioms pair12_1_extends_prefix
#print axioms pair12_14_extends_prefix
#print axioms pair12_15_extends_prefix
#print axioms pair12_22_extends_prefix
#print axioms pair22_2_extends_prefix
#print axioms pair24_2_extends_prefix
#print axioms pair24_3_extends_prefix
#print axioms pair12_1_total
#print axioms pair12_14_total
#print axioms pair12_15_total
#print axioms pair12_22_total
#print axioms pair22_2_total
#print axioms pair24_2_total
#print axioms pair24_3_total
#print axioms pair12_1_neverHalts
#print axioms pair12_14_neverHalts
#print axioms pair12_15_neverHalts
#print axioms pair12_22_neverHalts
#print axioms pair22_2_neverHalts
#print axioms pair24_2_neverHalts
#print axioms pair24_3_neverHalts

end BB6.Agent50Raw10SevenPairTotality
