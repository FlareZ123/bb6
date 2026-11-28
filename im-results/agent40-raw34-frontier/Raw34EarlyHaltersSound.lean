import Raw34OtherD1Halt8
import Raw34OtherD1Halt9New
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
The original-source finite halting witnesses from two Raw34 early banks
give *actual halt queries*, not merely WeightedBound 32, for every total
completion. This is the semantic disjointness needed to aggregate their
physical volumes with nonhalting proof families.
-/
namespace BB6.Agent40Raw34EarlyHalters
open BB6Coverage BB6.Agent23Raw34Next

theorem finite_check_exact_halt
    (p : PartialMachine) (n : Nat) (m : Machine)
    (hm : compatible p m) (h : finiteHaltCheck p n = true) :
    HaltsAfter m n := by
  unfold HaltsAfter
  cases he : finitePartialRun p n finiteBlank with
  | none => simp [finiteHaltCheck, he] at h
  | some c =>
    have hhalt : p (c.state, finiteTape c c.head) = some none := by
      simpa only [finiteHaltCheck, he, decide_eq_true_eq] using h
    have hr : run m n blank = some (embedFinRay c) := by
      have hs := finitePartialRun_sound p m hm finiteBlank c n he
      simpa only [embedFinRay_blank] using hs
    have hnone : m (c.state, finiteTape c c.head) = none := hm _ _ hhalt
    constructor
    · simp [hr]
    · simp [run, hr, rawStep, readSlot, embedFinRay, hnone]

def isShortHalt (bound : Nat) (w : Witness) : Bool :=
  match w.cert with
  | .halt n => decide (n+1 ≤ bound)
  | .side .. => false

theorem short_halt_sound (bound : Nat) (w : Witness)
    (hshort : isShortHalt bound w = true)
    (hcheck : check w = true)
    (m : Machine) (hm : compatible (table w.codes) m) :
    ∃ n : Nat, n+1 ≤ bound ∧ HaltsAfter m n := by
  cases w with
  | mk codes cert =>
    cases cert with
    | halt n =>
      have hb : decide (n+1 ≤ bound) = true := by
        simpa only [isShortHalt] using hshort
      have hn : n+1 ≤ bound := of_decide_eq_true hb
      have hh : decide (n+1 ≤ 27) = true ∧
          finiteHaltCheck (table codes) n = true := by
        simpa only [check, Bool.and_eq_true] using hcheck
      exact ⟨n, hn, finite_check_exact_halt (table codes) n m hm hh.2⟩
    | side entry period right boundary =>
      simp only [isShortHalt] at hshort
      contradiction

theorem short_bank8 :
    BB6.Agent40Raw34Halt8.witnesses.all (isShortHalt 8) = true := by
  decide

theorem short_bank9 :
    BB6.Agent40Raw34Halt9New.witnesses.all (isShortHalt 9) = true := by
  decide +kernel

theorem all_bank8_halt (w : Witness)
    (hw : w ∈ BB6.Agent40Raw34Halt8.witnesses)
    (m : Machine) (hm : compatible (table w.codes) m) :
    ∃ n : Nat, n+1 ≤ 8 ∧ HaltsAfter m n :=
  short_halt_sound 8 w
    (List.all_eq_true.mp short_bank8 w hw)
    (List.all_eq_true.mp BB6.Agent40Raw34Halt8.checked w hw)
    m hm

theorem all_bank9_halt (w : Witness)
    (hw : w ∈ BB6.Agent40Raw34Halt9New.witnesses)
    (m : Machine) (hm : compatible (table w.codes) m) :
    ∃ n : Nat, n+1 ≤ 9 ∧ HaltsAfter m n :=
  short_halt_sound 9 w
    (List.all_eq_true.mp short_bank9 w hw)
    (List.all_eq_true.mp BB6.Agent40Raw34Halt9New.checked w hw)
    m hm

#print axioms finite_check_exact_halt
#print axioms short_halt_sound
#print axioms short_bank8
#print axioms short_bank9
#print axioms all_bank8_halt
#print axioms all_bank9_halt
end BB6.Agent40Raw34EarlyHalters
