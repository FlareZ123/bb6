import Raw10CtlFootprint
import Mathlib.Tactic
import BusyBeaver.Bridge
import BusyBeaver.Calculi.CtlCertificate
import BusyBeaver.BB6.NonHalt.M_1RB0RC_1LC0LD_1RA1RC_1RA1LE_0LB1RE_HHH1RA

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50CtlFootprintSecond

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.CtlCert

abbrev CtlSource :=
  BusyBeaver.M_1RB0RC_1LC0LD_1RA1RC_1RA1LE_0LB1RE_HHH1RA

/-- Re-elaborate the exact pinned RLE locally so the finite CTL checker
    can reduce the transition table in this module. -/
def source3 : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RC_1LC0LD_1RA1RC_1RA1LE_0LB1RE_HHH1RA"

theorem source3_eq_pinned : source3 = CtlSource.machine := rfl
def candidate3 : BB6Coverage.Machine :=
  BB6.ConjectureBridge.toAgent8 source3

private abbrev target3 : BusyBeaver.Machine (Fin 2) (Fin 6) := source3.toBB

private def boolToFin2 (b : Bool) : Fin 2 := if b then 1 else 0
private def fin2ToBool (a : Fin 2) : Bool := a.val == 1
private def boolToDir (b : Bool) : Turing.Dir :=
  if b then Turing.Dir.right else Turing.Dir.left

def ofAgent8_3 (m : BB6Coverage.Machine) :
    ConjectureMachines.Machine 6 2 where
  transition q a :=
    (m (q, fin2ToBool a)).map fun mv =>
      (boolToFin2 mv.write, boolToDir mv.right, mv.next)

/-- The inverse adapter is a left inverse on every local transition table. -/
theorem toAgent8_ofAgent8_3 (m : BB6Coverage.Machine) :
    BB6.ConjectureBridge.toAgent8 (ofAgent8_3 m) = m := by
  funext s
  rcases s with ⟨q, b⟩
  cases b
  · cases h : m (q, false) with
    | none =>
        simp [BB6.ConjectureBridge.toAgent8, ofAgent8_3, h]
    | some mv =>
        cases mv with
        | mk w r n =>
            cases w <;> cases r <;>
              simp [BB6.ConjectureBridge.toAgent8, ofAgent8_3, h,
                boolToFin2, boolToDir, fin2ToBool]
  · cases h : m (q, true) with
    | none =>
        simp [BB6.ConjectureBridge.toAgent8, ofAgent8_3, h]
    | some mv =>
        cases mv with
        | mk w r n =>
            cases w <;> cases r <;>
              simp [BB6.ConjectureBridge.toAgent8, ofAgent8_3, h,
                boolToFin2, boolToDir, fin2ToBool]

/-- Recover the exact pinned source target after the local inverse adapter. -/
theorem ofAgent8_candidate3_toBB :
    (ofAgent8_3 candidate3).toBB = target3 := by
  funext q a
  fin_cases q <;> fin_cases a <;>
    simp [target3, source3, candidate3, ofAgent8_3,
      BB6.ConjectureBridge.toAgent8, ConjectureMachines.Machine.toBB,
      boolToFin2, boolToDir, fin2ToBool]

/-- The source DFA tables and accepted tuples are copied verbatim from the
    pinned module. Its source-side dimensions are Fin 1 and Fin 3. -/
private def ctlLeftDfaTable3 : List (Fin 1) := [0, 0]
private def ctlLeftDfa3 (p : Fin 1) (a : Fin 2) : Fin 1 :=
  ctlLeftDfaTable3.getD (2 * p.val + a.val) 0

private def ctlRightDfaTable3 : List (Fin 3) := [0, 1, 2, 2, 2, 2]
private def ctlRightDfa3 (p : Fin 3) (a : Fin 2) : Fin 3 :=
  ctlRightDfaTable3.getD (2 * p.val + a.val) 0

private def ctlAcc3 : List (Fin 1 × Fin 6 × Fin 2 × Fin 3) := [
  (0, 0, 0, 0), (0, 0, 1, 0), (0, 1, 0, 0), (0, 2, 0, 0),
  (0, 2, 0, 1), (0, 2, 1, 0), (0, 2, 1, 1)
]

/-- Exact projection of the accepted tuples onto A0, A1, B0, C0 and C1. -/
def used3 : List BB6Coverage.Slot :=
  [(0, false), (0, true), (1, false), (2, false), (2, true)]

private theorem ctlAcc3_used :
    ∀ p : Fin 1, ∀ s : Fin 6, ∀ a : Fin 2, ∀ q : Fin 3,
      (p, s, a, q) ∈ ctlAcc3 → (s, fin2ToBool a) ∈ used3 := by
  decide

/-- The five-pair transition footprint is exactly the projection of ctlAcc3. -/
theorem ctlAcc3_footprint :
    ∀ s : Fin 6, ∀ b : Bool, (s, b) ∈ used3 ↔
      ∃ p : Fin 1, ∃ a : Fin 2, ∃ q : Fin 3,
        (p, s, a, q) ∈ ctlAcc3 ∧ b = fin2ToBool a := by
  decide

def ctlLeaf3 : BB6Coverage.PartialMachine :=
  BB6.Agent50CtlFootprint.ctlLeafFor candidate3 used3

/-- Recheck the copied accepted tuples against the exact pinned source target. -/
theorem ctlCheck_target3 :
    ctlCheck target3 ctlLeftDfa3 ctlRightDfa3 ctlAcc3 = true := by
  decide +kernel

/-- Every completion of the five-transition CTL cylinder is nonhalting. -/
theorem ctlLeaf3_neverHalts (m : BB6Coverage.Machine)
    (hm : BB6Coverage.compatible ctlLeaf3 m) :
    BB6Coverage.NeverHalts m := by
  have hAgree :
      ∀ p : Fin 1, ∀ s : Fin 6, ∀ a : Fin 2, ∀ q : Fin 3,
        (p, s, a, q) ∈ ctlAcc3 →
          (ofAgent8_3 m).toBB s a = target3 s a := by
    intro p s a q hmem
    have hslot : (s, fin2ToBool a) ∈ used3 :=
      ctlAcc3_used p s a q hmem
    have hleaf :
        ctlLeaf3 (s, fin2ToBool a) =
          some (candidate3 (s, fin2ToBool a)) := by
      simp [ctlLeaf3, BB6.Agent50CtlFootprint.ctlLeafFor, hslot]
    have hmove : m (s, fin2ToBool a) =
        candidate3 (s, fin2ToBool a) := hm _ _ hleaf
    calc
      (ofAgent8_3 m).toBB s a =
          (ofAgent8_3 candidate3).toBB s a := by
            have hTransition :
                (ofAgent8_3 m).transition s a =
                  (ofAgent8_3 candidate3).transition s a := by
              change
                (m (s, fin2ToBool a)).map
                    (fun mv => (boolToFin2 mv.write, boolToDir mv.right, mv.next)) =
                  (candidate3 (s, fin2ToBool a)).map
                    (fun mv => (boolToFin2 mv.write, boolToDir mv.right, mv.next))
              rw [hmove]
            simp [ConjectureMachines.Machine.toBB, hTransition]
      _ = target3 s a := by
            rw [ofAgent8_candidate3_toBB]
  have hIsNotHalt : BusyBeaver.IsNotHalt
      (ofAgent8_3 m).toBB :=
    BB6.Agent50CtlFootprint.ctl_certificate_implies_is_does_not_halt_of_agreement
      ctlLeftDfa3 ctlRightDfa3 ctlAcc3 ctlCheck_target3 hAgree
  have hNoHalt :
      ¬ ConjectureMachines.Halts (BB6.Agent50CtlFootprint.ofAgent8 m) :=
    (ConjectureMachines.isNotHalt_toBB_iff_not_halts
      (BB6.Agent50CtlFootprint.ofAgent8 m)).mp hIsNotHalt
  have hNever :=
    BB6.ConjectureBridge.not_halts_to_agent8
      (BB6.Agent50CtlFootprint.ofAgent8 m) hNoHalt
  simpa [toAgent8_ofAgent8_3] using hNever

private def allSlots3 : List BB6Coverage.Slot :=
  (List.finRange 6).flatMap fun q => [(q, false), (q, true)]

theorem ctlLeaf3_assignedCount :
    (allSlots3.filter fun s => (ctlLeaf3 s).isSome).length = 5 := by
  decide

theorem ctlLeaf3_holes_exact :
    ∀ s, ctlLeaf3 s = none ↔ s ∉ used3 := by
  intro s
  simp [ctlLeaf3, BB6.Agent50CtlFootprint.ctlLeafFor]

theorem ctlLeaf3_completionCount :
    25 ^ 7 = 6_103_515_625 := by
  decide

#print axioms ofAgent8_candidate3_toBB
#print axioms ctlAcc3_footprint
#print axioms ctlCheck_target3
#print axioms ctlLeaf3_neverHalts
#print axioms ctlLeaf3_assignedCount
#print axioms ctlLeaf3_holes_exact
#print axioms ctlLeaf3_completionCount

end BB6.Agent50CtlFootprintSecond
