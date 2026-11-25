import CryptidsTapeAdapter
import Mathlib.Tactic
import BusyBeaver.Bridge
import BusyBeaver.Calculi.CtlCertificate
import BusyBeaver.BB6.NonHalt.M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH

set_option maxRecDepth 100000
set_option maxHeartbeats 0

universe u

namespace BB6.Agent50CtlFootprint

open BusyBeaver.CtlCert

abbrev CtlSource := BusyBeaver.M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH

def source2 : ConjectureMachines.Machine 6 2 := CtlSource.machine
def candidate2 : BB6Coverage.Machine := BB6.ConjectureBridge.toAgent8 source2
private def target2 : BusyBeaver.Machine (Fin 2) (Fin 6) := source2.toBB

private def boolToFin2 (b : Bool) : Fin 2 := if b then 1 else 0
private def fin2ToBool (a : Fin 2) : Bool := a.val == 1
private def boolToDir (b : Bool) : Turing.Dir :=
  if b then Turing.Dir.right else Turing.Dir.left

/-- Inverse adapter from the local absolute-tape machine convention to Cryptids. -/
def ofAgent8 (m : BB6Coverage.Machine) : ConjectureMachines.Machine 6 2 where
  transition q a :=
    (m (q, fin2ToBool a)).map fun mv =>
      (boolToFin2 mv.write, boolToDir mv.right, mv.next)

/-- The two local/source machine adapters are inverse on every one of the
    twelve state-symbol inputs. The proof reduces the private bit/direction
    helpers in the pinned adapter by computation. -/
theorem toAgent8_ofAgent8 (m : BB6Coverage.Machine) :
    BB6.ConjectureBridge.toAgent8 (ofAgent8 m) = m := by
  funext s
  rcases s with ⟨q, b⟩
  cases b
  · cases h : m (q, false) with
    | none => rfl
    | some mv =>
        cases mv with
        | mk w r n => cases w <;> cases r <;> rfl
  · cases h : m (q, true) with
    | none => rfl
    | some mv =>
        cases mv with
        | mk w r n => cases w <;> cases r <;> rfl

/-- The inverse adapter recovers the exact pinned Cryptids source machine. -/
theorem ofAgent8_candidate2 : ofAgent8 candidate2 = source2 := by
  ext q a
  fin_cases q
  all_goals
    fin_cases a
    all_goals rfl

private theorem list_all_congr {α : Type u} (xs : List α) (f g : α → Bool)
    (h : ∀ x, x ∈ xs → f x = g x) : xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs : ∀ y, y ∈ xs → f y = g y := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih hxs]

/-- The CTL checker reads the transition table only at state-symbol pairs
    projected from accepted quadruples. DFA sizes and machine state type
    are polymorphic. -/
theorem ctlCheck_congr
    {Λ : Type*} [Inhabited Λ] [DecidableEq Λ]
    {nL nR : Nat} [NeZero nL] [NeZero nR]
    {M N : BusyBeaver.Machine (Fin 2) Λ}
    (dL : Fin nL → Fin 2 → Fin nL)
    (dR : Fin nR → Fin 2 → Fin nR)
    (acc : List (Fin nL × Λ × Fin 2 × Fin nR))
    (h : ∀ p s a q, (p, s, a, q) ∈ acc → M s a = N s a) :
    ctlCheck M dL dR acc = ctlCheck N dL dR acc := by
  unfold ctlCheck
  congr 1
  apply list_all_congr
  intro x hx
  rcases x with ⟨p, s, a, q⟩
  simp [closureOk, h p s a q hx]

/-- Upstream CTL soundness transfers to any machine agreeing on the exact
    transition footprint. -/
theorem ctl_certificate_implies_is_does_not_halt_of_agreement
    {Λ : Type*} [Inhabited Λ] [DecidableEq Λ]
    {nL nR : Nat} [NeZero nL] [NeZero nR]
    {M N : BusyBeaver.Machine (Fin 2) Λ}
    (dL : Fin nL → Fin 2 → Fin nL)
    (dR : Fin nR → Fin 2 → Fin nR)
    (acc : List (Fin nL × Λ × Fin 2 × Fin nR))
    (hCheck : ctlCheck N dL dR acc = true)
    (hAgree : ∀ p s a q, (p, s, a, q) ∈ acc → M s a = N s a) :
    BusyBeaver.IsNotHalt M := by
  apply ctl_certificate_implies_is_does_not_halt M dL dR acc
  rw [ctlCheck_congr dL dR acc hAgree]
  exact hCheck

/-- The following DFA tables and accepted tuples are copied verbatim from
    the pinned source module. They are not exported by that upstream module's
    module visibility boundary, so the kernel check is replayed here. -/
private def ctlLeftDfaTable : List (Fin 3) := [0, 1, 2, 2, 2, 2]
private def ctlLeftDfa (p : Fin 3) (a : Fin 2) : Fin 3 :=
  ctlLeftDfaTable.getD (2 * p.val + a.val) 0

private def ctlRightDfaTable : List (Fin 2) := [0, 1, 1, 1]
private def ctlRightDfa (p : Fin 2) (a : Fin 2) : Fin 2 :=
  ctlRightDfaTable.getD (2 * p.val + a.val) 0

private def ctlAcc2 : List (Fin 3 × Fin 6 × Fin 2 × Fin 2) :=
  [(0, 0, 0, 0), (0, 2, 1, 1), (0, 4, 0, 1), (1, 1, 0, 0)]

/-- Exact projection of the pinned accepted quadruple list onto machine
    state-symbol pairs: A0, B0, C1 and E0. -/
def used2 : List BB6Coverage.Slot := [(0, false), (1, false), (2, true), (4, false)]

private theorem ctlAcc2_used :
    ∀ p : Fin 3, ∀ s : Fin 6, ∀ a : Fin 2, ∀ q : Fin 2,
      (p, s, a, q) ∈ ctlAcc2 → (s, fin2ToBool a) ∈ used2 := by
  decide

/-- Exact equality between the projected CTL footprint and the four fixed slots. -/
theorem ctlAcc2_footprint :
    ∀ s : Fin 6, ∀ b : Bool, (s, b) ∈ used2 ↔
      ∃ p : Fin 3, ∃ a : Fin 2, ∃ q : Fin 2,
        (p, s, a, q) ∈ ctlAcc2 ∧ b = fin2ToBool a := by
  decide

def ctlLeafFor (candidate : BB6Coverage.Machine)
    (used : List BB6Coverage.Slot) : BB6Coverage.PartialMachine :=
  fun s => if s ∈ used then some (candidate s) else none

/-- The exact 4-transition, 8-hole partial table induced by the pinned CTL
    certificate. -/
def ctlLeaf2 : BB6Coverage.PartialMachine := ctlLeafFor candidate2 used2

theorem ctlCheck_target2 :
    ctlCheck target2 ctlLeftDfa ctlRightDfa ctlAcc2 = true := by
  decide +kernel

/-- Every completion of the four-transition CTL cylinder is nonhalting. -/
theorem ctlLeaf2_neverHalts (m : BB6Coverage.Machine)
    (hm : BB6Coverage.compatible ctlLeaf2 m) :
    BB6Coverage.NeverHalts m := by
  have hAgree :
      ∀ p : Fin 3, ∀ s : Fin 6, ∀ a : Fin 2, ∀ q : Fin 2,
        (p, s, a, q) ∈ ctlAcc2 → (ofAgent8 m).toBB s a = target2 s a := by
    intro p s a q hmem
    have hslot : (s, fin2ToBool a) ∈ used2 := ctlAcc2_used p s a q hmem
    have hleaf :
        ctlLeaf2 (s, fin2ToBool a) =
          some (candidate2 (s, fin2ToBool a)) := by
      simp [ctlLeaf2, ctlLeafFor, hslot]
    have hmove : m (s, fin2ToBool a) = candidate2 (s, fin2ToBool a) :=
      hm _ _ hleaf
    calc
      (ofAgent8 m).toBB s a =
          (ofAgent8 candidate2).toBB s a := by
            simp [ofAgent8, hmove, boolToFin2, boolToDir, fin2ToBool]
      _ = target2 s a := by
            rw [ofAgent8_candidate2]
            rfl
  have hIsNotHalt : BusyBeaver.IsNotHalt (ofAgent8 m).toBB :=
    ctl_certificate_implies_is_does_not_halt_of_agreement
      ctlLeftDfa ctlRightDfa ctlAcc2 ctlCheck_target2 hAgree
  have hNoHalt : ¬ ConjectureMachines.Halts (ofAgent8 m) :=
    (ConjectureMachines.isNotHalt_toBB_iff_not_halts (ofAgent8 m)).mp hIsNotHalt
  have hNever := BB6.ConjectureBridge.not_halts_to_agent8 (ofAgent8 m) hNoHalt
  simpa [toAgent8_ofAgent8] using hNever

private def allSlots : List BB6Coverage.Slot :=
  (List.finRange 6).flatMap fun q => [(q, false), (q, true)]

theorem ctlLeaf2_assignedCount :
    (allSlots.filter fun s => (ctlLeaf2 s).isSome).length = 4 := by
  decide

theorem ctlLeaf2_holes_exact :
    ∀ s, ctlLeaf2 s = none ↔ s ∉ used2 := by
  intro s
  simp [ctlLeaf2, ctlLeafFor]

theorem ctlLeaf2_completionCount : 25 ^ 8 = 152_587_890_625 := by
  decide

#print axioms toAgent8_ofAgent8
#print axioms ofAgent8_candidate2
#print axioms ctlCheck_congr
#print axioms ctl_certificate_implies_is_does_not_halt_of_agreement
#print axioms ctlAcc2_footprint
#print axioms ctlCheck_target2
#print axioms ctlLeaf2_neverHalts
#print axioms ctlLeaf2_assignedCount
#print axioms ctlLeaf2_holes_exact
#print axioms ctlLeaf2_completionCount

end BB6.Agent50CtlFootprint
