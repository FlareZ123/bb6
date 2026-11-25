import CryptidsTapeAdapter
import BusyBeaver.Bridge
import BusyBeaver.Calculi.CtlCertificate
import BusyBeaver.BB6.NonHalt.M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50CtlFootprint
open BusyBeaver.CtlCert

abbrev CtlSource := BusyBeaver.M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH
def source2 : ConjectureMachines.Machine 6 2 := CtlSource.machine
def candidate2 : BB6Coverage.Machine := BB6.ConjectureBridge.toAgent8 source2

private def boolToFin2 (b : Bool) : Fin 2 := if b then 1 else 0
private def fin2ToBool (a : Fin 2) : Bool := a.val == 1
private def boolToDir (b : Bool) : Turing.Dir := if b then Turing.Dir.right else Turing.Dir.left

/-- Inverse adapter from the local absolute-tape machine convention to Cryptids. -/
def ofAgent8 (m : BB6Coverage.Machine) : ConjectureMachines.Machine 6 2 where
  transition q a :=
    (m (q, fin2ToBool a)).map fun mv =>
      (boolToFin2 mv.write, boolToDir mv.right, mv.next)

theorem toAgent8_ofAgent8 (m : BB6Coverage.Machine) :
    BB6.ConjectureBridge.toAgent8 (ofAgent8 m) = m := by
  funext s
  rcases s with ⟨q, b⟩
  cases b
  · cases h : m (q, false) with
    | none => simp [ofAgent8, BB6.ConjectureBridge.toAgent8, h]
    | some mv =>
        cases mv with
        | mk w r n =>
            cases w <;> cases r <;>
              simp [ofAgent8, BB6.ConjectureBridge.toAgent8, h,
                boolToFin2, boolToDir, fin2ToBool]
  · cases h : m (q, true) with
    | none => simp [ofAgent8, BB6.ConjectureBridge.toAgent8, h]
    | some mv =>
        cases mv with
        | mk w r n =>
            cases w <;> cases r <;>
              simp [ofAgent8, BB6.ConjectureBridge.toAgent8, h,
                boolToFin2, boolToDir, fin2ToBool]

theorem ofAgent8_candidate2 : ofAgent8 candidate2 = source2 := by
  funext q a
  fin_cases q
  all_goals
    fin_cases a
    all_goals
      simp [ofAgent8, candidate2, source2,
        BB6.ConjectureBridge.toAgent8, boolToFin2, boolToDir, fin2ToBool]

private theorem list_all_congr {α : Type} (xs : List α) (f g : α → Bool)
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
    projected from accepted quadruples. DFA sizes are polymorphic. -/
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

private def ctlAcc2 := CtlSource.ctlAcc
def used2 : List BB6Coverage.Slot := [(0, false), (1, false), (2, true), (4, false)]

private theorem ctlAcc2_used :
    ∀ p s a q, (p, s, a, q) ∈ ctlAcc2 →
      (s, fin2ToBool a) ∈ used2 := by
  decide

/-- Exact equality between the projected CTL footprint and the four fixed slots. -/
theorem ctlAcc2_footprint :
    ∀ s b, (s, b) ∈ used2 ↔
      ∃ p a q, (p, s, a, q) ∈ ctlAcc2 ∧ b = fin2ToBool a := by
  decide

def ctlLeafFor (candidate : BB6Coverage.Machine)
    (used : List BB6Coverage.Slot) : BB6Coverage.PartialMachine :=
  fun s => if s ∈ used then some (candidate s) else none

/-- The 4-transition, 8-hole partial table induced by the pinned CTL certificate. -/
def ctlLeaf2 : BB6Coverage.PartialMachine := ctlLeafFor candidate2 used2

private theorem ctlCheck_target2 :
    ctlCheck CtlSource.target CtlSource.ctlLeftDfa
      CtlSource.ctlRightDfa ctlAcc2 = true := by
  decide +kernel

/-- Every completion of the four-transition CTL cylinder is nonhalting. -/
theorem ctlLeaf2_neverHalts (m : BB6Coverage.Machine)
    (hm : BB6Coverage.compatible ctlLeaf2 m) :
    BB6Coverage.NeverHalts m := by
  have hAgree :
      ∀ p s a q, (p, s, a, q) ∈ ctlAcc2 →
        (ofAgent8 m).toBB s a = CtlSource.target s a := by
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
      _ = CtlSource.target s a := by
            rw [ofAgent8_candidate2]
            rfl
  have hIsNotHalt : BusyBeaver.IsNotHalt (ofAgent8 m).toBB :=
    ctl_certificate_implies_is_does_not_halt_of_agreement
      CtlSource.ctlLeftDfa CtlSource.ctlRightDfa ctlAcc2 ctlCheck_target2 hAgree
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
