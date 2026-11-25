import Raw10HardRootR1Adapter
import Raw10BoxCombinedConsumer
import BusyBeaver.Bridge
import BusyBeaver.Calculi.CtlCertificate
import BusyBeaver.BB6.NonHalt.M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw10CtlPartial

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent47WeightedHalt
open BB6.Agent49Box
open BB6.Agent49BoxBridge
open BB6.Agent17Raw10CombinedConsumer
open BB6.Agent50Raw10HardRootR1Adapter
open BB6.ConjectureBridge
open BusyBeaver.CtlCert

abbrev CtlSource :=
  BusyBeaver.BB6.NonHalt.M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH

def source2 : ConjectureMachines.Machine 6 2 := CtlSource.machine

def candidate2 : Machine :=
  BB6.ConjectureBridge.toAgent8 source2

private def boolToFin2 (b : Bool) : Fin 2 := if b then 1 else 0

private def fin2ToBool (a : Fin 2) : Bool := a.val == 1

private def boolToDir (b : Bool) : Turing.Dir :=
  if b then Turing.Dir.right else Turing.Dir.left

/-- Inverse adapter from the local two-symbol machine table to Cryptids. -/
def ofAgent8 (m : Machine) : ConjectureMachines.Machine 6 2 where
  transition q a :=
    (m (q, fin2ToBool a)).map fun mv =>
      (boolToFin2 mv.write, boolToDir mv.right, mv.next)

theorem toAgent8_ofAgent8 (m : Machine) :
    BB6.ConjectureBridge.toAgent8 (ofAgent8 m) = m := by
  funext s
  rcases s with ⟨q, b⟩
  cases b
  · cases h : m (q, false) with
    | none =>
        simp [ofAgent8, BB6.ConjectureBridge.toAgent8, h]
    | some mv =>
        cases mv with
        | mk w r n =>
            cases w <;> cases r <;>
              simp [ofAgent8, BB6.ConjectureBridge.toAgent8, h,
                boolToFin2, boolToDir, fin2ToBool]
  · cases h : m (q, true) with
    | none =>
        simp [ofAgent8, BB6.ConjectureBridge.toAgent8, h]
    | some mv =>
        cases mv with
        | mk w r n =>
            cases w <;> cases r <;>
              simp [ofAgent8, BB6.ConjectureBridge.toAgent8, h,
                boolToFin2, boolToDir, fin2ToBool]

theorem ofAgent8_candidate2 :
    ofAgent8 candidate2 = source2 := by
  funext q a
  fin_cases q
  all_goals
    fin_cases a
    all_goals
      simp [ofAgent8, candidate2, source2,
        BB6.ConjectureBridge.toAgent8, boolToFin2, boolToDir, fin2ToBool]

/-- A list-level congruence lemma: a Boolean fold is determined by its values
    on the elements of the list. -/
private theorem list_all_congr {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ x, x ∈ xs → f x = g x) :
    xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs : ∀ y, y ∈ xs → f y = g y := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih hxs]

/-- CTL checking depends on the machine only at the state/symbol pairs
    projected from the accepted quadruples. -/
theorem ctlCheck_congr
    {M N : BusyBeaver.Machine (Fin 2) (Fin 6)}
    (dL : Fin 4 → Fin 2 → Fin 4)
    (dR : Fin 4 → Fin 2 → Fin 4)
    (acc : List (Fin 4 × Fin 6 × Fin 2 × Fin 4))
    (h : ∀ p s a q, (p, s, a, q) ∈ acc → M s a = N s a) :
    ctlCheck M dL dR acc = ctlCheck N dL dR acc := by
  unfold ctlCheck
  congr 1
  apply list_all_congr
  intro x hx
  rcases x with ⟨p, s, a, q⟩
  simp [closureOk, h p s a q hx]

/-- Keep only the transition pairs read by a CTL certificate. -/
def ctlLeafFor (candidate : Machine) (used : List Slot) : PartialMachine :=
  fun s => if s ∈ used then some (candidate s) else none

private def used2 : List Slot :=
  [(0, false), (1, false), (2, true), (4, false)]

private def ctlAcc2 :=
  CtlSource.ctlAcc

private theorem ctlAcc2_used :
    ∀ p s a q, (p, s, a, q) ∈ ctlAcc2 →
      (s, fin2ToBool a) ∈ used2 := by
  decide

def ctlLeaf2 : PartialMachine :=
  ctlLeafFor candidate2 used2

private theorem ctlCheck_target2 :
    ctlCheck CtlSource.target CtlSource.ctlLeftDfa
      CtlSource.ctlRightDfa ctlAcc2 = true := by
  decide +kernel

/-- Every completion of the four-transition CTL cylinder is nonhalting. -/
theorem ctlLeaf2_neverHalts (m : Machine)
    (hm : compatible ctlLeaf2 m) : NeverHalts m := by
  have hAgree :
      ∀ p s a q, (p, s, a, q) ∈ ctlAcc2 →
        (ofAgent8 m).toBB s a = CtlSource.target s a := by
    intro p s a q hmem
    have hslot : (s, fin2ToBool a) ∈ used2 :=
      ctlAcc2_used p s a q hmem
    have hleaf :
        ctlLeaf2 (s, fin2ToBool a) =
          some (candidate2 (s, fin2ToBool a)) := by
      simp [ctlLeaf2, ctlLeafFor, hslot]
    have hmove : m (s, fin2ToBool a) =
        candidate2 (s, fin2ToBool a) :=
      hm _ _ hleaf
    calc
      (ofAgent8 m).toBB s a =
          (ofAgent8 candidate2).toBB s a := by
            simp [ofAgent8, hmove, boolToFin2, boolToDir, fin2ToBool]
      _ = CtlSource.target s a := by
            rw [ofAgent8_candidate2]
            rfl
  have hctl :
      ctlCheck (ofAgent8 m).toBB CtlSource.ctlLeftDfa
        CtlSource.ctlRightDfa ctlAcc2 = true := by
    rw [ctlCheck_congr CtlSource.ctlLeftDfa CtlSource.ctlRightDfa
      ctlAcc2 hAgree]
    exact ctlCheck_target2
  have hIsNotHalt :
      BusyBeaver.IsNotHalt (ofAgent8 m).toBB :=
    ctl_certificate_implies_is_does_not_halt
      (ofAgent8 m).toBB CtlSource.ctlLeftDfa
      CtlSource.ctlRightDfa ctlAcc2 hctl
  have hNoHalt : ¬ ConjectureMachines.Halts (ofAgent8 m) :=
    (ConjectureMachines.isNotHalt_toBB_iff_not_halts
      (ofAgent8 m)).mp hIsNotHalt
  have hNever :=
    BB6.ConjectureBridge.not_halts_to_agent8 (ofAgent8 m) hNoHalt
  simpa [toAgent8_ofAgent8] using hNever

def ctlLeaf2Certificate (B : Nat) :
    WeightedTNFCertificate B ctlLeaf2 6 :=
  .nonhalt
    (by decide)
    (by decide)
    (by decide)
    (by
      intro m hm
      exact ctlLeaf2_neverHalts m hm)

def certifiedTablesWithCtl2 : List PartialMachine :=
  certifiedTablesWithCycleAndHalt ++ [ctlLeaf2]

def raw10RemainderWithCtl2 : List (Box Slot Transition) :=
  remainder firstOneB0_1LC certifiedTablesWithCtl2

theorem raw10RemainderWithCtl2_exact (m : Machine) :
    (∃ r ∈ raw10RemainderWithCtl2, Fits r m) ↔
    compatible firstOneB0_1LC m ∧
      (∀ w ∈ b0_1lcSideWitnesses,
        ¬ compatible (unpackTable w.table) m) ∧
      ¬ compatible held m ∧
      ¬ compatible table m ∧
      ¬ compatible haltTable m ∧
      ¬ compatible ctlLeaf2 m := by
  rw [raw10RemainderWithCtl2, remainder_exact]
  simp only [certifiedTablesWithCtl2, List.mem_append,
    certifiedTablesWithCycleAndHalt, sideTables, List.mem_map,
    List.mem_cons, List.mem_singleton]
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨hp, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw
      exact hn _ (Or.inl ⟨w, hw, rfl⟩)
    · exact hn held (Or.inr (Or.inl rfl))
    · exact hn table (Or.inr (Or.inr (Or.inl rfl)))
    · exact hn haltTable (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact hn ctlLeaf2 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · rintro ⟨hp, hs, hh, hc, hhalt, hctl⟩
    refine ⟨hp, ?_⟩
    intro q hq
    rcases hq with hside | htail
    · obtain ⟨w, hw, rfl⟩ := hside
      exact hs w hw
    · rcases htail with hHeldMem | htail
      · have he : q = held := by simpa using hHeldMem
        subst q
        exact hh
      · rcases htail with hCycleMem | htail
        · have he : q = table := by simpa using hCycleMem
          subst q
          exact hc
        · rcases htail with hHaltMem | htail
          · have he : q = haltTable := by simpa using hHaltMem
            subst q
            exact hhalt
          · have he : q = ctlLeaf2 := by simpa using htail
            subst q
            exact hctl

theorem raw10RemainderWithCtl2_disjoint :
    raw10RemainderWithCtl2.Pairwise Disjoint :=
  remainder_disjoint _ _

theorem raw10RemainderWithCtl2_count :
    raw10RemainderWithCtl2.length = 47 := by
  decide

def allSlots : List Slot :=
  (List.finRange 6).flatMap fun q => [(q, false), (q, true)]

def boxMass (b : Box Slot Transition) : Nat :=
  (allSlots.map fun s => (b s).length).prod

theorem ctlLeaf2_assignedCount :
    (allSlots.filter fun s => (ctlLeaf2 s).isSome).length = 4 := by
  decide

theorem ctlLeaf2_completionCount :
    25 ^ 8 = 152_587_890_625 := by
  norm_num

theorem raw10RemainderWithCtl2_mass :
    (raw10RemainderWithCtl2.map boxMass).sum =
      90_584_915_823_100 := by
  decide

/-- Conditional score-B consumer after removing the 25^8 CTL cylinder. -/
def raw10CoverWithCtl2 (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10RemainderWithCtl2,
      ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  coverFromRemainder B firstOneB0_1LC certifiedTablesWithCtl2
    (fun q hq m hm => by
      rcases List.mem_append.mp hq with hbase | hctl
      · rcases List.mem_append.mp hbase with hs | htail
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs
          have hb := b0_1lcSideWitnesses_safe w hw m hm
          intro k d hk hd
          exact Nat.le_trans (hb k d hk hd) hB
        · rcases List.mem_cons.mp htail with hHeldMem | htail
          · have he : q = held := by simpa using hHeldMem
            subst q
            exact hHeld m hm
          · rcases List.mem_cons.mp htail with hCycleMem | htail
            · have he : q = table := by simpa using hCycleMem
              subst q
              exact (BB6.Agent50Raw10Box8.cover B).sound hm
            · rcases List.mem_singleton.mp htail with hHaltMem
              have he : q = haltTable := by simpa using hHaltMem
              subst q
              have h7014 := BB6.Agent50Raw10Box0Halt.cover.sound hm
              intro k d hk hd
              exact Nat.le_trans (h7014 k d hk hd) hB
      · have he : q = ctlLeaf2 := by simpa using hctl
        subst q
        exact (ctlLeaf2Certificate B).sound hm)
    hOpen

#print axioms toAgent8_ofAgent8
#print axioms ofAgent8_candidate2
#print axioms ctlCheck_congr
#print axioms ctlLeaf2_neverHalts
#print axioms ctlLeaf2Certificate
#print axioms raw10RemainderWithCtl2_exact
#print axioms raw10RemainderWithCtl2_disjoint
#print axioms raw10CoverWithCtl2

end BB6.Agent50Raw10CtlPartial
