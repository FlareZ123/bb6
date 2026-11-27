import Raw11FreshCut
import RootFrontier

namespace BB6.Agent24Raw11Q0Graft

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent44Raw11
open BB6.Agent50RootFrontier

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A table extension relation: every assignment in p is retained by q. -/
def extendsTable (p q : PartialMachine) : Prop :=
  ∀ s, p s = none ∨ q s = p s

/-- Executable finite quantification over the twelve transition slots. -/
instance (p q : PartialMachine) : Decidable (extendsTable p q) := by
  apply decidable_of_iff
    (∀ a : Fin 6, (p (a,false) = none ∨ q (a,false) = p (a,false)) ∧
                    (p (a,true) = none ∨ q (a,true) = p (a,true)))
  constructor
  · intro h ⟨a,b⟩
    cases b
    · exact (h a).1
    · exact (h a).2
  · intro h a
    constructor
    · exact h (a,false)
    · exact h (a,true)

theorem extendsTable_compat {p q : PartialMachine}
    (h : extendsTable p q) : ∀ s t, p s = some t → q s = some t := by
  intro s t hs
  rcases h s with hnone | heq
  · rw [hs] at hnone
    contradiction
  · rw [heq]
    exact hs

/-- Add one defined transition without changing any other slot. -/
def addRow (p : PartialMachine) (s : Slot) (mv : Move) : PartialMachine :=
  fun s' => if s' = s then some (some mv) else p s'

/-- The sixteen non-singleton q0 checkpoint rows, represented as refinements
    of the Raw11 parent. -/
def q0Partial (a1 c1 : Move) : PartialMachine :=
  addRow (addRow parent (0, true) a1) (2, true) c1

def m1LC : Move := ⟨true, false, ⟨2, by decide⟩⟩
def m0LC : Move := ⟨false, false, ⟨2, by decide⟩⟩

def m0LA : Move := ⟨false, false, ⟨0, by decide⟩⟩
def m0RA : Move := ⟨false, true,  ⟨0, by decide⟩⟩
def m1LA : Move := ⟨true,  false, ⟨0, by decide⟩⟩
def m1RA : Move := ⟨true,  true,  ⟨0, by decide⟩⟩
def m0LB : Move := ⟨false, false, ⟨1, by decide⟩⟩
def m0RB : Move := ⟨false, true,  ⟨1, by decide⟩⟩
def m1LB : Move := ⟨true,  false, ⟨1, by decide⟩⟩
def m1RB : Move := ⟨true,  true,  ⟨1, by decide⟩⟩
def m0RC : Move := ⟨false, true,  ⟨2, by decide⟩⟩
def m1RC : Move := ⟨true,  true,  ⟨2, by decide⟩⟩

def q0TailTables : List PartialMachine := [
  q0Partial m1LC m0LA, q0Partial m1LC m0RA,
  q0Partial m1LC m1LA, q0Partial m1LC m1RA,
  q0Partial m1LC m0LB, q0Partial m1LC m0RB,
  q0Partial m1LC m1LB, q0Partial m1LC m1RB,
  q0Partial m1LC m0LC, q0Partial m1LC m0RC,
  q0Partial m1LC m1LC, q0Partial m1LC m1RC,
  q0Partial m0LC m0LA, q0Partial m0LC m0RA,
  q0Partial m0LC m1LA, q0Partial m0LC m1RA
]

def q0TailSourceIndices : List Nat :=
  [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 152, 153, 154, 155]

def q0TailExpected : List String := [
  "1RB1LC_1RC---_0LA0LA_------_------_------",
  "1RB1LC_1RC---_0LA0RA_------_------_------",
  "1RB1LC_1RC---_0LA1LA_------_------_------",
  "1RB1LC_1RC---_0LA1RA_------_------_------",
  "1RB1LC_1RC---_0LA0LB_------_------_------",
  "1RB1LC_1RC---_0LA0RB_------_------_------",
  "1RB1LC_1RC---_0LA1LB_------_------_------",
  "1RB1LC_1RC---_0LA1RB_------_------_------",
  "1RB1LC_1RC---_0LA0LC_------_------_------",
  "1RB1LC_1RC---_0LA0RC_------_------_------",
  "1RB1LC_1RC---_0LA1LC_------_------_------",
  "1RB1LC_1RC---_0LA1RC_------_------_------",
  "1RB0LC_1RC---_0LA0LA_------_------_------",
  "1RB0LC_1RC---_0LA0RA_------_------_------",
  "1RB0LC_1RC---_0LA1LA_------_------_------",
  "1RB0LC_1RC---_0LA1RA_------_------_------"
]

theorem q0TailEncoding_exact :
    q0TailTables.map encodeTable = q0TailExpected := by
  decide +kernel

theorem q0TailSourceIndices_length :
    q0TailSourceIndices.length = 16 := by decide

def q0NoFrontierTables : List PartialMachine := [
  q0Partial m1LC m0LA,
  q0Partial m1LC m0RA,
  q0Partial m1LC m1RA,
  q0Partial m1LC m0LC,
  q0Partial m1LC m0RC,
  q0Partial m1LC m1LC,
  q0Partial m1LC m1RC,
  q0Partial m0LC m0LA,
  q0Partial m0LC m0RA,
  q0Partial m0LC m1RA
]

def q0CoarseTables : List PartialMachine := [
  q0Partial m1LC m1LA,
  q0Partial m1LC m0LB,
  q0Partial m1LC m0RB,
  q0Partial m1LC m1LB,
  q0Partial m1LC m1RB,
  q0Partial m0LC m1LA
]

/-- A conflict in one of the already named A/B/C source rows. At least one
    conflicting target is also already named, so a permutation of D/E/F
    cannot repair it. -/
def conflictMoves (a b : Move) : Prop :=
  a.write ≠ b.write ∨ a.right ≠ b.right ∨
    ((a.next.val < 3 ∨ b.next.val < 3) ∧ a.next ≠ b.next)

instance (a b : Move) : Decidable (conflictMoves a b) := by
  unfold conflictMoves
  infer_instance

def slotConflict (p q : PartialMachine) (s : Slot) : Prop :=
  match p s, q s with
  | some (some a), some (some b) => conflictMoves a b
  | _, _ => False

instance (p q : PartialMachine) (s : Slot) : Decidable (slotConflict p q s) := by
  unfold slotConflict
  split <;> infer_instance

def rootConflict (p q : PartialMachine) : Prop :=
  ∃ s : Slot, s.1.val < 3 ∧ slotConflict p q s

/-- Constructive witness search; no classical Decidable instance enters kernel checks. -/
instance (p q : PartialMachine) : Decidable (rootConflict p q) := by
  apply decidable_of_iff
    (∃ a : Fin 6, (a.val < 3 ∧ slotConflict p q (a,false)) ∨
                    (a.val < 3 ∧ slotConflict p q (a,true)))
  constructor
  · rintro ⟨a,h⟩
    rcases h with h | h
    · exact ⟨(a,false), h.1, h.2⟩
    · exact ⟨(a,true), h.1, h.2⟩
  · rintro ⟨⟨a,b⟩,ha,hc⟩
    cases b
    · exact ⟨a, Or.inl ⟨ha,hc⟩⟩
    · exact ⟨a, Or.inr ⟨ha,hc⟩⟩

theorem rootConflict_elim {p q : PartialMachine} (h : rootConflict p q) :
    ∃ s : Slot, s.1.val < 3 ∧
      ∃ a b : Move,
        p s = some (some a) ∧ q s = some (some b) ∧ conflictMoves a b := by
  rcases h with ⟨s, hs, hslot⟩
  cases hpSlot : p s with
  | none => simp [slotConflict, hpSlot] at hslot
  | some pt =>
    cases pt with
    | none => simp [slotConflict, hpSlot] at hslot
    | some a =>
      cases hqSlot : q s with
      | none => simp [slotConflict, hpSlot, hqSlot] at hslot
      | some qt =>
        cases qt with
        | none => simp [slotConflict, hpSlot, hqSlot] at hslot
        | some b =>
          refine ⟨s, hs, a, b, hpSlot, hqSlot, ?_⟩
          simpa [slotConflict, hpSlot, hqSlot] using hslot

def raw11FrontierTables : List PartialMachine := frontier.map Prod.snd

def raw11FrontierExpected : List String := [
  "1RB0LB_1RC0LD_0LA---_------_------_------",
  "1RB0LB_1RC0RD_0LA---_------_------_------",
  "1RB0LB_1RC1LB_0LA0LD_------_------_------",
  "1RB0LB_1RC1LB_0LA0RD_------_------_------",
  "1RB0LB_1RC1LB_0LA1LD_------_------_------",
  "1RB0LB_1RC1LB_0LA1RD_------_------_------",
  "1RB0LB_1RC1LC_0LA0LD_------_------_------",
  "1RB0LB_1RC1LC_0LA0RD_------_------_------",
  "1RB0LB_1RC1LC_0LA1LD_------_------_------",
  "1RB0LB_1RC1LC_0LA1RD_------_------_------",
  "1RB0LB_1RC1LD_0LA---_------_------_------",
  "1RB0LB_1RC1RD_0LA---_------_------_------",
  "1RB0LC_1RC---_0LA0LD_------_------_------",
  "1RB0LC_1RC---_0LA0RD_------_------_------",
  "1RB0LC_1RC0LD_0LA1LA_------_------_------",
  "1RB0LC_1RC0RD_0LA1LA_------_------_------",
  "1RB0LC_1RC1LD_0LA1LA_------_------_------",
  "1RB0LC_1RC1RD_0LA1LA_------_------_------",
  "1RB0LC_1RC0LD_0LA1LB_------_------_------",
  "1RB0LC_1RC0RD_0LA1LB_------_------_------",
  "1RB0LC_1RC1LD_0LA1LB_------_------_------",
  "1RB0LC_1RC1RD_0LA1LB_------_------_------",
  "1RB0LC_1RC---_0LA1LD_------_------_------",
  "1RB0LC_1RC---_0LA1RD_------_------_------",
  "1RB0LD_1RC---_0LA---_------_------_------",
  "1RB0RD_1RC---_0LA---_------_------_------",
  "1RB1LA_1RC0LC_0LA0LD_------_------_------",
  "1RB1LA_1RC0LC_0LA0RD_------_------_------",
  "1RB1LA_1RC0LC_0LA1LD_------_------_------",
  "1RB1LA_1RC0LC_0LA1RD_------_------_------",
  "1RB1LA_1RC0LD_0LA---_------_------_------",
  "1RB1LA_1RC0RC_0LA0LD_------_------_------",
  "1RB1LA_1RC0RC_0LA0RD_------_------_------",
  "1RB1LA_1RC0RC_0LA1LD_------_------_------",
  "1RB1LA_1RC0RC_0LA1RD_------_------_------",
  "1RB1LA_1RC0RD_0LA---_------_------_------",
  "1RB1LA_1RC1LB_0LA0LD_------_------_------",
  "1RB1LA_1RC1LB_0LA0RD_------_------_------",
  "1RB1LA_1RC1LB_0LA1LD_------_------_------",
  "1RB1LA_1RC1LB_0LA1RD_------_------_------",
  "1RB1LA_1RC1LC_0LA0LD_------_------_------",
  "1RB1LA_1RC1LC_0LA0RD_------_------_------",
  "1RB1LA_1RC1LC_0LA1LD_------_------_------",
  "1RB1LA_1RC1LC_0LA1RD_------_------_------",
  "1RB1LA_1RC1LD_0LA---_------_------_------",
  "1RB1LA_1RC1RC_0LA0LD_------_------_------",
  "1RB1LA_1RC1RC_0LA0RD_------_------_------",
  "1RB1LA_1RC1RC_0LA1LD_------_------_------",
  "1RB1LA_1RC1RC_0LA1RD_------_------_------",
  "1RB1LA_1RC1RD_0LA---_------_------_------",
  "1RB1LB_1RC0LA_0LA0LD_------_------_------",
  "1RB1LB_1RC0LA_0LA0RD_------_------_------",
  "1RB1LB_1RC0LA_0LA1LD_------_------_------",
  "1RB1LB_1RC0LA_0LA1RD_------_------_------",
  "1RB1LB_1RC0LB_0LA0LD_------_------_------",
  "1RB1LB_1RC0LB_0LA0RD_------_------_------",
  "1RB1LB_1RC0LB_0LA1LD_------_------_------",
  "1RB1LB_1RC0LB_0LA1RD_------_------_------",
  "1RB1LB_1RC0LD_0LA---_------_------_------",
  "1RB1LB_1RC0RA_0LA0LD_------_------_------",
  "1RB1LB_1RC0RA_0LA0RD_------_------_------",
  "1RB1LB_1RC0RA_0LA1LD_------_------_------",
  "1RB1LB_1RC0RA_0LA1RD_------_------_------",
  "1RB1LB_1RC0RB_0LA0LD_------_------_------",
  "1RB1LB_1RC0RB_0LA0RD_------_------_------",
  "1RB1LB_1RC0RB_0LA1LD_------_------_------",
  "1RB1LB_1RC0RB_0LA1RD_------_------_------",
  "1RB1LB_1RC0RC_0LA0LD_------_------_------",
  "1RB1LB_1RC0RC_0LA0RD_------_------_------",
  "1RB1LB_1RC0RC_0LA1LD_------_------_------",
  "1RB1LB_1RC0RC_0LA1RD_------_------_------",
  "1RB1LB_1RC0RD_0LA---_------_------_------",
  "1RB1LB_1RC1LA_0LA0LD_------_------_------",
  "1RB1LB_1RC1LA_0LA0RD_------_------_------",
  "1RB1LB_1RC1LA_0LA1LD_------_------_------",
  "1RB1LB_1RC1LA_0LA1RD_------_------_------",
  "1RB1LB_1RC1LB_0LA0LD_------_------_------",
  "1RB1LB_1RC1LB_0LA0RD_------_------_------",
  "1RB1LB_1RC1LB_0LA1LD_------_------_------",
  "1RB1LB_1RC1LB_0LA1RD_------_------_------",
  "1RB1LB_1RC1LC_0LA0LD_------_------_------",
  "1RB1LB_1RC1LC_0LA0RD_------_------_------",
  "1RB1LB_1RC1LC_0LA1LD_------_------_------",
  "1RB1LB_1RC1LC_0LA1RD_------_------_------",
  "1RB1LB_1RC1LD_0LA---_------_------_------",
  "1RB1LB_1RC1RC_0LA0LD_------_------_------",
  "1RB1LB_1RC1RC_0LA0RD_------_------_------",
  "1RB1LB_1RC1RC_0LA1LD_------_------_------",
  "1RB1LB_1RC1RC_0LA1RD_------_------_------",
  "1RB1LB_1RC1RD_0LA---_------_------_------",
  "1RB1LC_1RC0LD_0LA0LB_------_------_------",
  "1RB1LC_1RC0RD_0LA0LB_------_------_------",
  "1RB1LC_1RC1LD_0LA0LB_------_------_------",
  "1RB1LC_1RC1RD_0LA0LB_------_------_------",
  "1RB1LC_1RC---_0LA0LD_------_------_------",
  "1RB1LC_1RC0LD_0LA0RB_------_------_------",
  "1RB1LC_1RC0RD_0LA0RB_------_------_------",
  "1RB1LC_1RC1LD_0LA0RB_------_------_------",
  "1RB1LC_1RC1RD_0LA0RB_------_------_------",
  "1RB1LC_1RC---_0LA0RD_------_------_------",
  "1RB1LC_1RC0LD_0LA1LA_------_------_------",
  "1RB1LC_1RC0RD_0LA1LA_------_------_------",
  "1RB1LC_1RC1LD_0LA1LA_------_------_------",
  "1RB1LC_1RC1RD_0LA1LA_------_------_------",
  "1RB1LC_1RC0LD_0LA1LB_------_------_------",
  "1RB1LC_1RC0RD_0LA1LB_------_------_------",
  "1RB1LC_1RC1LD_0LA1LB_------_------_------",
  "1RB1LC_1RC1RD_0LA1LB_------_------_------",
  "1RB1LC_1RC---_0LA1LD_------_------_------",
  "1RB1LC_1RC0LD_0LA1RB_------_------_------",
  "1RB1LC_1RC0RD_0LA1RB_------_------_------",
  "1RB1LC_1RC1LD_0LA1RB_------_------_------",
  "1RB1LC_1RC1RD_0LA1RB_------_------_------",
  "1RB1LC_1RC---_0LA1RD_------_------_------",
  "1RB1LD_1RC---_0LA---_------_------_------",
  "1RB1RD_1RC---_0LA---_------_------_------"
]

/-- The original frontier enumeration has a different order than the
    historical JSON export.  Record the discrepancy without assuming an
    invalid pointwise identity. -/
#eval (raw11FrontierTables.map encodeTable == raw11FrontierExpected)

/-- Order-independent certification of the exact first-D source frontier
    against the saved table manifest.  Sorted equality retains multiplicities
    and can be used safely to transport finite membership facts. -/
theorem raw11FrontierManifest_multiset_exact :
    (raw11FrontierTables.map encodeTable).mergeSort =
      raw11FrontierExpected.mergeSort := by
  decide +kernel

theorem raw11FrontierTables_length :
    raw11FrontierTables.length = 116 := by
  simpa [raw11FrontierTables] using frontier_count

def extendsParentCheck : Bool :=
  q0TailTables.all (fun p => decide (extendsTable parent p))

theorem extendsParentCheck_ok : extendsParentCheck = true := by
  decide +kernel

def frontierExtendsParentCheck : Bool :=
  raw11FrontierTables.all (fun p => decide (extendsTable parent p))

theorem frontierExtendsParentCheck_ok :
    frontierExtendsParentCheck = true := by
  decide +kernel

theorem q0Tail_extends_parent {p : PartialMachine} (hp : p ∈ q0TailTables) :
    extendsTable parent p := by
  have h := List.all_eq_true.mp
    (show q0TailTables.all (fun p => decide (extendsTable parent p)) = true
      from extendsParentCheck_ok) p hp
  exact of_decide_eq_true h

theorem frontier_extends_parent {e : List Move × PartialMachine}
    (he : e ∈ frontier) : extendsTable parent e.2 := by
  have hmem : e.2 ∈ raw11FrontierTables :=
    List.mem_map.mpr ⟨e, he, rfl⟩
  have h := List.all_eq_true.mp
    (show raw11FrontierTables.all (fun p => decide (extendsTable parent p)) = true
      from frontierExtendsParentCheck_ok) e.2 hmem
  exact of_decide_eq_true h

def q0NoFrontierExtendsParentCheck : Bool :=
  q0NoFrontierTables.all (fun p => decide (extendsTable parent p))

theorem q0NoFrontierExtendsParentCheck_ok :
    q0NoFrontierExtendsParentCheck = true := by decide +kernel

theorem q0NoFrontier_extends_parent {p : PartialMachine}
    (hp : p ∈ q0NoFrontierTables) : extendsTable parent p := by
  have h := List.all_eq_true.mp q0NoFrontierExtendsParentCheck_ok p hp
  exact of_decide_eq_true h

def q0CoarseExtendsParentCheck : Bool :=
  q0CoarseTables.all (fun p => decide (extendsTable parent p))

theorem q0CoarseExtendsParentCheck_ok :
    q0CoarseExtendsParentCheck = true := by decide +kernel

theorem q0Coarse_extends_parent {p : PartialMachine}
    (hp : p ∈ q0CoarseTables) : extendsTable parent p := by
  have h := List.all_eq_true.mp q0CoarseExtendsParentCheck_ok p hp
  exact of_decide_eq_true h

/-- The 10 unmatched q0 rows conflict with every one of the 116 Raw11
    first-D residuals at a fixed A/B/C transition. -/
def q0NoFrontierConflictCheck : Bool :=
  q0NoFrontierTables.all (fun p =>
    raw11FrontierTables.all (fun q => decide (rootConflict p q)))

theorem q0NoFrontierConflictCheck_ok :
    q0NoFrontierConflictCheck = true := by decide +kernel

theorem q0NoFrontier_conflict {p : PartialMachine}
    (hp : p ∈ q0NoFrontierTables)
    {e : List Move × PartialMachine} (he : e ∈ frontier) :
    rootConflict p e.2 := by
  have hpCheck := List.all_eq_true.mp
    (show q0NoFrontierTables.all
      (fun p => raw11FrontierTables.all (fun q => decide (rootConflict p q))) = true
      from q0NoFrontierConflictCheck_ok) p hp
  have hmem : e.2 ∈ raw11FrontierTables :=
    List.mem_map.mpr ⟨e, he, rfl⟩
  have heCheck := List.all_eq_true.mp hpCheck e.2 hmem
  exact of_decide_eq_true heCheck

/-- Extract the original transition underlying a renamed transition. -/
theorem renameTable_slot_inv (e : StatePerm) (m : Machine) (s : Slot)
    (mv : Move) (h : renameTable e m s = some mv) :
    ∃ t : Move,
      m (e.backward s.1, s.2) = some t ∧
      t.write = mv.write ∧ t.right = mv.right ∧ e.forward t.next = mv.next := by
  unfold renameTable at h
  cases hm : m (e.backward s.1, s.2) with
  | none =>
      simp [hm] at h
  | some t =>
      have ht : renameMove e t = mv := by simpa [hm] using h
      cases t with
      | mk w r n =>
          cases mv with
          | mk w' r' n' =>
              simp [renameMove] at ht
              rcases ht with ⟨rfl, rfl, rfl⟩
              exact ⟨⟨w, r, n⟩, rfl, rfl, rfl, rfl⟩

/-- Any two TNF witnesses for this Raw11 parent agree on the original states
    corresponding to A, B, and C. The A0 and B0 edges force those images. -/
theorem rootBackwardAgreement (m : Machine) (e f : StatePerm)
    (he0 : e.forward 0 = 0) (hf0 : f.forward 0 = 0)
    (hpe : compatible parent (renameTable e m))
    (hpf : compatible parent (renameTable f m)) :
    e.backward 0 = f.backward 0 ∧
    e.backward 1 = f.backward 1 ∧
    e.backward 2 = f.backward 2 := by
  have he0b : e.backward (0 : Fin 6) = 0 := by
    simpa [he0] using e.leftInverse (0 : Fin 6)
  have hf0b : f.backward (0 : Fin 6) = 0 := by
    simpa [hf0] using f.leftInverse (0 : Fin 6)

  have hA_e : renameTable e m (0, false) = some (⟨true, true, 1⟩ : Move) :=
    hpe (0, false) (some (⟨true, true, 1⟩ : Move)) (by simp [parent])
  have hA_f : renameTable f m (0, false) = some (⟨true, true, 1⟩ : Move) :=
    hpf (0, false) (some (⟨true, true, 1⟩ : Move)) (by simp [parent])
  obtain ⟨ta, hta, _, _, hna⟩ :=
    renameTable_slot_inv e m (0, false) ⟨true, true, 1⟩ hA_e
  obtain ⟨tb, htb, _, _, hnb⟩ :=
    renameTable_slot_inv f m (0, false) ⟨true, true, 1⟩ hA_f
  have hrowA : some ta = some tb := by
    calc
      some ta = m (e.backward 0, false) := hta.symm
      _ = m (f.backward 0, false) := by rw [he0b, hf0b]
      _ = some tb := htb
  have hmoveA : ta = tb := Option.some.inj hrowA
  have he1 : e.backward 1 = ta.next := by
    calc
      e.backward 1 = e.backward (e.forward ta.next) := by rw [hna]
      _ = ta.next := e.leftInverse ta.next
  have hf1 : f.backward 1 = tb.next := by
    calc
      f.backward 1 = f.backward (f.forward tb.next) := by rw [hnb]
      _ = tb.next := f.leftInverse tb.next
  have h1 : e.backward 1 = f.backward 1 := by
    calc
      e.backward 1 = ta.next := he1
      _ = tb.next := by rw [hmoveA]
      _ = f.backward 1 := hf1.symm

  have hB_e : renameTable e m (1, false) = some (⟨true, true, 2⟩ : Move) :=
    hpe (1, false) (some (⟨true, true, 2⟩ : Move)) (by simp [parent])
  have hB_f : renameTable f m (1, false) = some (⟨true, true, 2⟩ : Move) :=
    hpf (1, false) (some (⟨true, true, 2⟩ : Move)) (by simp [parent])
  obtain ⟨tbe, htbe, _, _, hnbe⟩ :=
    renameTable_slot_inv e m (1, false) ⟨true, true, 2⟩ hB_e
  obtain ⟨tbf, htbf, _, _, hnbf⟩ :=
    renameTable_slot_inv f m (1, false) ⟨true, true, 2⟩ hB_f
  have hrowB : some tbe = some tbf := by
    calc
      some tbe = m (e.backward 1, false) := htbe.symm
      _ = m (f.backward 1, false) := by rw [h1]
      _ = some tbf := htbf
  have hmoveB : tbe = tbf := Option.some.inj hrowB
  have he2 : e.backward 2 = tbe.next := by
    calc
      e.backward 2 = e.backward (e.forward tbe.next) := by rw [hnbe]
      _ = tbe.next := e.leftInverse tbe.next
  have hf2 : f.backward 2 = tbf.next := by
    calc
      f.backward 2 = f.backward (f.forward tbf.next) := by rw [hnbf]
      _ = tbf.next := f.leftInverse tbf.next
  have h2 : e.backward 2 = f.backward 2 := by
    calc
      e.backward 2 = tbe.next := he2
      _ = tbf.next := by rw [hmoveB]
      _ = f.backward 2 := hf2.symm

  exact ⟨by rw [he0b, hf0b], h1, h2⟩

/-- A conflict at A/B/C which touches an already named target excludes
    simultaneous quotient compatibility, even if the two TNF witnesses
    initially appear to differ by a permutation of unused states. -/
theorem no_common_quotient_of_rootConflict {p q : PartialMachine}
    (hp : extendsTable parent p) (hq : extendsTable parent q)
    (hconf : rootConflict p q) :
    ¬ ∃ m : Machine, TNFQuotientCompatible p m ∧ TNFQuotientCompatible q m := by
  rintro ⟨m, hpm, hqm⟩
  rcases hpm with ⟨e, he0, hpe⟩
  rcases hqm with ⟨f, hf0, hpf⟩
  have hpeParent : compatible parent (renameTable e m) := by
    intro s t hs
    exact hpe s t (extendsTable_compat hp s t hs)
  have hpfParent : compatible parent (renameTable f m) := by
    intro s t hs
    exact hpf s t (extendsTable_compat hq s t hs)
  obtain ⟨hback0, hback1, hback2⟩ :=
    rootBackwardAgreement m e f he0 hf0 hpeParent hpfParent

  rcases rootConflict_elim hconf with ⟨s, hs, a, b, hpa, hqb, hdiff⟩
  have hsrc : e.backward s.1 = f.backward s.1 := by
    have hv : s.1.val = 0 ∨ s.1.val = 1 ∨ s.1.val = 2 := by omega
    rcases hv with hv | hv | hv
    · have hi : s.1 = (0 : Fin 6) := Fin.ext hv
      simpa [hi] using hback0
    · have hi : s.1 = (1 : Fin 6) := Fin.ext hv
      simpa [hi] using hback1
    · have hi : s.1 = (2 : Fin 6) := Fin.ext hv
      simpa [hi] using hback2

  have hrowp : renameTable e m s = some a := hpe s (some a) hpa
  have hrowq : renameTable f m s = some b := hpf s (some b) hqb
  obtain ⟨ta, hta, hwa, hra, hna⟩ := renameTable_slot_inv e m s a hrowp
  obtain ⟨tb, htb, hwb, hrb, hnb⟩ := renameTable_slot_inv f m s b hrowq
  have hsame : ta = tb := by
    apply Option.some.inj
    calc
      some ta = m (e.backward s.1, s.2) := hta.symm
      _ = m (f.backward s.1, s.2) := by rw [hsrc]
      _ = some tb := htb

  rcases hdiff with hwrite | hright | ⟨hsmall, hneq⟩
  · apply hwrite
    calc
      a.write = ta.write := hwa.symm
      _ = tb.write := by rw [hsame]
      _ = b.write := hwb
  · apply hright
    calc
      a.right = ta.right := hra.symm
      _ = tb.right := by rw [hsame]
      _ = b.right := hrb
  · have hnextEq : ta.next = tb.next := by rw [hsame]
    have htarget : e.backward a.next = f.backward b.next := by
      calc
        e.backward a.next = e.backward (e.forward ta.next) := by rw [hna]
        _ = ta.next := e.leftInverse ta.next
        _ = tb.next := hnextEq
        _ = f.backward (f.forward tb.next) := (f.leftInverse tb.next).symm
        _ = f.backward b.next := by rw [hnb]
    by_cases haSmall : a.next.val < 3
    · have hbacka : e.backward a.next = f.backward a.next := by
        have hv : a.next.val = 0 ∨ a.next.val = 1 ∨ a.next.val = 2 := by omega
        rcases hv with hv | hv | hv
        · have hi : a.next = (0 : Fin 6) := Fin.ext hv
          simpa [hi] using hback0
        · have hi : a.next = (1 : Fin 6) := Fin.ext hv
          simpa [hi] using hback1
        · have hi : a.next = (2 : Fin 6) := Fin.ext hv
          simpa [hi] using hback2
      have hsameBack : f.backward a.next = f.backward b.next := by
        calc
          f.backward a.next = e.backward a.next := hbacka.symm
          _ = f.backward b.next := htarget
      have hEq : a.next = b.next := by
        have h := congrArg f.forward hsameBack
        simpa [f.rightInverse] using h
      exact hneq hEq
    · have hbSmall : b.next.val < 3 := by omega
      have hbackb : e.backward b.next = f.backward b.next := by
        have hv : b.next.val = 0 ∨ b.next.val = 1 ∨ b.next.val = 2 := by omega
        rcases hv with hv | hv | hv
        · have hi : b.next = (0 : Fin 6) := Fin.ext hv
          simpa [hi] using hback0
        · have hi : b.next = (1 : Fin 6) := Fin.ext hv
          simpa [hi] using hback1
        · have hi : b.next = (2 : Fin 6) := Fin.ext hv
          simpa [hi] using hback2
      have hsameBack : e.backward a.next = e.backward b.next := by
        calc
          e.backward a.next = f.backward b.next := htarget
          _ = e.backward b.next := hbackb.symm
      have hEq : a.next = b.next := by
        have h := congrArg e.forward hsameBack
        simpa [e.rightInverse] using h
      exact hneq hEq

/-- The 10 q0 checkpoint rows with no first-D overlap are fully discharged
    by the Raw11 low-bound branch. -/
theorem q0NoFrontier_safe {p : PartialMachine}
    (hp : p ∈ q0NoFrontierTables) (m : Machine)
    (hm : TNFQuotientCompatible p m) : WeightedBound bound m := by
  have hpExt := q0NoFrontier_extends_parent hp
  rcases hm with ⟨e, he0, hpm⟩
  have hOriginal : TNFQuotientCompatible p m := ⟨e, he0, hpm⟩
  have hparent : compatible parent (renameTable e m) := by
    intro s t hs
    exact hpm s t (extendsTable_compat hpExt s t hs)
  have htnf : TNFQuotientCompatible parent m := ⟨e, he0, hparent⟩
  rcases partition m htnf with hsafe | ⟨entry, hentry, hentryTnf⟩
  · exact hsafe
  · exact False.elim
      (no_common_quotient_of_rootConflict hpExt
        (frontier_extends_parent hentry)
        (q0NoFrontier_conflict hp hentry)
        ⟨m, hOriginal, hentryTnf⟩)

/-- The six remaining q0 checkpoint rows retain exactly their compatible
    first-D frontier entries. The finite match-list theorem below identifies
    each retained set as four entries. -/
theorem q0Coarse_restricted_partition {p : PartialMachine}
    (hp : p ∈ q0CoarseTables) (m : Machine)
    (hm : TNFQuotientCompatible p m) :
    WeightedBound bound m ∨
      ∃ entry ∈ frontier,
        ¬ rootConflict p entry.2 ∧ TNFQuotientCompatible entry.2 m := by
  have hpExt := q0Coarse_extends_parent hp
  rcases hm with ⟨e, he0, hpm⟩
  have hOriginal : TNFQuotientCompatible p m := ⟨e, he0, hpm⟩
  have hparent : compatible parent (renameTable e m) := by
    intro s t hs
    exact hpm s t (extendsTable_compat hpExt s t hs)
  have htnf : TNFQuotientCompatible parent m := ⟨e, he0, hparent⟩
  rcases partition m htnf with hsafe | ⟨entry, hentry, hentryTnf⟩
  · exact Or.inl hsafe
  · by_cases hconf : rootConflict p entry.2
    · exact False.elim
        (no_common_quotient_of_rootConflict hpExt
          (frontier_extends_parent hentry) hconf
          ⟨m, hOriginal, hentryTnf⟩)
    · exact Or.inr ⟨entry, hentry, hconf, hentryTnf⟩

def frontierConflictFreeIndices (p : PartialMachine) : List Nat :=
  (List.range 116).filter (fun i =>
    decide (¬ rootConflict p (raw11FrontierTables.getD i (fun _ => none))))

/-- Every coarse q0 row retains exactly four of the actual source-computed
    first-D frontier entries; their indices need not follow the old JSON order. -/
theorem q0CoarseMatches_cardinalities :
    (q0CoarseTables.map frontierConflictFreeIndices).map List.length =
      [4, 4, 4, 4, 4, 4] := by
  decide +kernel

#print axioms q0NoFrontier_safe
#print axioms q0Coarse_restricted_partition

end BB6.Agent24Raw11Q0Graft
