import Raw10BoxCombinedConsumer

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw10HardRootR1Adapter

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent49Box
open BB6.Agent49BoxBridge
open BB6.Agent17Raw10CombinedConsumer

/-- The literal first Cryptids608 nonhalting root, in A0,A1,...,F1 order. -/
def r1 : Machine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some ⟨true,true,1⟩
  | 0, true  => some ⟨false,false,2⟩
  | 1, false => some ⟨true,false,2⟩
  | 1, true  => some ⟨false,true,1⟩
  | 2, false => some ⟨false,false,4⟩
  | 2, true  => some ⟨false,false,3⟩
  | 3, false => some ⟨true,false,2⟩
  | 3, true  => none
  | 4, false => some ⟨false,true,0⟩
  | 4, true  => some ⟨true,false,5⟩
  | 5, false => some ⟨true,false,0⟩
  | 5, true  => some ⟨true,false,5⟩
  | _, _ => none

def r1Hole : Slot := (⟨3, by decide⟩, true)

/-- Erase the unique halt row, leaving a one-hole cylinder. -/
def eraseHalt (m : Machine) (s : Slot) : PartialMachine :=
  fun t => if t = s then none else some (m t)

/-- Generic exact adapter: if the sole halt completion is nonhalting, then
    every completion of its one-hole cylinder is nonhalting. The 24 ordinary
    replacements are handled by totality, not by a simulation. -/
theorem oneHaltLeafCover (B : Nat) (m : Machine) (s : Slot)
    (hHalt : m s = none)
    (hOrdinary : ∀ t, t ≠ s → ∃ mv, m t = some mv)
    (hNever : NeverHalts m) :
    Cover (WeightedBound B) (eraseHalt m s) := by
  refine Cover.leaf (eraseHalt m s) ?_
  intro n hn
  by_cases hns : n s = none
  · have hEq : n = m := by
      funext t
      by_cases ht : t = s
      · subst t
        simpa [hHalt] using hns
      · obtain ⟨mv, hmv⟩ := hOrdinary t ht
        have hcomp := hn t (some mv) (by simp [eraseHalt, ht, hmv])
        exact hcomp.trans hmv.symm
    exact weighted_never B n (hEq.symm ▸ hNever)
  · apply weighted_never B n
    apply all_ordinary_never n
    intro t
    by_cases ht : t = s
    · subst t
      cases hnt : n s with
      | none => exact False.elim (hns hnt)
      | some mv => exact ⟨mv, hnt⟩
    · obtain ⟨mv, hmv⟩ := hOrdinary t ht
      have hcomp := hn t (some mv) (by simp [eraseHalt, ht, hmv])
      exact ⟨mv, hcomp⟩

theorem r1_halt : r1 r1Hole = none := by decide

theorem r1_other_rows_ordinary :
    ∀ t, t ≠ r1Hole → ∃ mv, r1 t = some mv := by
  decide

def r1Leaf : PartialMachine := eraseHalt r1 r1Hole

theorem r1LeafCoverOfNever (B : Nat) (hNever : NeverHalts r1) :
    Cover (WeightedBound B) r1Leaf :=
  oneHaltLeafCover B r1 r1Hole r1_halt r1_other_rows_ordinary hNever

/-- Test that a partial cylinder is wholly contained in a product box:
    fixed rows must be admitted, and every hole must retain all 25 choices. -/
def boxContainsPartial (b : Box Slot Transition) (p : PartialMachine) : Bool :=
  slots.all fun s =>
    match p s with
    | none => decide (b s = transitions)
    | some t => decide (t ∈ b s)

theorem boxContainsPartial_sound {b : Box Slot Transition} {p : PartialMachine}
    (h : boxContainsPartial b p = true) :
    ∀ m, compatible p m → Fits b m := by
  intro m hm s
  have hs := (List.all_eq_true.mp h) s (slots_complete s)
  cases hp : p s with
  | none =>
    have hdom : b s = transitions := of_decide_eq_true hs
    rw [hdom]
    exact transitions_complete (m s)
  | some t =>
    have hmem : t ∈ b s := of_decide_eq_true hs
    have hvalue : m s = t := hm s t hp
    simpa [hvalue] using hmem

/-- The unique current residual rectangle containing the complete r1 leaf. -/
def r1Box24 : Box Slot Transition :=
  List.get raw10RemainderWithCycleAndHalt ⟨24, by decide⟩

theorem r1Box24_mem :
    r1Box24 ∈ raw10RemainderWithCycleAndHalt := by
  simp [r1Box24]

theorem r1Leaf_box24_contains :
    boxContainsPartial r1Box24 r1Leaf = true := by
  decide

theorem r1Leaf_fits_box24 :
    ∀ m, compatible r1Leaf m → Fits r1Box24 m :=
  boxContainsPartial_sound r1Leaf_box24_contains

/-- The entire r1 one-hole leaf is inside the B0=1LC parent and in its exact
    residual box 24, not merely the single completed root table. -/
theorem r1Leaf_parent (m : Machine) (hm : compatible r1Leaf m) :
    compatible firstOneB0_1LC m := by
  have hres := (raw10RemainderWithCycleAndHalt_exact m).mp
    ⟨r1Box24, r1Box24_mem, r1Leaf_fits_box24 m hm⟩
  exact hres.1

/-- A stronger B0=1LC consumer: box 24 is split logically into the already
    source-certifiable r1 leaf and its still-open complement. All other 40
    residual boxes retain their original obligations. Supplying
    Cryptids608.literal_r1_never as hNever discharges the r1 branch. -/
theorem raw10CoverWithR1 (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hNever : NeverHalts r1)
    (hOpen : ∀ r ∈ raw10RemainderWithCycleAndHalt,
      ∀ m, Fits r m →
        (r = r1Box24 → ¬ compatible r1Leaf m) → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  raw10CoverWithCycleAndHalt B hB hHeld
    (fun r hr m hm => by
      by_cases hbox : r = r1Box24
      · by_cases hleaf : compatible r1Leaf m
        · exact (r1LeafCoverOfNever B hNever).sound m hleaf
        · exact hOpen r hr m hm (by intro heq; subst r; exact hleaf)
      · exact hOpen r hr m hm (by intro heq; exact hbox heq))

#print axioms oneHaltLeafCover
#print axioms r1LeafCoverOfNever
#print axioms r1Leaf_box24_contains
#print axioms r1Leaf_fits_box24
#print axioms r1Leaf_parent
#print axioms raw10CoverWithR1

end BB6.Agent50Raw10HardRootR1Adapter
