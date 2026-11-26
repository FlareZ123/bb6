import F412Partition
import Raw10BoxCombinedConsumer

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412Graft
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent49Box BB6.Agent49BoxBridge BB6.Agent17Raw10CombinedConsumer

def fHaltChild (i : Fin 9) : PartialMachine :=
  refine (fParent i) (fHole i) none

theorem fHaltChild_sound (B : Nat) (hB : 20 ≤ B) (i : Fin 9)
    (m : Machine) (hm : compatible (fHaltChild i) m) :
    WeightedBound B m := by
  have hu : fParent i (readSlot (fConfig i)) = none := by
    rw [fReadSlot i]
    exact fHoleProof i
  apply first_hole_weighted_halt B (fParent i) (fRunLength i)
    (fConfig i) (fParentInitialSlot i) (fRunKnown i) hu
  · intro d hd
    have hd6 : d < 6 := by
      unfold possibleDelays at hd
      exact List.mem_range.mp (List.mem_filter.mp hd).1
    have hn := fRunLength_le14 i
    omega
  · rw [fReadSlot i]
    exact hm

def fSideTables : List PartialMachine :=
  fWitnesses.map fun w => fChild w.depth w.child

def fEarlyHaltTables : List PartialMachine :=
  (List.finRange 9).map fHaltChild

/-- All new certificates with no dependence on the long exact clock. -/
def fShortTables : List PartialMachine := fSideTables ++ fEarlyHaltTables

theorem fShortTables_sound (B : Nat) (hB : 20 ≤ B)
    (p : PartialMachine) (hp : p ∈ fShortTables)
    (m : Machine) (hm : compatible p m) : WeightedBound B m := by
  rcases List.mem_append.mp hp with hs | hh
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hs
    have hc : fClosed w.depth w.child = true := by
      unfold fClosed
      exact List.any_eq_true.mpr ⟨w,hw,by simp⟩
    exact weighted_never B m (fClosed_sound w.depth w.child hc m hm)
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hh
    exact fHaltChild_sound B hB i m hm

/-- Add the final one-hole cylinder only after the exact clock is available. -/
def fAllCertifiedTables : List PartialMachine := fShortTables ++ [fP9]

theorem fAllCertifiedTables_sound (B : Nat) (hB : fMoves+1 ≤ B)
    (hclock : HaltsAfter fLiteral fMoves)
    (p : PartialMachine) (hp : p ∈ fAllCertifiedTables)
    (m : Machine) (hm : compatible p m) : WeightedBound B m := by
  rcases List.mem_append.mp hp with hs | hf
  · have h20 : 20 ≤ B := by unfold fMoves at hB; omega
    exact fShortTables_sound B h20 p hs m hm
  · have he : p = fP9 := by simpa using hf
    subst p
    exact fFinalSound B hB hclock m hm

/-- Subtract an arbitrary list of partial-machine cylinders from an existing
    exact box partition. No re-enumeration of complete tables. -/
def graftBoxes (rs : List (Box Slot Transition)) (ps : List PartialMachine) :
    List (Box Slot Transition) :=
  subtractMany slots rs (ps.map cubeOf)

theorem graftBoxes_exact (rs : List (Box Slot Transition))
    (ps : List PartialMachine) (m : Machine) :
    (∃ r ∈ graftBoxes rs ps, Fits r m) ↔
      (∃ r ∈ rs, Fits r m) ∧ ∀ p ∈ ps, ¬ compatible p m := by
  rw [graftBoxes, subtractMany_exact]
  constructor
  · rintro ⟨hr,hn⟩
    exact ⟨hr, fun p hp hc =>
      hn (cubeOf p) (List.mem_map.mpr ⟨p,hp,rfl⟩) ((matches_cubeOf p m).mpr hc)⟩
  · rintro ⟨hr,hn⟩
    refine ⟨hr, ?_⟩
    intro c hc hmatch
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    exact hn p hp ((matches_cubeOf p m).mp hmatch)

theorem graftBoxes_disjoint (rs : List (Box Slot Transition))
    (ps : List PartialMachine) (hd : rs.Pairwise Disjoint) :
    (graftBoxes rs ps).Pairwise Disjoint :=
  subtractMany_disjoint slots _ _ hd

theorem graftBoxes_consume (B : Nat) (rs : List (Box Slot Transition))
    (ps : List PartialMachine)
    (hcert : ∀ p ∈ ps, ∀ m, compatible p m → WeightedBound B m)
    (hopen : ∀ r ∈ graftBoxes rs ps, ∀ m, Fits r m → WeightedBound B m) :
    ∀ r ∈ rs, ∀ m, Fits r m → WeightedBound B m := by
  intro r hr m hm
  classical
  by_cases h : ∃ p ∈ ps, compatible p m
  · obtain ⟨p,hp,hc⟩ := h
    exact hcert p hp m hc
  · obtain ⟨r',hr',hm'⟩ := (graftBoxes_exact rs ps m).mpr
      ⟨⟨r,hr,hm⟩, fun p hp hc => h ⟨p,hp,hc⟩⟩
    exact hopen r' hr' m hm'

/-- The new raw10 partition can consume all short certificates immediately,
    independently of the pending F412 clock audit. -/
def raw10ShortRemainder : List (Box Slot Transition) :=
  graftBoxes raw10RemainderWithCycleAndHalt fShortTables

def raw10FullF412Remainder : List (Box Slot Transition) :=
  graftBoxes raw10RemainderWithCycleAndHalt fAllCertifiedTables

theorem raw10ShortRemainder_disjoint : raw10ShortRemainder.Pairwise Disjoint :=
  graftBoxes_disjoint _ _ raw10RemainderWithCycleAndHalt_disjoint

theorem raw10FullF412Remainder_disjoint : raw10FullF412Remainder.Pairwise Disjoint :=
  graftBoxes_disjoint _ _ raw10RemainderWithCycleAndHalt_disjoint

def raw10CoverWithF412Short (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10ShortRemainder, ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent50RootFrontier.firstOneB0_1LC :=
  raw10CoverWithCycleAndHalt B hB hHeld
    (graftBoxes_consume B _ _ (fShortTables_sound B (by omega)) hOpen)

def raw10CoverWithF412Full (B : Nat) (hB : fMoves+1 ≤ B)
    (hclock : HaltsAfter fLiteral fMoves)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10FullF412Remainder, ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent50RootFrontier.firstOneB0_1LC :=
  raw10CoverWithCycleAndHalt B (by unfold fMoves at hB; omega) hHeld
    (graftBoxes_consume B _ _ (fAllCertifiedTables_sound B hB hclock) hOpen)

#print axioms fShortTables_sound
#print axioms graftBoxes_exact
#print axioms graftBoxes_disjoint
#print axioms raw10CoverWithF412Short
#print axioms raw10CoverWithF412Full

end BB6.Agent26F412Graft
