import F412Partition

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412DeepHalt
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent26F412Graft

/-- Fill B1 at depth eight; the only remaining undefined row is E1. -/
def pB1 (mv : Move) : PartialMachine := fChild (8 : Fin 9) mv

theorem pB1_other_slots (mv : Move) (slot : Slot) (hs : slot ≠ (4,true)) :
    ∃ u, pB1 mv slot = some (some u) := by
  by_cases hb : slot = (1,true)
  · subst slot
    exact ⟨mv, by simp [pB1, fChild, fParent, fHole, refine]⟩
  · obtain ⟨u,hu⟩ := fFinalOtherSlots slot hs
    refine ⟨u, ?_⟩
    have hu8 : fP8 slot = some (some u) := by
      simpa [fP9, refine, hb] using hu
    simpa [pB1, fChild, fParent, fHole, refine, hb] using hu8

theorem pB1_root (mv : Move) :
    pB1 mv initialSlot = some (some ⟨true,true,1⟩) := by
  simp [pB1, fChild, fParent, fHole, refine, fP8, fP7, fP6, fP5,
    fP4, fP3, fP2, fP1, fResidual, fRoot, initialSlot]

theorem pB1_E1_unknown (mv : Move) : pB1 mv (4,true) = none := by
  simp [pB1, fChild, fParent, fHole, refine, fP8, fP7, fP6,
    fP5, fP4, fP3, fP2, fP1, fResidual, fRoot, emptyTable]

/-- A finite 30-step first-hole certificate suffices for every ordinary
    or halting completion. Ordinary completions are total and have no
    halting rows, so no infinite-run search or macro analysis is needed. -/
theorem short_last_hole (B : Nat) (hB : 37 ≤ B)
    (mv : Move) (n : Nat) (hn : n ≤ 30)
    (hknown : knownRun (pB1 mv) n =
      some ((knownRun (pB1 mv) n).getD blank))
    (hslot : readSlot ((knownRun (pB1 mv) n).getD blank) = (4,true)) :
    ∀ m, compatible (pB1 mv) m → WeightedBound B m := by
  let c : Config := (knownRun (pB1 mv) n).getD blank
  have hr : knownRun (pB1 mv) n = some c := hknown
  have hu : pB1 mv (readSlot c) = none := by
    rw [hslot]
    exact pB1_E1_unknown mv
  apply last_hole_sound B (pB1 mv) n c (pB1_root mv) hr hu
  · intro slot hs
    exact pB1_other_slots mv slot (by simpa only [hslot] using hs)
  · intro d hd
    have hd6 : d < 6 := by
      unfold possibleDelays at hd
      exact List.mem_range.mp (List.mem_filter.mp hd).1
    omega

/-- B1=0RE reaches its final E1 hole after 15 ordinary moves. -/
theorem B1_0RE_sound (B : Nat) (hB : 37 ≤ B) :
    ∀ m, compatible (pB1 ⟨false,true,4⟩) m → WeightedBound B m :=
  short_last_hole B hB ⟨false,true,4⟩ 15 (by decide) (by decide) (by decide)

/-- B1=1LD reaches E1 after 16 ordinary moves. -/
theorem B1_1LD_sound (B : Nat) (hB : 37 ≤ B) :
    ∀ m, compatible (pB1 ⟨true,false,3⟩) m → WeightedBound B m :=
  short_last_hole B hB ⟨true,false,3⟩ 16 (by decide) (by decide) (by decide)

/-- B1=1LE reaches E1 after 30 ordinary moves. -/
theorem B1_1LE_sound (B : Nat) (hB : 37 ≤ B) :
    ∀ m, compatible (pB1 ⟨true,false,4⟩) m → WeightedBound B m :=
  short_last_hole B hB ⟨true,false,4⟩ 30 (by decide) (by decide) (by decide)

/-- B1=1RE reaches E1 after 15 ordinary moves. -/
theorem B1_1RE_sound (B : Nat) (hB : 37 ≤ B) :
    ∀ m, compatible (pB1 ⟨true,true,4⟩) m → WeightedBound B m :=
  short_last_hole B hB ⟨true,true,4⟩ 15 (by decide) (by decide) (by decide)

#print axioms B1_0RE_sound
#print axioms B1_1LD_sound
#print axioms B1_1LE_sound
#print axioms B1_1RE_sound
end BB6.Agent26F412DeepHalt
