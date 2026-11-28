import F412Partition

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412TwoHole
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent26F412Graft

/-- Arbitrary alternative at F0, followed by either of the two remaining
    holes (B1/E1). The second refinement leaves exactly one hole. -/
def pF0 (fm : Move) : PartialMachine := fChild (7 : Fin 9) fm
def pF0B1 (fm bm : Move) : PartialMachine :=
  refine (pF0 fm) (1,true) (some bm)
def pF0E1 (fm em : Move) : PartialMachine :=
  refine (pF0 fm) (4,true) (some em)

/-- The nine F412 instructions before F0 are total ordinary rows. -/
theorem pF7_assigned (slot : Slot)
    (hF : slot ≠ (5,false)) (hB : slot ≠ (1,true))
    (hE : slot ≠ (4,true)) :
    ∃ mv, fP7 slot = some (some mv) := by
  obtain ⟨mv,hv⟩ := fFinalOtherSlots slot hE
  refine ⟨mv, ?_⟩
  simpa [fP9, fP8, refine, hB, hF] using hv

theorem pF0B1_rest (fm bm : Move) (slot : Slot) (hs : slot ≠ (4,true)) :
    ∃ mv, pF0B1 fm bm slot = some (some mv) := by
  by_cases hF : slot = (5,false)
  · subst slot
    exact ⟨fm, by simp [pF0B1,pF0,fChild,fParent,fHole,refine]⟩
  · by_cases hB : slot = (1,true)
    · subst slot
      exact ⟨bm, by simp [pF0B1,pF0,fChild,fParent,fHole,refine]⟩
    · obtain ⟨mv,hv⟩ := pF7_assigned slot hF hB hs
      refine ⟨mv, ?_⟩
      simpa [pF0B1,pF0,fChild,fParent,fHole,refine,hF,hB] using hv

theorem pF0E1_rest (fm em : Move) (slot : Slot) (hs : slot ≠ (1,true)) :
    ∃ mv, pF0E1 fm em slot = some (some mv) := by
  by_cases hF : slot = (5,false)
  · subst slot
    exact ⟨fm, by simp [pF0E1,pF0,fChild,fParent,fHole,refine]⟩
  · by_cases hE : slot = (4,true)
    · subst slot
      exact ⟨em, by simp [pF0E1,pF0,fChild,fParent,fHole,refine]⟩
    · obtain ⟨mv,hv⟩ := pF7_assigned slot hF hs hE
      refine ⟨mv, ?_⟩
      simpa [pF0E1,pF0,fChild,fParent,fHole,refine,hF,hE] using hv

theorem pF0B1_root (fm bm : Move) :
    pF0B1 fm bm initialSlot = some (some ⟨true,true,1⟩) := by
  simp [pF0B1,pF0,fChild,fParent,fHole,refine, fP7,fP6,fP5,
    fP4,fP3,fP2,fP1,fResidual,fRoot,initialSlot]

theorem pF0E1_root (fm em : Move) :
    pF0E1 fm em initialSlot = some (some ⟨true,true,1⟩) := by
  simp [pF0E1,pF0,fChild,fParent,fHole,refine, fP7,fP6,fP5,
    fP4,fP3,fP2,fP1,fResidual,fRoot,initialSlot]

theorem pF0B1_E1_unknown (fm bm : Move) :
    pF0B1 fm bm (4,true) = none := by
  simp [pF0B1,pF0,fChild,fParent,fHole,refine,fP7,fP6,fP5,
    fP4,fP3,fP2,fP1,fResidual,fRoot,emptyTable] <;> decide

theorem pF0E1_B1_unknown (fm em : Move) :
    pF0E1 fm em (1,true) = none := by
  simp [pF0E1,pF0,fChild,fParent,fHole,refine,fP7,fP6,fP5,
    fP4,fP3,fP2,fP1,fResidual,fRoot,emptyTable]

/-- Fully generic one-hole certificate. The only dynamic proof obligation
    is a bounded sparse run reaching the final hole. All ordinary table
    completions are nonhalting, independently of the run's eventual growth. -/
theorem bounded_last_hole
    (B : Nat) (hB : 128 ≤ B)
    (p : PartialMachine) (s : Slot) (n : Nat) (hn : n ≤ 120)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hunknown : p s = none)
    (hrest : ∀ slot, slot ≠ s → ∃ mv, p slot = some (some mv))
    (hknown : (knownRun p n).isSome = true)
    (hslot : readSlot ((knownRun p n).getD blank) = s) :
    ∀ m, compatible p m → WeightedBound B m := by
  let c : Config := (knownRun p n).getD blank
  have hr : knownRun p n = some c := by
    cases h : knownRun p n with
    | none => simp [h] at hknown
    | some cfg => simp [c,h]
  have hu : p (readSlot c) = none := by
    rw [hslot]
    exact hunknown
  apply last_hole_sound B p n c hroot hr hu
  · intro slot hs
    have hcslot : readSlot c = s := hslot
    rw [hcslot] at hs
    exact hrest slot hs
  · intro d hd
    have hd6 : d < 6 := by
      unfold possibleDelays at hd
      exact List.mem_range.mp (List.mem_filter.mp hd).1
    omega

theorem pF0B1_short (B : Nat) (hB : 128 ≤ B)
    (fm bm : Move) (n : Nat) (hn : n ≤ 120)
    (hknown : (knownRun (pF0B1 fm bm) n).isSome = true)
    (hslot : readSlot ((knownRun (pF0B1 fm bm) n).getD blank) = (4,true)) :
    ∀ m, compatible (pF0B1 fm bm) m → WeightedBound B m :=
  bounded_last_hole B hB _ (4,true) n hn
    (pF0B1_root fm bm) (pF0B1_E1_unknown fm bm)
    (pF0B1_rest fm bm) hknown hslot

theorem pF0E1_short (B : Nat) (hB : 128 ≤ B)
    (fm em : Move) (n : Nat) (hn : n ≤ 120)
    (hknown : (knownRun (pF0E1 fm em) n).isSome = true)
    (hslot : readSlot ((knownRun (pF0E1 fm em) n).getD blank) = (1,true)) :
    ∀ m, compatible (pF0E1 fm em) m → WeightedBound B m :=
  bounded_last_hole B hB _ (1,true) n hn
    (pF0E1_root fm em) (pF0E1_B1_unknown fm em)
    (pF0E1_rest fm em) hknown hslot

/-- Exhaustively split one of the two remaining holes, uniformly for
    all 24 ordinary transitions plus the explicit halt completion. The
    bounded halt child uses the exact TNF delay, not a heuristic cutoff. -/
theorem split_at_hole
    (B : Nat) (hB : 128 ≤ B)
    (p : PartialMachine) (slot : Slot) (n : Nat) (hn : n ≤ 120)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hunknown : p slot = none)
    (hknown : (knownRun p n).isSome = true)
    (hslot : readSlot ((knownRun p n).getD blank) = slot)
    (hchildren : ∀ mv : Move, ∀ m : Machine,
      compatible (refine p slot (some mv)) m → WeightedBound B m) :
    ∀ m, compatible p m → WeightedBound B m := by
  intro m hm
  let c : Config := (knownRun p n).getD blank
  have hr : knownRun p n = some c := by
    cases h : knownRun p n with
    | none => simp [h] at hknown
    | some cfg => simp [c,h]
  have hu : p (readSlot c) = none := by
    rw [hslot]
    exact hunknown
  have href := compatible_refine p m slot hm
  cases ht : m slot with
  | none =>
    apply first_hole_weighted_halt B p n c hroot hr hu
    · intro d hd
      have hd6 : d < 6 := by
        unfold possibleDelays at hd
        exact List.mem_range.mp (List.mem_filter.mp hd).1
      omega
    · rw [hslot]
      simpa [ht] using href
  | some mv =>
    exact hchildren mv m (by simpa [ht] using href)

/-- The initial A0 remains assigned along every depth-seven alternative. -/
theorem pF0_root (fm : Move) :
    pF0 fm initialSlot = some (some ⟨true,true,1⟩) := by
  simp [pF0,fChild,fParent,fHole,refine,fP7,fP6,fP5,
    fP4,fP3,fP2,fP1,fResidual,fRoot,initialSlot] <;> decide

theorem pF0_B1_unknown (fm : Move) : pF0 fm (1,true) = none := by
  simp [pF0,fChild,fParent,fHole,refine,fP7,fP6,fP5,
    fP4,fP3,fP2,fP1,fResidual,fRoot,emptyTable] <;> decide

theorem pF0_E1_unknown (fm : Move) : pF0 fm (4,true) = none := by
  simp [pF0,fChild,fParent,fHole,refine,fP7,fP6,fP5,
    fP4,fP3,fP2,fP1,fResidual,fRoot,emptyTable] <;> decide

#print axioms bounded_last_hole
#print axioms pF0B1_short
#print axioms pF0E1_short

end BB6.Agent26F412TwoHole
