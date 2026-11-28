import F412TwoHoleGeneric

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412ThreeHole
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent26F412Graft
open BB6.Agent26F412TwoHole

/-- Three-hole A1 siblings of F412 after the first eight fixed rows. -/
def pA1 (am : Move) : PartialMachine := fChild (6 : Fin 9) am
def pA1F0 (am fm : Move) : PartialMachine :=
  refine (pA1 am) (5,false) (some fm)
def pA1F0B1 (am fm bm : Move) : PartialMachine :=
  refine (pA1F0 am fm) (1,true) (some bm)
def pA1F0E1 (am fm em : Move) : PartialMachine :=
  refine (pA1F0 am fm) (4,true) (some em)

/-- Remaining assignments in fP6 exactly exclude A1, F0, B1, E1. -/
theorem pF6_assigned (slot : Slot)
    (ha : slot ≠ (0,true)) (hf : slot ≠ (5,false))
    (hb : slot ≠ (1,true)) (he : slot ≠ (4,true)) :
    ∃ mv, fP6 slot = some (some mv) := by
  obtain ⟨mv,hv⟩ := fFinalOtherSlots slot he
  refine ⟨mv, ?_⟩
  simpa [fP9,fP8,fP7,refine,ha,hf,hb] using hv

theorem pA1F0B1_rest (am fm bm : Move)
    (slot : Slot) (hs : slot ≠ (4,true)) :
    ∃ mv, pA1F0B1 am fm bm slot = some (some mv) := by
  by_cases ha : slot = (0,true)
  · subst slot
    exact ⟨am, by simp [pA1F0B1,pA1F0,pA1,fChild,fParent,fHole,refine]⟩
  · by_cases hf : slot = (5,false)
    · subst slot
      exact ⟨fm, by simp [pA1F0B1,pA1F0,pA1,fChild,fParent,fHole,refine]⟩
    · by_cases hb : slot = (1,true)
      · subst slot
        exact ⟨bm, by simp [pA1F0B1,pA1F0,pA1,fChild,fParent,fHole,refine]⟩
      · obtain ⟨mv,hv⟩ := pF6_assigned slot ha hf hb hs
        refine ⟨mv, ?_⟩
        simpa [pA1F0B1,pA1F0,pA1,fChild,fParent,fHole,refine,ha,hf,hb]
          using hv

theorem pA1F0E1_rest (am fm em : Move)
    (slot : Slot) (hs : slot ≠ (1,true)) :
    ∃ mv, pA1F0E1 am fm em slot = some (some mv) := by
  by_cases ha : slot = (0,true)
  · subst slot
    exact ⟨am, by simp [pA1F0E1,pA1F0,pA1,fChild,fParent,fHole,refine]⟩
  · by_cases hf : slot = (5,false)
    · subst slot
      exact ⟨fm, by simp [pA1F0E1,pA1F0,pA1,fChild,fParent,fHole,refine]⟩
    · by_cases he : slot = (4,true)
      · subst slot
        exact ⟨em, by simp [pA1F0E1,pA1F0,pA1,fChild,fParent,fHole,refine]⟩
      · obtain ⟨mv,hv⟩ := pF6_assigned slot ha hf hs he
        refine ⟨mv, ?_⟩
        simpa [pA1F0E1,pA1F0,pA1,fChild,fParent,fHole,refine,ha,hf,he]
          using hv

theorem pA1_root (am : Move) :
    pA1 am initialSlot = some (some ⟨true,true,1⟩) := by
  simp [pA1,fChild,fParent,fHole,refine,fP6,fP5,fP4,fP3,fP2,
    fP1,fResidual,fRoot,initialSlot] <;> decide

theorem pA1F0_root (am fm : Move) :
    pA1F0 am fm initialSlot = some (some ⟨true,true,1⟩) := by
  simp [pA1F0,refine,pA1_root,initialSlot] <;> decide

theorem pA1F0B1_root (am fm bm : Move) :
    pA1F0B1 am fm bm initialSlot = some (some ⟨true,true,1⟩) := by
  simp [pA1F0B1,refine,pA1F0_root,initialSlot] <;> decide

theorem pA1F0E1_root (am fm em : Move) :
    pA1F0E1 am fm em initialSlot = some (some ⟨true,true,1⟩) := by
  simp [pA1F0E1,refine,pA1F0_root,initialSlot] <;> decide

theorem pA1_F0_unknown (am : Move) : pA1 am (5,false) = none := by
  simp [pA1,fChild,fParent,fHole,refine,fP6,fP5,fP4,fP3,fP2,
    fP1,fResidual,fRoot,emptyTable]

theorem pA1F0_B1_unknown (am fm : Move) :
    pA1F0 am fm (1,true) = none := by
  simp [pA1F0,pA1,fChild,fParent,fHole,refine,fP6,fP5,fP4,fP3,
    fP2,fP1,fResidual,fRoot,emptyTable]

theorem pA1F0_E1_unknown (am fm : Move) :
    pA1F0 am fm (4,true) = none := by
  simp [pA1F0,pA1,fChild,fParent,fHole,refine,fP6,fP5,fP4,fP3,
    fP2,fP1,fResidual,fRoot,emptyTable]

theorem pA1F0B1_short (B : Nat) (hB : 128 ≤ B)
    (am fm bm : Move) (n : Nat) (hn : n ≤ 120)
    (hknown : (knownRun (pA1F0B1 am fm bm) n).isSome = true)
    (hslot : readSlot ((knownRun (pA1F0B1 am fm bm) n).getD blank) = (4,true)) :
    ∀ m, compatible (pA1F0B1 am fm bm) m → WeightedBound B m :=
  bounded_last_hole B hB _ (4,true) n hn
    (pA1F0B1_root am fm bm) (by
      simp [pA1F0B1,pA1F0_E1_unknown,refine])
    (pA1F0B1_rest am fm bm) hknown hslot

theorem pA1F0E1_short (B : Nat) (hB : 128 ≤ B)
    (am fm em : Move) (n : Nat) (hn : n ≤ 120)
    (hknown : (knownRun (pA1F0E1 am fm em) n).isSome = true)
    (hslot : readSlot ((knownRun (pA1F0E1 am fm em) n).getD blank) = (1,true)) :
    ∀ m, compatible (pA1F0E1 am fm em) m → WeightedBound B m :=
  bounded_last_hole B hB _ (1,true) n hn
    (pA1F0E1_root am fm em) (by
      simp [pA1F0E1,pA1F0_B1_unknown,refine])
    (pA1F0E1_rest am fm em) hknown hslot

#print axioms pA1F0B1_short
#print axioms pA1F0E1_short
end BB6.Agent26F412ThreeHole
