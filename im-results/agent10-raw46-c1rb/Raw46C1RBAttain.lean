import Raw46C1RBBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw46C1RB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent10CanonicalAudit

def attainPartial : PartialMachine :=
  refine (refine (refine (refine (refine parent (0,true) (some ⟨false,false,5⟩))
    (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩))
    (4,true) (some ⟨false,true,0⟩)) (5,false) (some ⟨true,false,4⟩)
def witness : Machine := weightedTNFDefaultCompletion attainPartial

theorem witness_compatible : compatible parent witness := by
  have h := weightedTNFDefaultCompletion_compatible attainPartial
  apply refine_preserves_compat _ _ (0,true) (some ⟨false,false,5⟩) (by decide)
  apply refine_preserves_compat _ _ (1,true) (some ⟨false,false,4⟩) (by decide)
  apply refine_preserves_compat _ _ (4,false) (some ⟨true,false,0⟩) (by decide)
  apply refine_preserves_compat _ _ (4,true) (some ⟨false,true,0⟩) (by decide)
  apply refine_preserves_compat _ _ (5,false) (some ⟨true,false,4⟩) (by decide)
  exact h

theorem witness_halts : HaltsAfter witness 178 := by
  have hr : (knownRun attainPartial 178).map readSlot = some (5,true) := by decide
  exact (weightedTNF_halt_iff_firstHole attainPartial
    (weightedTNFNoAssignedHalt_refine _ _ _
      (weightedTNFNoAssignedHalt_refine _ _ _
        (weightedTNFNoAssignedHalt_refine _ _ _
          (weightedTNFNoAssignedHalt_refine _ _ _
            (weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt)))) ) 178).mpr (by
    cases he : knownRun attainPartial 178 with
    | none => simp [he] at hr
    | some c =>
      have hs : readSlot c = (5,true) := by simpa [he] using hr
      exact ⟨c, rfl, by rw [hs]; decide⟩)

theorem bound_lower (B : Nat) (h : ∀ m, compatible parent m → WeightedBound B m) : 179 ≤ B := by
  have hz := firstOne_terminal parent parent_root witness witness_compatible
  have hd : 0 ∈ delays (zeroNext witness) 0 := (mem_delays_iff hz).mpr ⟨0, TerminalPath.stop 0 hz⟩
  have hb := h witness witness_compatible 178 0 witness_halts hd
  omega
#print axioms witness_halts
#print axioms bound_lower
end BB6.Agent10Raw46C1RB
