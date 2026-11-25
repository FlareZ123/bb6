import ZipThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3Raw120
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31ThreeHole BB6.Agent10ZipAudit

abbrev p120 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,4⟩)
abbrev pRF : PartialMachine := refine p120 (4,false) (some ⟨false,true,5⟩)
abbrev p1 : PartialMachine := refine pRF (5,true) (some ⟨false,false,0⟩)
abbrev p2 : PartialMachine := refine p1 (2,true) (some ⟨true,true,1⟩)
abbrev p3 : PartialMachine := refine p2 (1,true) (some ⟨true,true,5⟩)
abbrev p448 : PartialMachine := refine p3 (0,true) (some ⟨true,false,5⟩)

theorem late_query_checked : zipQueryOK 14416 p448 14415 (5,false) = true := by decide

def lateMachine : Machine := weightedTNFDefaultCompletion (refine p448 (5,false) none)

theorem late_compatible : compatible p448 lateMachine :=
  refine_preserves_compat _ _ _ _ (by decide) (weightedTNFDefaultCompletion_compatible _)

theorem late_compatible_RF : compatible pRF lateMachine := by
  have h3 : compatible p3 lateMachine :=
    refine_preserves_compat _ _ _ _ (by decide) late_compatible
  have h2 : compatible p2 lateMachine :=
    refine_preserves_compat _ _ _ _ (by decide) h3
  have h1 : compatible p1 lateMachine :=
    refine_preserves_compat _ _ _ _ (by decide) h2
  exact refine_preserves_compat _ _ _ _ (by decide) h1

theorem late_compatible_raw120 : compatible p120 lateMachine :=
  refine_preserves_compat _ _ _ _ (by decide) late_compatible_RF

theorem late_halts : HaltsAfter lateMachine 14415 := by
  obtain ⟨hr,hh,_⟩ := zipQueryOK_sound late_query_checked
  cases hrun : knownRun p448 14415 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = (5,false) := by simpa [hrun] using hr
    apply first_hole_halts p448 14415 c hrun
    · simpa [hs] using hh
    · simpa [hs,lateMachine] using
        (weightedTNFDefaultCompletion_compatible (refine p448 (5,false) none))

theorem late_bound_lower (B : Nat) (h : WeightedBound B lateMachine) : 14416 ≤ B := by
  have hz := firstOne_terminal p448 (by decide) lateMachine late_compatible
  have hd : 0 ∈ delays (zeroNext lateMachine) 0 :=
    (mem_delays_iff hz).mpr ⟨0, TerminalPath.stop 0 hz⟩
  have hb := h 14415 0 late_halts hd
  omega

theorem raw120_not_7014 :
    ¬ (∀ m, compatible p120 m → WeightedBound 7014 m) := by
  intro h
  have hh := late_bound_lower 7014 (h lateMachine late_compatible_raw120)
  omega

#print axioms late_query_checked
#print axioms late_halts
#print axioms raw120_not_7014
end BB6.Agent3Raw120
