import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
abbrev p59 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,0⟩)
abbrev child (mv : Move) : PartialMachine := refine p59 (0,true) (some mv)
theorem p59_root : p59 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p59_nohalt : weightedTNFNoAssignedHalt p59 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
theorem query : zipQueryOK 395 p59 7 (0,true) = true := by decide
theorem halt_branch (m : Machine) (hc : compatible (refine p59 (0,true) none) m) :
    WeightedBound 395 m := by
  obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound query
  cases hr : knownRun p59 7 with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = (0,true) := by simpa [hr] using hread
    exact first_hole_weighted_halt 395 p59 7 c p59_root hr
      (by simpa only [hs] using hhole)
      (by simpa only [hs] using weightOK_sound p59 (0,true) 7 395 hw)
      m (by simpa only [hs] using hc)
theorem cycle_child (mv : Move) (e k : Nat) (r : Bool) (b : Int)
    (h : zipCheck 395 (child mv) (.cycle e k r b) = true) :
    ∀ m, compatible (child mv) m → WeightedBound 395 m :=
  (certifiedZip 395 (child mv) (.cycle e k r b)
    (refine_preserves_firstOne p59 (0,true) (some mv) (by decide) p59_root)
    (weightedTNFNoAssignedHalt_refine _ _ _ p59_nohalt) h).sound
theorem all_0RA : ∀ m, compatible (child ⟨false,true,0⟩) m → WeightedBound 395 m := cycle_child ⟨false,true,0⟩ 0 10 true 0 (by decide)
theorem all_1RA : ∀ m, compatible (child ⟨true,true,0⟩) m → WeightedBound 395 m := cycle_child ⟨true,true,0⟩ 0 10 true 0 (by decide)
theorem all_1LD : ∀ m, compatible (child ⟨true,false,3⟩) m → WeightedBound 395 m := cycle_child ⟨true,false,3⟩ 11 1 false (-1) (by decide)
theorem all_1RE : ∀ m, compatible (child ⟨true,true,4⟩) m → WeightedBound 395 m := cycle_child ⟨true,true,4⟩ 6 2 true 1 (by decide)
#print axioms halt_branch
#print axioms all_0RA
#print axioms all_1RA
#print axioms all_1LD
#print axioms all_1RE
end BB6.Agent32Raw59
