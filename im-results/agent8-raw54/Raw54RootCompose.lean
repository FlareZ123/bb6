import Raw54E1Compose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false
namespace BB6.Agent8Raw54
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6Coverage.Agent10ZipAudit

def rootChild (mv : Move) : PartialMachine := refine raw54 (4,true) (some mv)

def rootCycle (mv : Move) : Bool :=
  (!mv.write && !mv.right && mv.next == 2) ||
  (!mv.write && mv.next == 3) ||
  (mv.write && !mv.right && mv.next == 3)

theorem root_query (B : Nat) (hB : 7014 ≤ B) : zipQueryOK B raw54 6 (4,true) = true := by
  have h : zipQueryOK 7014 raw54 6 (4,true) = true := by decide
  obtain ⟨hr,hu,hw⟩ := zipQueryOK_sound h
  have hh : weightOK raw54 (4,true) 6 B = true := by
    apply List.all_eq_true.mpr
    intro d hd
    exact decide_eq_true (Nat.le_trans (weightOK_sound raw54 (4,true) 6 7014 hw d hd) hB)
  unfold zipQueryOK
  have hs : zipRead raw54 6 = some (4,true) := by decide
  simp [hs,hu,hh]

theorem root_cover_of_open_children (B : Nat) (hB : 7014 ≤ B)
    (kids : ∀ mv, rootCycle mv = false → ∀ m, compatible (rootChild mv) m → WeightedBound B m) :
    ∀ m, compatible raw54 m → WeightedBound B m := by
  apply cover_of_firstHole B raw54 6 (4,true) (by decide) (root_query B hB)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  all_goals first | exact kids _ (by decide) | skip
  · exact cycle_weighted _ _ 8 1 false 0 (by decide) (by decide)
  · exact cycle_weighted _ _ 7 1 false (-1) (by decide) (by decide)
  · exact cycle_weighted _ _ 7 1 false 1 (by decide) (by decide)
  · exact cycle_weighted _ _ 7 1 false (-1) (by decide) (by decide)
#print axioms root_query
#print axioms root_cover_of_open_children
end BB6.Agent8Raw54
