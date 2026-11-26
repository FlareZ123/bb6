import Raw122Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122RootCompose
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 (parent_root parent_nohalt)

/-- Root composition from independent covers of all ordinary children.
The halt at the first F1 query is certified by the original root split. -/
theorem root_bound (C : Nat) (hC : 7014 ≤ C)
    (covers : ∀ (mv : Move) (m : Machine), compatible (BB6.Agent43Raw122.child mv) m → WeightedBound C m)
    (m : Machine) (hm : compatible BB6.Agent43Raw122.parent m) : WeightedBound C m := by
  let t : PartialAudit := .split 7 (5,true) (fun _ => .unresolved)
  have hcheck : partialCheck 7014 BB6.Agent43Raw122.parent t = true := by
    rw [partialCheck.eq_3,Bool.and_eq_true]
    exact ⟨by decide,allMoves_of _ (by intro mv; rfl)⟩
  rcases partialSound 7014 BB6.Agent43Raw122.parent t BB6.Agent43Raw122.parent_root BB6.Agent43Raw122.parent_nohalt hcheck m hm with h|⟨e,he,hh⟩
  · intro k d hk hd
    exact Nat.le_trans (h k d hk hd) hC
  · rw [partialResiduals.eq_3] at he
    obtain ⟨mv,_,hmem⟩ := List.mem_flatMap.mp he
    rw [partialResiduals.eq_1] at hmem
    obtain ⟨e',he',heq⟩ := List.mem_map.mp hmem
    have he'' : e' = ([], BB6.Agent43Raw122.child mv) := by simpa only [List.mem_singleton] using he'
    rw [← heq,he''] at hh
    exact covers mv m hh

#print axioms root_bound
end BB6.Agent43Raw122RootCompose
