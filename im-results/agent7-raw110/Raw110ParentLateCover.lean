import Raw110DeepParent
import Raw110LateCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw110
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit

private def isLate (p : PartialMachine) : Bool :=
  tableOK p (BB6.Agent7Raw110Pair.table false) ||
  tableOK p (BB6.Agent7Raw110Pair.table true)

/-- The two remaining entries are matched by all twelve transitions.
    This is not a claim about a search roster or an index convention. -/
theorem kid05_matches :
    (partialResiduals (child110 ⟨false,false,5⟩)
      (assembledKids ⟨false,false,5⟩)).all (fun e => isLate e.2) = true := by
  decide

theorem assembledChildren_matches (mv : Move) :
    (partialResiduals (child110 mv) (assembledKids mv)).all
      (fun e => isLate e.2) = true := by
  by_cases h : mv = ⟨false,false,5⟩
  · subst mv
    exact kid05_matches
  have hz : expectedCount mv = 0 := by
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    all_goals first | contradiction | rfl
  rw [List.eq_nil_of_length_eq_zero ((assembledKids_count mv).trans hz)]
  rfl

theorem assembledResidual_matches (e : List Move × PartialMachine)
    (he : e ∈ deepResiduals assembledKids) : isLate e.2 = true := by
  change e ∈ auditMoves.flatMap (fun mv =>
    (partialResiduals (child110 mv) (assembledKids mv)).map
      (fun a => (mv :: a.1,a.2))) at he
  obtain ⟨mv,_,hm⟩ := List.mem_flatMap.mp he
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
  exact List.all_eq_true.mp (assembledChildren_matches mv) a ha

theorem lateResidual_cover (B : Nat) (hB : 6766859 ≤ B)
    (e : List Move × PartialMachine) (he : e ∈ deepResiduals assembledKids) :
    Cover (WeightedBound B) e.2 := by
  have h := assembledResidual_matches e he
  simp only [isLate,Bool.or_eq_true] at h
  rcases h with hf|hs
  · rw [tableOK_sound _ _ hf]
    exact BB6.Agent7Raw110Late.fast_cover B (by omega)
  · rw [tableOK_sound _ _ hs]
    exact BB6.Agent7Raw110Late.slow_cover B hB

/-- Universal raw110 closure, with the old 7014-cut audit retained unchanged
    and exactly two late one-hole weighted covers at the actual target. -/
theorem raw110_cover (B : Nat) (hB : 6766859 ≤ B) :
    Cover (WeightedBound B) p110 :=
  assembledParentCover B (by omega) (lateResidual_cover B hB)

#print axioms kid05_matches
#print axioms assembledResidual_matches
#print axioms raw110_cover
end BB6.Agent7Raw110
