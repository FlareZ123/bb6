import Raw110ParentResidualMatch
import Raw110LateCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw110
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit

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

#print axioms raw110_cover
end BB6.Agent7Raw110
