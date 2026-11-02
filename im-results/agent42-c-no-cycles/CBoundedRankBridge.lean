import CNoCyclesBridge
import CBoundedRank

namespace BB6Agent42

/-- Exact source-level bounded reachability in Agent 11's unmodified map. -/
theorem source_hit_target_iff_bounded (s target : S) :
    (∃ n, sourceRun n (some s) = some target) ↔
    (∃ n, n < (rank target+1)*(rank target+1) ∧
          sourceRun n (some s) = some target) := by
  simpa only [source_run_agrees] using hit_target_iff_bounded s target

#print axioms source_hit_target_iff_bounded
end BB6Agent42
