import CSharpBound
import CNoCyclesBridge

namespace BB6Agent42

/-- Source-level all-state target reachability cutoff, with exact 
    floor((R+2)^2/4) primitive-accelerator step limit. -/
theorem source_sharp_hit_target_iff_bounded (s target : S) :
    (∃ n, sourceRun n (some s) = some target) ↔
    (∃ n, n < ((rank target+2)*(rank target+2))/4 ∧
       sourceRun n (some s) = some target) := by
  simpa only [source_run_agrees, ← cutoff_closed_form] using
    sharp_hit_target_iff_bounded s target

#print axioms source_sharp_hit_target_iff_bounded
end BB6Agent42
