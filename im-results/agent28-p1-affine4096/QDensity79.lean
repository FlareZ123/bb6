import Q4101
import DensityCount701
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace BB6.Agent28Affine4096

/-- Distinctness across the expanded 79 affine cylinders at period 4096. -/
theorem expanded_q_distinct_mod1024 :
    (expandedQ.map (fun q => q % 1024)).Nodup := by decide

theorem expanded_q_cardinality : expandedQ.length = 79 := by decide

/-- All 79 new classes lie outside the previous 701/1024 source exclusion census. -/
theorem expanded_q_outside_701 :
    expandedQ.all (fun q => !(BB6.Agent13Narrow.certified701 (q % 1024))) = true := by decide

#print axioms expanded_q_cardinality
#print axioms expanded_q_distinct_mod1024
#print axioms expanded_q_outside_701

end BB6.Agent28Affine4096
