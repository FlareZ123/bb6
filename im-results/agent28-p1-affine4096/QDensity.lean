import QFinal
import DensityCount701
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace BB6.Agent28Affine4096

/-- The seventy-eight certified parameter residues are pairwise distinct modulo 1024,
    so their 4096-modulus cylinders are disjoint even under reduction mod 1024. -/
theorem new_q_distinct_mod1024 :
    (newQ.map (fun q => q % 1024)).Nodup := by decide

theorem new_q_cardinality : newQ.length = 78 := by decide

/-- None of the 78 new classes is included in the earlier 701/1024 source census. -/
theorem new_q_outside_701 :
    newQ.all (fun q => !(BB6.Agent13Narrow.certified701 (q % 1024))) = true := by decide

#print axioms new_q_distinct_mod1024
#print axioms new_q_cardinality
#print axioms new_q_outside_701

end BB6.Agent28Affine4096
