import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c11 : PZ := ⟨4,580748572878401644310825996683551080884907,6296488643826193618261⟩
def e11 : PZ := ⟨4,135216064024344469492981675240107,1772303994379887830538409413707126101⟩
def a11 : List (Action table) := [.prim 2, .sweep m5 v5 19, .prim 8, .sweep m14 v14 3, .prim 2, .sweep m0 v0 41, .prim 8, .sweep m15 v15 3, .prim 2, .sweep m3 v3 11, .prim 8, .sweep m13 v13 3, .prim 2, .sweep m0 v0 47, .prim 8, .sweep m12 v12 4, .prim 2, .sweep m8 v8 10, .prim 8, .sweep m2 v2 17, .prim 2, .sweep m0 v0 53, .prim 8, .sweep m7 v7 6, .prim 2, .sweep m3 v3 14, .prim 8, .sweep m2 v2 19, .prim 2, .sweep m0 v0 59, .prim 8, .sweep m13 v13 4]
theorem s11 : prun table 3200 c11 = some e11 := by
  exact runActions_sound a11 c11 e11 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
