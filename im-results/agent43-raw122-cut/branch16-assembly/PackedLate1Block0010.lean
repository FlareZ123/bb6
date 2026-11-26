import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c10 : PZ := ⟨4,2494296127711407647067622114502456353546124873345707,22369621⟩
def e10 : PZ := ⟨4,580748572878401644310825996683551080884907,6296488643826193618261⟩
def a10 : List (Action table) := [.prim 2, .sweep m5 v5 7, .prim 8, .sweep m6 v6 3, .prim 2, .sweep m0 v0 17, .prim 8, .sweep m7 v7 2, .prim 2, .sweep m8 v8 4, .prim 8, .sweep m11 v11 3, .prim 2, .sweep m0 v0 23, .prim 8, .sweep m12 v12 2, .prim 2, .sweep m5 v5 13, .prim 8, .sweep m7 v7 3, .prim 2, .sweep m0 v0 29, .prim 8, .sweep m13 v13 2, .prim 2, .sweep m3 v3 8, .prim 8, .sweep m9 v9 3, .prim 2, .sweep m8 v8 7, .prim 8, .sweep m12 v12 3]
theorem s10 : prun table 1664 c10 = some e10 := by
  exact runActions_sound a10 c10 e10 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
