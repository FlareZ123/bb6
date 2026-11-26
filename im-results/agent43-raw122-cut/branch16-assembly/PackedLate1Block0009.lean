import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c9 : PZ := ⟨4,63861775544811133913828212450370702826885628397879290,0⟩
def e9 : PZ := ⟨4,2494296127711407647067622114502456353546124873345707,22369621⟩
def a9 : List (Action table) := [.prim 8, .sweep m7 v7 9, .prim 2, .sweep m0 v0 83, .prim 8, .sweep m15 v15 6, .prim 2, .sweep m5 v5 43, .prim 8, .sweep m2 v2 29, .prim 2, .sweep m0 v0 89, .prim 8, .sweep m13 v13 6, .prim 4, .sweep m18 v18 7, .prim 9, .sweep m0 v0 2, .prim 8, .sweep m1 v1 3, .prim 2, .sweep m0 v0 5, .prim 8, .sweep m2 v2 2, .prim 2, .sweep m3 v3 2, .prim 8, .sweep m2 v2 3, .prim 2, .sweep m0 v0 11, .prim 8, .sweep m4 v4 2]
theorem s9 : prun table 2719 c9 = some e9 := by
  exact runActions_sound a9 c9 e9 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
