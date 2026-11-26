import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c8 : PZ := ⟨4,974334424887296304385702074224874175751044202490,0⟩
def e8 : PZ := ⟨4,63861775544811133913828212450370702826885628397879290,0⟩
def a8 : List (Action table) := [.prim 8, .sweep m2 v2 19, .prim 2, .sweep m0 v0 59, .prim 8, .sweep m13 v13 4, .prim 2, .sweep m5 v5 31, .prim 8, .sweep m7 v7 7, .prim 2, .sweep m8 v8 13, .prim 8, .sweep m9 v9 6, .prim 2, .sweep m3 v3 17, .prim 8, .sweep m2 v2 23, .prim 2, .sweep m0 v0 71, .prim 8, .sweep m12 v12 6, .prim 2, .sweep m5 v5 37, .prim 8, .sweep m13 v13 5, .prim 2, .sweep m0 v0 77, .prim 8, .sweep m14 v14 6, .prim 2, .sweep m8 v8 16]
theorem s8 : prun table 4496 c8 = some e8 := by
  exact runActions_sound a8 c8 e8 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
