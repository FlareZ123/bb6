import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c7 : PZ := ⟨4,14867163465687082094357243897733967454928890,0⟩
def e7 : PZ := ⟨4,974334424887296304385702074224874175751044202490,0⟩
def a7 : List (Action table) := [.prim 8, .sweep m9 v9 3, .prim 2, .sweep m8 v8 7, .prim 8, .sweep m12 v12 3, .prim 2, .sweep m5 v5 19, .prim 8, .sweep m14 v14 3, .prim 2, .sweep m0 v0 41, .prim 8, .sweep m15 v15 3, .prim 2, .sweep m3 v3 11, .prim 8, .sweep m13 v13 3, .prim 2, .sweep m0 v0 47, .prim 8, .sweep m12 v12 4, .prim 2, .sweep m8 v8 10, .prim 8, .sweep m2 v2 17, .prim 2, .sweep m0 v0 53, .prim 8, .sweep m7 v7 6, .prim 2, .sweep m3 v3 14]
theorem s7 : prun table 2960 c7 = some e7 := by
  exact runActions_sound a7 c7 e7 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
