import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c6 : PZ := ⟨4,226854911280625642308916404954512490490,0⟩
def e6 : PZ := ⟨4,14867163465687082094357243897733967454928890,0⟩
def a6 : List (Action table) := [.prim 8, .sweep m2 v2 3, .prim 2, .sweep m0 v0 11, .prim 8, .sweep m4 v4 2, .prim 2, .sweep m5 v5 7, .prim 8, .sweep m6 v6 3, .prim 2, .sweep m0 v0 17, .prim 8, .sweep m7 v7 2, .prim 2, .sweep m8 v8 4, .prim 8, .sweep m11 v11 3, .prim 2, .sweep m0 v0 23, .prim 8, .sweep m12 v12 2, .prim 2, .sweep m5 v5 13, .prim 8, .sweep m7 v7 3, .prim 2, .sweep m0 v0 29, .prim 8, .sweep m13 v13 2, .prim 2, .sweep m3 v3 8]
theorem s6 : prun table 1424 c6 = some e6 := by
  exact runActions_sound a6 c6 e6 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
