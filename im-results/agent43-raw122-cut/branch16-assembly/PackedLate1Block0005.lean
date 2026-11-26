import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c5 : PZ := ⟨4,6990507,25790417485112089060398421⟩
def e5 : PZ := ⟨4,226854911280625642308916404954512490490,0⟩
def a5 : List (Action table) := [.prim 2, .sweep m3 v3 11, .prim 8, .sweep m13 v13 3, .prim 2, .sweep m0 v0 47, .prim 8, .sweep m12 v12 4, .prim 2, .sweep m8 v8 10, .prim 8, .sweep m2 v2 17, .prim 2, .sweep m0 v0 53, .prim 8, .sweep m7 v7 6, .prim 2, .sweep m3 v3 14, .prim 8, .sweep m16 v16 29, .prim 2, .sweep m17 v17 4, .prim 7, .sweep m0 v0 2, .prim 8, .sweep m1 v1 3, .prim 2, .sweep m0 v0 5, .prim 8, .sweep m2 v2 2, .prim 2, .sweep m3 v3 2]
theorem s5 : prun table 2319 c5 = some e5 := by
  exact runActions_sound a5 c5 e5 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
