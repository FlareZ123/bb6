import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c1 : PZ := ⟨4,6990507,5461⟩
def e1 : PZ := ⟨4,48038396025634810,0⟩
def a1 : List (Action table) := [.prim 2, .sweep m3 v3 2, .prim 8, .sweep m2 v2 3, .prim 2, .sweep m0 v0 11, .prim 8, .sweep m4 v4 2, .prim 2, .sweep m5 v5 7, .prim 8, .sweep m6 v6 3, .prim 2, .sweep m0 v0 17, .prim 8, .sweep m7 v7 2, .prim 2, .sweep m8 v8 4, .prim 8, .sweep m9 v9 2, .prim 2, .sweep m10 v10 2, .prim 7, .sweep m0 v0 2, .prim 8, .sweep m1 v1 3, .prim 2, .sweep m0 v0 5, .prim 8, .sweep m2 v2 2, .prim 2, .sweep m3 v3 2]
theorem s1 : prun table 807 c1 = some e1 := by
  exact runActions_sound a1 c1 e1 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
