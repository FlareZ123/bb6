import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c3 : PZ := ⟨4,3246626956972881084410,0⟩
def e3 : PZ := ⟨4,30023997515803307,91625968981⟩
def a3 : List (Action table) := [.prim 8, .sweep m9 v9 3, .prim 2, .sweep m8 v8 7, .prim 8, .sweep m12 v12 3, .prim 4, .sweep m10 v10 3, .prim 11, .sweep m0 v0 2, .prim 8, .sweep m1 v1 3, .prim 2, .sweep m0 v0 5, .prim 8, .sweep m2 v2 2, .prim 2, .sweep m3 v3 2, .prim 8, .sweep m2 v2 3, .prim 2, .sweep m0 v0 11, .prim 8, .sweep m4 v4 2, .prim 2, .sweep m5 v5 7, .prim 8, .sweep m6 v6 3, .prim 2, .sweep m0 v0 17, .prim 8, .sweep m7 v7 2]
theorem s3 : prun table 979 c3 = some e3 := by
  exact runActions_sound a3 c3 e3 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
