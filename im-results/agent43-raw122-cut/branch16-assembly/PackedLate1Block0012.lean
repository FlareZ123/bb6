import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c12 : PZ := ⟨4,135216064024344469492981675240107,1772303994379887830538409413707126101⟩
def e12 : PZ := ⟨4,31482443219130968091307,498859225542281529413524422900491270709224974669141⟩
def a12 : List (Action table) := [.prim 2, .sweep m5 v5 31, .prim 8, .sweep m7 v7 7, .prim 2, .sweep m8 v8 13, .prim 8, .sweep m9 v9 6, .prim 2, .sweep m3 v3 17, .prim 8, .sweep m2 v2 23, .prim 2, .sweep m0 v0 71, .prim 8, .sweep m12 v12 6, .prim 2, .sweep m5 v5 37, .prim 8, .sweep m13 v13 5, .prim 2, .sweep m0 v0 77, .prim 8, .sweep m14 v14 6, .prim 2, .sweep m8 v8 16, .prim 8, .sweep m7 v7 9, .prim 2, .sweep m0 v0 83, .prim 8, .sweep m15 v15 6]
theorem s12 : prun table 4736 c12 = some e12 := by
  exact runActions_sound a12 c12 e12 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
