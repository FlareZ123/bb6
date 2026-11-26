import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c13 : PZ := ⟨4,31482443219130968091307,498859225542281529413524422900491270709224974669141⟩
def e13 : PZ := ⟨4,7330077518507,140416388891409582263890703578227243091860127200732148339081303381⟩
def a13 : List (Action table) := [.prim 2, .sweep m5 v5 43, .prim 8, .sweep m2 v2 29, .prim 2, .sweep m0 v0 89, .prim 8, .sweep m13 v13 6, .prim 2, .sweep m3 v3 23, .prim 8, .sweep m2 v2 31, .prim 2, .sweep m8 v8 19, .prim 8, .sweep m12 v12 8, .prim 2, .sweep m5 v5 49, .prim 8, .sweep m9 v9 9, .prim 2, .sweep m0 v0 101, .prim 8, .sweep m4 v4 17, .prim 2, .sweep m3 v3 26, .prim 8, .sweep m13 v13 7, .prim 2, .sweep m0 v0 107, .prim 8, .sweep m12 v12 9]
theorem s13 : prun table 6272 c13 = some e13 := by
  exact runActions_sound a13 c13 e13 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
