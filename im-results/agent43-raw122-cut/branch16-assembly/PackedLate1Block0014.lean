import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c14 : PZ := ⟨4,7330077518507,140416388891409582263890703578227243091860127200732148339081303381⟩
def e14 : PZ := ⟨4,1707,39523699793003928037912229549632139213916154765871979192134855341367681583764821⟩
def a14 : List (Action table) := [.prim 2, .sweep m8 v8 22, .prim 8, .sweep m2 v2 37, .prim 2, .sweep m0 v0 113, .prim 8, .sweep m4 v4 19, .prim 2, .sweep m3 v3 29, .prim 8, .sweep m14 v14 9, .prim 2, .sweep m0 v0 119, .prim 8, .sweep m13 v13 8, .prim 2, .sweep m5 v5 61, .prim 8, .sweep m2 v2 41, .prim 2, .sweep m8 v8 25, .prim 8, .sweep m15 v15 9, .prim 2, .sweep m3 v3 32, .prim 8, .sweep m2 v2 43, .prim 2, .sweep m0 v0 131, .prim 8, .sweep m12 v12 11]
theorem s14 : prun table 7808 c14 = some e14 := by
  exact runActions_sound a14 c14 e14 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
