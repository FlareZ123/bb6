import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c15 : PZ := ⟨4,1707,39523699793003928037912229549632139213916154765871979192134855341367681583764821⟩
def e15 : PZ := ⟨4,84876499013936920261185237017057423377144516402747343776505852056432554156805787716943866,0⟩
def a15 : List (Action table) := [.prim 2, .sweep m5 v5 67, .prim 8, .sweep m13 v13 9, .prim 2, .sweep m0 v0 137, .prim 8, .sweep m1 v1 139, .prim 2, .sweep m19 v19 10, .prim 9, .sweep m0 v0 2, .prim 8, .sweep m1 v1 3, .prim 2, .sweep m0 v0 5, .prim 8, .sweep m2 v2 2, .prim 2, .sweep m3 v3 2, .prim 8, .sweep m2 v2 3, .prim 2, .sweep m0 v0 11, .prim 8, .sweep m4 v4 2, .prim 2, .sweep m5 v5 7, .prim 8, .sweep m6 v6 3, .prim 2, .sweep m0 v0 17]
theorem s15 : prun table 2967 c15 = some e15 := by
  exact runActions_sound a15 c15 e15 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
