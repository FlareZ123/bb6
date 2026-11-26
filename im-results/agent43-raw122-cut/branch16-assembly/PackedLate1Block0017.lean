import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c17 : PZ := ⟨4,5562466239377370006237035693149875298444543026970449921737087520370389659637903211107190833146,0⟩
def e17 : PZ := ⟨4,364541787463835320728750371186270227558861571815535406070969027092153146553783205862210740559020026,0⟩
def a17 : List (Action table) := [.prim 8, .sweep m15 v15 3, .prim 2, .sweep m3 v3 11, .prim 8, .sweep m13 v13 3, .prim 2, .sweep m0 v0 47, .prim 8, .sweep m12 v12 4, .prim 2, .sweep m8 v8 10, .prim 8, .sweep m2 v2 17, .prim 2, .sweep m0 v0 53, .prim 8, .sweep m7 v7 6, .prim 2, .sweep m3 v3 14, .prim 8, .sweep m2 v2 19, .prim 2, .sweep m0 v0 59, .prim 8, .sweep m13 v13 4, .prim 2, .sweep m5 v5 31, .prim 8, .sweep m7 v7 7, .prim 2, .sweep m8 v8 13]
theorem s17 : prun table 3536 c17 = some e17 := by
  exact runActions_sound a17 c17 e17 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
