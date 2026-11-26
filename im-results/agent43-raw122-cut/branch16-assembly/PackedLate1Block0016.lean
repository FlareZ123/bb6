import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c16 : PZ := ⟨4,84876499013936920261185237017057423377144516402747343776505852056432554156805787716943866,0⟩
def e16 : PZ := ⟨4,5562466239377370006237035693149875298444543026970449921737087520370389659637903211107190833146,0⟩
def a16 : List (Action table) := [.prim 8, .sweep m7 v7 2, .prim 2, .sweep m8 v8 4, .prim 8, .sweep m11 v11 3, .prim 2, .sweep m0 v0 23, .prim 8, .sweep m12 v12 2, .prim 2, .sweep m5 v5 13, .prim 8, .sweep m7 v7 3, .prim 2, .sweep m0 v0 29, .prim 8, .sweep m13 v13 2, .prim 2, .sweep m3 v3 8, .prim 8, .sweep m9 v9 3, .prim 2, .sweep m8 v8 7, .prim 8, .sweep m12 v12 3, .prim 2, .sweep m5 v5 19, .prim 8, .sweep m14 v14 3, .prim 2, .sweep m0 v0 41]
theorem s16 : prun table 2000 c16 = some e16 := by
  exact runActions_sound a16 c16 e16 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
