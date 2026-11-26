import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c36 : PZ := ⟨4,48038396025285291,80511198396192882181153164394416403006227652702217395805359067738573315464365842177837370137123387040884658667322962024528439138771728909494643930697230848931187100308821⟩
def e36 : PZ := ⟨4,11184811,22661887693515396210755763479571994766062639689686695389842949896550551887396362356870933429983116188539278058079850709988120718406515508881472852427374393682936800888976777345353733461⟩
def a36 : List (Action table) := [.prim 2, .sweep m3 v3 71, .prim 8, .sweep m13 v13 19, .prim 2, .sweep m0 v0 287, .prim 8, .sweep m12 v12 24, .prim 2, .sweep m8 v8 58, .prim 8, .sweep m2 v2 97, .prim 2, .sweep m0 v0 293, .prim 8, .sweep m15 v15 21, .prim 2, .sweep m3 v3 74, .prim 8, .sweep m9 v9 27, .prim 2, .sweep m0 v0 299, .prim 8, .sweep m13 v13 20, .prim 2, .sweep m5 v5 151, .prim 8, .sweep m2 v2 101, .prim 2, .sweep m8 v8 61, .prim 8, .sweep m7 v7 34]
theorem s36 : prun table 18944 c36 = some e36 := by
  exact runActions_sound a36 c36 e36 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
