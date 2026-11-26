import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c37 : PZ := ⟨4,11184811,22661887693515396210755763479571994766062639689686695389842949896550551887396362356870933429983116188539278058079850709988120718406515508881472852427374393682936800888976777345353733461⟩
def e37 : PZ := ⟨4,797344288843968495596980859603131446048540329202777662961167895608125059621834349872137338673320672149048273067240221540035453206986828545742630432664840077443420594610331530049683314834862466842618,0⟩
def a37 : List (Action table) := [.prim 2, .sweep m3 v3 77, .prim 8, .sweep m2 v2 103, .prim 2, .sweep m0 v0 311, .prim 8, .sweep m14 v14 24, .prim 2, .sweep m5 v5 157, .prim 8, .sweep m13 v13 21, .prim 2, .sweep m0 v0 317, .prim 8, .sweep m4 v4 53, .prim 2, .sweep m8 v8 64, .prim 8, .sweep m2 v2 107, .prim 2, .sweep m0 v0 323, .prim 8, .sweep m12 v12 27, .prim 2, .sweep m18 v18 25, .prim 9, .sweep m0 v0 2, .prim 8, .sweep m1 v1 3, .prim 2, .sweep m0 v0 5]
theorem s37 : prun table 15935 c37 = some e37 := by
  exact runActions_sound a37 c37 e37 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
