import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c33 : PZ := ⟨4,3805993847215893016155429251865320363687324331,3610246997553144348409393468936306905516194108562261165586561953925288161205241696666633341281431742314311472605994234152310101⟩
def e33 : PZ := ⟨4,886151997189943915269204706853563051,1016194189555987054486197014906629656819205124565420296503631822794717362897059121132912142924313792695256162474416218390445304583101655373141⟩
def a33 : List (Action table) := [.prim 2, .sweep m3 v3 53, .prim 8, .sweep m2 v2 71, .prim 2, .sweep m8 v8 43, .prim 8, .sweep m12 v12 18, .prim 2, .sweep m5 v5 109, .prim 8, .sweep m2 v2 73, .prim 2, .sweep m0 v0 221, .prim 8, .sweep m4 v4 37, .prim 2, .sweep m3 v3 56, .prim 8, .sweep m13 v13 15, .prim 2, .sweep m0 v0 227, .prim 8, .sweep m12 v12 19, .prim 2, .sweep m8 v8 46, .prim 8, .sweep m9 v9 21, .prim 2, .sweep m0 v0 233, .prim 8, .sweep m14 v14 18]
theorem s33 : prun table 14336 c33 = some e33 := by
  exact runActions_sound a33 c33 e33 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
