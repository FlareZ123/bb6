import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c32 : PZ := ⟨4,16346619102569481155822368289603297958599883969958423211,12826173892055494535247083365932165952174394293771304253889418425861237555825914912569748129845350143491740882261⟩
def e32 : PZ := ⟨4,3805993847215893016155429251865320363687324331,3610246997553144348409393468936306905516194108562261165586561953925288161205241696666633341281431742314311472605994234152310101⟩
def a32 : List (Action table) := [.prim 2, .sweep m3 v3 47, .prim 8, .sweep m7 v7 21, .prim 2, .sweep m0 v0 191, .prim 8, .sweep m12 v12 16, .prim 2, .sweep m5 v5 97, .prim 8, .sweep m14 v14 15, .prim 2, .sweep m0 v0 197, .prim 8, .sweep m9 v9 18, .prim 2, .sweep m8 v8 40, .prim 8, .sweep m2 v2 67, .prim 2, .sweep m0 v0 203, .prim 8, .sweep m12 v12 17, .prim 2, .sweep m5 v5 103, .prim 8, .sweep m7 v7 23, .prim 2, .sweep m0 v0 209, .prim 8, .sweep m15 v15 15]
theorem s32 : prun table 12800 c32 = some e32 := by
  exact runActions_sound a32 c32 e32 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
