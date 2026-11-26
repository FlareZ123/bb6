import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c31 : PZ := ⟨4,70208194445704791131945351789113621545930063600366074169540651691,45567723432979415091093796398283778444857696476941925758870220966874020816653665067156524521313621⟩
def e31 : PZ := ⟨4,16346619102569481155822368289603297958599883969958423211,12826173892055494535247083365932165952174394293771304253889418425861237555825914912569748129845350143491740882261⟩
def a31 : List (Action table) := [.prim 2, .sweep m3 v3 41, .prim 8, .sweep m13 v13 11, .prim 2, .sweep m0 v0 167, .prim 8, .sweep m15 v15 12, .prim 2, .sweep m8 v8 34, .prim 8, .sweep m7 v7 19, .prim 2, .sweep m0 v0 173, .prim 8, .sweep m4 v4 29, .prim 2, .sweep m3 v3 44, .prim 8, .sweep m2 v2 59, .prim 2, .sweep m0 v0 179, .prim 8, .sweep m13 v13 12, .prim 2, .sweep m5 v5 91, .prim 8, .sweep m2 v2 61, .prim 2, .sweep m8 v8 37, .prim 8, .sweep m4 v4 31]
theorem s31 : prun table 11264 c31 = some e31 := by
  exact runActions_sound a31 c31 e31 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
