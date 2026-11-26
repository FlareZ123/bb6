import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c30 : PZ := ⟨4,301541899055510925582216106793458093367890585066772302186087458353940441771,161889074352144089243288492235293242220200569921011626770984367478242023767100708181⟩
def e30 : PZ := ⟨4,70208194445704791131945351789113621545930063600366074169540651691,45567723432979415091093796398283778444857696476941925758870220966874020816653665067156524521313621⟩
def a30 : List (Action table) := [.prim 2, .sweep m8 v8 28, .prim 8, .sweep m2 v2 47, .prim 2, .sweep m0 v0 143, .prim 8, .sweep m12 v12 12, .prim 2, .sweep m5 v5 73, .prim 8, .sweep m11 v11 21, .prim 2, .sweep m0 v0 149, .prim 8, .sweep m13 v13 10, .prim 2, .sweep m3 v3 38, .prim 8, .sweep m7 v7 17, .prim 2, .sweep m8 v8 31, .prim 8, .sweep m14 v14 12, .prim 2, .sweep m5 v5 79, .prim 8, .sweep m2 v2 53, .prim 2, .sweep m0 v0 161, .prim 8, .sweep m7 v7 18]
theorem s30 : prun table 9728 c30 = some e30 := by
  exact runActions_sound a30 c30 e30 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
