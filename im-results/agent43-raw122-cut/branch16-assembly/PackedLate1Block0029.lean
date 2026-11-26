import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c29 : PZ := ⟨4,1295112594817152713946307937882345937761604559368093014167874939825936190136805665451,575145528899213648952896321856418787704259081014198879596877018649941⟩
def e29 : PZ := ⟨4,301541899055510925582216106793458093367890585066772302186087458353940441771,161889074352144089243288492235293242220200569921011626770984367478242023767100708181⟩
def a29 : List (Action table) := [.prim 2, .sweep m3 v3 29, .prim 8, .sweep m14 v14 9, .prim 2, .sweep m0 v0 119, .prim 8, .sweep m13 v13 8, .prim 2, .sweep m5 v5 61, .prim 8, .sweep m2 v2 41, .prim 2, .sweep m8 v8 25, .prim 8, .sweep m15 v15 9, .prim 2, .sweep m3 v3 32, .prim 8, .sweep m2 v2 43, .prim 2, .sweep m0 v0 131, .prim 8, .sweep m12 v12 11, .prim 2, .sweep m5 v5 67, .prim 8, .sweep m13 v13 9, .prim 2, .sweep m0 v0 137, .prim 8, .sweep m4 v4 23]
theorem s29 : prun table 8192 c29 = some e29 := by
  exact runActions_sound a29 c29 e29 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
