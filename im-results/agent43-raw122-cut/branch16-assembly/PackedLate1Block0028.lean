import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c28 : PZ := ⟨4,5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731,2043327387821185144477796036200412244824985496244802901⟩
def e28 : PZ := ⟨4,1295112594817152713946307937882345937761604559368093014167874939825936190136805665451,575145528899213648952896321856418787704259081014198879596877018649941⟩
def a28 : List (Action table) := [.prim 2, .sweep m3 v3 23, .prim 8, .sweep m2 v2 31, .prim 2, .sweep m8 v8 19, .prim 8, .sweep m12 v12 8, .prim 2, .sweep m5 v5 49, .prim 8, .sweep m9 v9 9, .prim 2, .sweep m0 v0 101, .prim 8, .sweep m4 v4 17, .prim 2, .sweep m3 v3 26, .prim 8, .sweep m13 v13 7, .prim 2, .sweep m0 v0 107, .prim 8, .sweep m12 v12 9, .prim 2, .sweep m8 v8 22, .prim 8, .sweep m2 v2 37, .prim 2, .sweep m0 v0 113, .prim 8, .sweep m4 v4 19]
theorem s28 : prun table 6656 c28 = some e28 := by
  exact runActions_sound a28 c28 e28 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
