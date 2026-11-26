import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c27 : PZ := ⟨4,23890610583229911579279384326063405633297551970502928372266550410280446625921716750729359928230475901611,7259357160980020553885324958544388511061⟩
def e27 : PZ := ⟨4,5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731,2043327387821185144477796036200412244824985496244802901⟩
def a27 : List (Action table) := [.prim 2, .sweep m3 v3 17, .prim 8, .sweep m2 v2 23, .prim 2, .sweep m0 v0 71, .prim 8, .sweep m12 v12 6, .prim 2, .sweep m5 v5 37, .prim 8, .sweep m13 v13 5, .prim 2, .sweep m0 v0 77, .prim 8, .sweep m14 v14 6, .prim 2, .sweep m8 v8 16, .prim 8, .sweep m7 v7 9, .prim 2, .sweep m0 v0 83, .prim 8, .sweep m15 v15 6, .prim 2, .sweep m5 v5 43, .prim 8, .sweep m2 v2 29, .prim 2, .sweep m0 v0 89, .prim 8, .sweep m13 v13 6]
theorem s27 : prun table 5120 c27 = some e27 := by
  exact runActions_sound a27 c27 e27 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
