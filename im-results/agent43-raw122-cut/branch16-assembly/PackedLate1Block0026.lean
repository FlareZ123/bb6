import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c26 : PZ := ⟨4,102609391136443956281976666927457327617395154350170434031115347406889900446607319300557985038762801147933927058091,25790417485112089060398421⟩
def e26 : PZ := ⟨4,23890610583229911579279384326063405633297551970502928372266550410280446625921716750729359928230475901611,7259357160980020553885324958544388511061⟩
def a26 : List (Action table) := [.prim 2, .sweep m3 v3 11, .prim 8, .sweep m13 v13 3, .prim 2, .sweep m0 v0 47, .prim 8, .sweep m12 v12 4, .prim 2, .sweep m8 v8 10, .prim 8, .sweep m2 v2 17, .prim 2, .sweep m0 v0 53, .prim 8, .sweep m7 v7 6, .prim 2, .sweep m3 v3 14, .prim 8, .sweep m2 v2 19, .prim 2, .sweep m0 v0 59, .prim 8, .sweep m13 v13 4, .prim 2, .sweep m5 v5 31, .prim 8, .sweep m7 v7 7, .prim 2, .sweep m8 v8 13, .prim 8, .sweep m9 v9 6]
theorem s26 : prun table 3584 c26 = some e26 := by
  exact runActions_sound a26 c26 e26 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
