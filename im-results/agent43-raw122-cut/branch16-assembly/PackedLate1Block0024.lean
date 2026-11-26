import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c24 : PZ := ⟨4,32492222977978299135684541220426762149645746977060350490279057585327593450847175269999700071532885680828803253453948107370790906,0⟩
def e24 : PZ := ⟨4,440703979193499065967943538688514026552269788642854146189765863516270527490874230550126140293143523231727474683348905536171,91625968981⟩
def a24 : List (Action table) := [.prim 8, .sweep m15 v15 15, .prim 2, .sweep m3 v3 53, .prim 8, .sweep m2 v2 71, .prim 2, .sweep m17 v17 14, .prim 17, .sweep m0 v0 2, .prim 8, .sweep m1 v1 3, .prim 2, .sweep m0 v0 5, .prim 8, .sweep m2 v2 2, .prim 2, .sweep m3 v3 2, .prim 8, .sweep m2 v2 3, .prim 2, .sweep m0 v0 11, .prim 8, .sweep m4 v4 2, .prim 2, .sweep m5 v5 7, .prim 8, .sweep m6 v6 3, .prim 2, .sweep m0 v0 17, .prim 8, .sweep m7 v7 2]
theorem s24 : prun table 3101 c24 = some e24 := by
  exact runActions_sound a24 c24 e24 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
