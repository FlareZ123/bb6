import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c25 : PZ := ⟨4,440703979193499065967943538688514026552269788642854146189765863516270527490874230550126140293143523231727474683348905536171,91625968981⟩
def e25 : PZ := ⟨4,102609391136443956281976666927457327617395154350170434031115347406889900446607319300557985038762801147933927058091,25790417485112089060398421⟩
def a25 : List (Action table) := [.prim 2, .sweep m8 v8 4, .prim 8, .sweep m11 v11 3, .prim 2, .sweep m0 v0 23, .prim 8, .sweep m12 v12 2, .prim 2, .sweep m5 v5 13, .prim 8, .sweep m7 v7 3, .prim 2, .sweep m0 v0 29, .prim 8, .sweep m13 v13 2, .prim 2, .sweep m3 v3 8, .prim 8, .sweep m9 v9 3, .prim 2, .sweep m8 v8 7, .prim 8, .sweep m12 v12 3, .prim 2, .sweep m5 v5 19, .prim 8, .sweep m14 v14 3, .prim 2, .sweep m0 v0 41, .prim 8, .sweep m15 v15 3]
theorem s25 : prun table 2048 c25 = some e25 := by
  exact runActions_sound a25 c25 e25 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
