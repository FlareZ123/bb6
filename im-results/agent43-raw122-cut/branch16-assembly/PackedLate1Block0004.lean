import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c4 : PZ := ⟨4,30023997515803307,91625968981⟩
def e4 : PZ := ⟨4,6990507,25790417485112089060398421⟩
def a4 : List (Action table) := [.prim 2, .sweep m8 v8 4, .prim 8, .sweep m11 v11 3, .prim 2, .sweep m0 v0 23, .prim 8, .sweep m12 v12 2, .prim 2, .sweep m5 v5 13, .prim 8, .sweep m7 v7 3, .prim 2, .sweep m0 v0 29, .prim 8, .sweep m13 v13 2, .prim 2, .sweep m3 v3 8, .prim 8, .sweep m9 v9 3, .prim 2, .sweep m8 v8 7, .prim 8, .sweep m12 v12 3, .prim 2, .sweep m5 v5 19, .prim 8, .sweep m14 v14 3, .prim 2, .sweep m0 v0 41, .prim 8, .sweep m15 v15 3]
theorem s4 : prun table 2048 c4 = some e4 := by
  exact runActions_sound a4 c4 e4 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
