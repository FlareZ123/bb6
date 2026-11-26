import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c19 : PZ := ⟨4,23890610583229911579279384326063405633297551970504971699654371595424924421957917162974184913726720704506,0⟩
def e19 : PZ := ⟨4,1565695055182555485259653731192891351584363511467779127453813544009995768864109888056813531136109345706606586,0⟩
def a19 : List (Action table) := [.prim 8, .sweep m13 v13 6, .prim 2, .sweep m3 v3 23, .prim 8, .sweep m2 v2 31, .prim 2, .sweep m8 v8 19, .prim 8, .sweep m12 v12 8, .prim 2, .sweep m5 v5 49, .prim 8, .sweep m9 v9 9, .prim 2, .sweep m0 v0 101, .prim 8, .sweep m4 v4 17, .prim 2, .sweep m3 v3 26, .prim 8, .sweep m13 v13 7, .prim 2, .sweep m0 v0 107, .prim 8, .sweep m12 v12 9, .prim 2, .sweep m8 v8 22, .prim 8, .sweep m2 v2 37, .prim 2, .sweep m0 v0 113]
theorem s19 : prun table 6608 c19 = some e19 := by
  exact runActions_sound a19 c19 e19 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
