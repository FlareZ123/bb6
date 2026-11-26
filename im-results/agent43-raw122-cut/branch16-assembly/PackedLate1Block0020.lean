import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c20 : PZ := ⟨4,1565695055182555485259653731192891351584363511467779127453813544009995768864109888056813531136109345706606586,0⟩
def e20 : PZ := ⟨4,102609391136443956281976666927619216691747298439413722523350640649110101016528330927328969406241043171701027766266,0⟩
def a20 : List (Action table) := [.prim 8, .sweep m4 v4 19, .prim 2, .sweep m3 v3 29, .prim 8, .sweep m14 v14 9, .prim 2, .sweep m0 v0 119, .prim 8, .sweep m13 v13 8, .prim 2, .sweep m5 v5 61, .prim 8, .sweep m2 v2 41, .prim 2, .sweep m8 v8 25, .prim 8, .sweep m15 v15 9, .prim 2, .sweep m3 v3 32, .prim 8, .sweep m2 v2 43, .prim 2, .sweep m0 v0 131, .prim 8, .sweep m12 v12 11, .prim 2, .sweep m5 v5 67, .prim 8, .sweep m13 v13 9, .prim 2, .sweep m0 v0 137]
theorem s20 : prun table 8144 c20 = some e20 := by
  exact runActions_sound a20 c20 e20 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
