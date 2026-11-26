import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c21 : PZ := ⟨4,102609391136443956281976666927619216691747298439413722523350640649110101016528330927328969406241043171701027766266,0⟩
def e21 : PZ := ⟨4,6724609057517991118941190567190822837824702631891053343108033104134878441427727498648242128317012601098154368200343546,0⟩
def a21 : List (Action table) := [.prim 8, .sweep m4 v4 23, .prim 2, .sweep m8 v8 28, .prim 8, .sweep m2 v2 47, .prim 2, .sweep m0 v0 143, .prim 8, .sweep m12 v12 12, .prim 2, .sweep m5 v5 73, .prim 8, .sweep m11 v11 21, .prim 2, .sweep m0 v0 149, .prim 8, .sweep m13 v13 10, .prim 2, .sweep m3 v3 38, .prim 8, .sweep m7 v7 17, .prim 2, .sweep m8 v8 31, .prim 8, .sweep m14 v14 12, .prim 2, .sweep m5 v5 79, .prim 8, .sweep m2 v2 53, .prim 2, .sweep m0 v0 161]
theorem s21 : prun table 9680 c21 = some e21 := by
  exact runActions_sound a21 c21 e21 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
