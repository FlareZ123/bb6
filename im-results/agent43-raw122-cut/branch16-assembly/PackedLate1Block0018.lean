import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c18 : PZ := ⟨4,364541787463835320728750371186270227558861571815535406070969027092153146553783205862210740559020026,0⟩
def e18 : PZ := ⟨4,23890610583229911579279384326063405633297551970504971699654371595424924421957917162974184913726720704506,0⟩
def a18 : List (Action table) := [.prim 8, .sweep m9 v9 6, .prim 2, .sweep m3 v3 17, .prim 8, .sweep m2 v2 23, .prim 2, .sweep m0 v0 71, .prim 8, .sweep m12 v12 6, .prim 2, .sweep m5 v5 37, .prim 8, .sweep m13 v13 5, .prim 2, .sweep m0 v0 77, .prim 8, .sweep m14 v14 6, .prim 2, .sweep m8 v8 16, .prim 8, .sweep m7 v7 9, .prim 2, .sweep m0 v0 83, .prim 8, .sweep m15 v15 6, .prim 2, .sweep m5 v5 43, .prim 8, .sweep m2 v2 29, .prim 2, .sweep m0 v0 89]
theorem s18 : prun table 5072 c18 = some e18 := by
  exact runActions_sound a18 c18 e18 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
