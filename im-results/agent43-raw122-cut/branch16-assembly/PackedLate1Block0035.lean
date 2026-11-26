import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c35 : PZ := ⟨4,206323339880896712483187371,286033235838775404790912533295058050719559804172637725391435977466064299308235668838439985027560606457387346307978369084880082833321526825523917845463127381⟩
def e35 : PZ := ⟨4,48038396025285291,80511198396192882181153164394416403006227652702217395805359067738573315464365842177837370137123387040884658667322962024528439138771728909494643930697230848931187100308821⟩
def a35 : List (Action table) := [.prim 2, .sweep m8 v8 52, .prim 8, .sweep m7 v7 29, .prim 2, .sweep m0 v0 263, .prim 8, .sweep m12 v12 22, .prim 2, .sweep m5 v5 133, .prim 8, .sweep m2 v2 89, .prim 2, .sweep m0 v0 269, .prim 8, .sweep m13 v13 18, .prim 2, .sweep m3 v3 68, .prim 8, .sweep m14 v14 21, .prim 2, .sweep m8 v8 55, .prim 8, .sweep m12 v12 23, .prim 2, .sweep m5 v5 139, .prim 8, .sweep m7 v7 31, .prim 2, .sweep m0 v0 281, .prim 8, .sweep m4 v4 47]
theorem s35 : prun table 17408 c35 = some e35 := by
  exact runActions_sound a35 c35 e35 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
