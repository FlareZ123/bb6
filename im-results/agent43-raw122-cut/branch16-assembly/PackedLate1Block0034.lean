import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c34 : PZ := ⟨4,886151997189943915269204706853563051,1016194189555987054486197014906629656819205124565420296503631822794717362897059121132912142924313792695256162474416218390445304583101655373141⟩
def e34 : PZ := ⟨4,206323339880896712483187371,286033235838775404790912533295058050719559804172637725391435977466064299308235668838439985027560606457387346307978369084880082833321526825523917845463127381⟩
def a34 : List (Action table) := [.prim 2, .sweep m3 v3 59, .prim 8, .sweep m2 v2 79, .prim 2, .sweep m0 v0 239, .prim 8, .sweep m13 v13 16, .prim 2, .sweep m5 v5 121, .prim 8, .sweep m7 v7 27, .prim 2, .sweep m8 v8 49, .prim 8, .sweep m4 v4 41, .prim 2, .sweep m3 v3 62, .prim 8, .sweep m2 v2 83, .prim 2, .sweep m0 v0 251, .prim 8, .sweep m15 v15 18, .prim 2, .sweep m5 v5 127, .prim 8, .sweep m13 v13 17, .prim 2, .sweep m0 v0 257, .prim 8, .sweep m4 v4 43]
theorem s34 : prun table 15872 c34 = some e34 := by
  exact runActions_sound a34 c34 e34 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
