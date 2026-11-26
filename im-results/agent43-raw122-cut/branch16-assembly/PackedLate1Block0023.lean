import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c23 : PZ := ⟨4,440703979206325239859999033223761109918201954595028540483537167770159945916735468105952055205713271361572824826840646418426,0⟩
def e23 : PZ := ⟨4,32492222977978299135684541220426762149645746977060350490279057585327593450847175269999700071532885680828803253453948107370790906,0⟩
def a23 : List (Action table) := [.prim 8, .sweep m4 v4 31, .prim 2, .sweep m3 v3 47, .prim 8, .sweep m7 v7 21, .prim 2, .sweep m0 v0 191, .prim 8, .sweep m12 v12 16, .prim 2, .sweep m5 v5 97, .prim 8, .sweep m14 v14 15, .prim 2, .sweep m0 v0 197, .prim 8, .sweep m9 v9 18, .prim 2, .sweep m8 v8 40, .prim 8, .sweep m2 v2 67, .prim 2, .sweep m0 v0 203, .prim 8, .sweep m12 v12 17, .prim 2, .sweep m5 v5 103, .prim 8, .sweep m7 v7 23, .prim 2, .sweep m0 v0 209]
theorem s23 : prun table 12752 c23 = some e23 := by
  exact runActions_sound a23 c23 e23 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
