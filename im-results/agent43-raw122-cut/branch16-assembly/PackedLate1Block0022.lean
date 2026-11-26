import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c22 : PZ := ⟨4,6724609057517991118941190567190822837824702631891053343108033104134878441427727498648242128317012601098154368200343546,0⟩
def e22 : PZ := ⟨4,440703979206325239859999033223761109918201954595028540483537167770159945916735468105952055205713271361572824826840646418426,0⟩
def a22 : List (Action table) := [.prim 8, .sweep m7 v7 18, .prim 2, .sweep m3 v3 41, .prim 8, .sweep m13 v13 11, .prim 2, .sweep m0 v0 167, .prim 8, .sweep m15 v15 12, .prim 2, .sweep m8 v8 34, .prim 8, .sweep m7 v7 19, .prim 2, .sweep m0 v0 173, .prim 8, .sweep m4 v4 29, .prim 2, .sweep m3 v3 44, .prim 8, .sweep m2 v2 59, .prim 2, .sweep m0 v0 179, .prim 8, .sweep m13 v13 12, .prim 2, .sweep m5 v5 91, .prim 8, .sweep m2 v2 61, .prim 2, .sweep m8 v8 37]
theorem s22 : prun table 11216 c22 = some e22 := by
  exact runActions_sound a22 c22 e22 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
