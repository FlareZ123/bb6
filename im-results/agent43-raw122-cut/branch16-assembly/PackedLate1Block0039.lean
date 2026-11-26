import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c39 : PZ := ⟨4,52254755313678319327443737614950822448237139014633236919823099206574083907376535953220392627294743569960027623734655158847763461373088795573789028035122959315332012088382687153336045722554775299449421818,0⟩
def e39 : PZ := ⟨4,3424567644237222335443352788333417099967669142463003814777526629602039162953828660230251651222388314600900370349074360490247026204546747306723837741309818261689598744224247785713722497250508238101039571533818,0⟩
def a39 : List (Action table) := [.prim 8, .sweep m13 v13 2, .prim 2, .sweep m3 v3 8, .prim 8, .sweep m9 v9 3, .prim 2, .sweep m8 v8 7, .prim 8, .sweep m12 v12 3, .prim 2, .sweep m5 v5 19, .prim 8, .sweep m14 v14 3, .prim 2, .sweep m0 v0 41, .prim 8, .sweep m15 v15 3, .prim 2, .sweep m3 v3 11, .prim 8, .sweep m13 v13 3, .prim 2, .sweep m0 v0 47, .prim 8, .sweep m12 v12 4, .prim 2, .sweep m8 v8 10, .prim 8, .sweep m2 v2 17, .prim 2, .sweep m0 v0 53]
theorem s39 : prun table 2768 c39 = some e39 := by
  exact runActions_sound a39 c39 e39 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
