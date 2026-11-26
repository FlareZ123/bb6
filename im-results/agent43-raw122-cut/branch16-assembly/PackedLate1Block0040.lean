import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c40 : PZ := ⟨4,3424567644237222335443352788333417099967669142463003814777526629602039162953828660230251651222388314600900370349074360490247026204546747306723837741309818261689598744224247785713722497250508238101039571533818,0⟩
def e40 : PZ := ⟨4,224432465132730602975615568336218823063481164920455418005259985197599238583342115076849772214510440585684606671196937289088829109341175631493453430214480249598089543423272105967086230186704838663265430378721050618,0⟩
def a40 : List (Action table) := [.prim 8, .sweep m7 v7 6, .prim 2, .sweep m3 v3 14, .prim 8, .sweep m2 v2 19, .prim 2, .sweep m0 v0 59, .prim 8, .sweep m13 v13 4, .prim 2, .sweep m5 v5 31, .prim 8, .sweep m7 v7 7, .prim 2, .sweep m8 v8 13, .prim 8, .sweep m9 v9 6, .prim 2, .sweep m3 v3 17, .prim 8, .sweep m2 v2 23, .prim 2, .sweep m0 v0 71, .prim 8, .sweep m12 v12 6, .prim 2, .sweep m5 v5 37, .prim 8, .sweep m13 v13 5, .prim 2, .sweep m0 v0 77]
theorem s40 : prun table 4304 c40 = some e40 := by
  exact runActions_sound a40 c40 e40 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
