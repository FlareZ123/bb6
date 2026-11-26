import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c41 : PZ := ⟨4,224432465132730602975615568336218823063481164920455418005259985197599238583342115076849772214510440585684606671196937289088829109341175631493453430214480249598089543423272105967086230186704838663265430378721050618,0⟩
def e41 : PZ := ⟨4,14708406034938632796609941886482436788288301624226966274392718389909863699797908853676426671850156234223426382803562482177725504509783286185554964002536177671941741253997605672877650014177633060701566781318510332084218,0⟩
def a41 : List (Action table) := [.prim 8, .sweep m14 v14 6, .prim 2, .sweep m8 v8 16, .prim 8, .sweep m7 v7 9, .prim 2, .sweep m0 v0 83, .prim 8, .sweep m15 v15 6, .prim 2, .sweep m5 v5 43, .prim 8, .sweep m2 v2 29, .prim 2, .sweep m0 v0 89, .prim 8, .sweep m13 v13 6, .prim 2, .sweep m3 v3 23, .prim 8, .sweep m2 v2 31, .prim 2, .sweep m8 v8 19, .prim 8, .sweep m12 v12 8, .prim 2, .sweep m5 v5 49, .prim 8, .sweep m9 v9 9, .prim 2, .sweep m0 v0 101]
theorem s41 : prun table 5840 c41 = some e41 := by
  exact runActions_sound a41 c41 e41 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
