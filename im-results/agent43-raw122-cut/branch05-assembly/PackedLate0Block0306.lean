import PackedLate0Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M0
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c306 : PZ := ⟨1,1144132943355101619163650133180232202878239216690550901565743909777343662242671269006306257404775624291353400435500196312378338827499171845526638584694221483,559245460⟩
def e306 : PZ := ⟨0,37490948287859969856754487564049848823914142652515971942506296438429198605809376900988887199685848871933451983765855567732533673368933982140460750791033966914217,17066⟩
def a306 : List (Action table) := [.prim 6, .sweep m6 v6 51, .prim 4, .sweep m12 v12 38, .prim 10, .sweep m9 v9 38, .prim 4, .sweep m2 v2 151, .prim 10, .sweep m1 v1 151, .prim 4, .sweep m10 v10 30, .prim 6, .sweep m11 v11 30, .prim 4, .sweep m2 v2 149, .prim 10, .sweep m1 v1 149, .prim 4, .sweep m12 v12 37, .prim 2, .sweep m13 v13 2, .prim 5]
theorem s306 : prun table 3087 c306 = some e306 := by
  exact runActions_sound a306 c306 e306 (by rfl)
end BB6Coverage.Agent29PackedLate.M0
