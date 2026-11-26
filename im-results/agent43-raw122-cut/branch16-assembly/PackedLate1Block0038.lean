import PackedLate1Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def c38 : PZ := ⟨4,797344288843968495596980859603131446048540329202777662961167895608125059621834349872137338673320672149048273067240221540035453206986828545742630432664840077443420594610331530049683314834862466842618,0⟩
def e38 : PZ := ⟨4,52254755313678319327443737614950822448237139014633236919823099206574083907376535953220392627294743569960027623734655158847763461373088795573789028035122959315332012088382687153336045722554775299449421818,0⟩
def a38 : List (Action table) := [.prim 8, .sweep m2 v2 2, .prim 2, .sweep m3 v3 2, .prim 8, .sweep m2 v2 3, .prim 2, .sweep m0 v0 11, .prim 8, .sweep m4 v4 2, .prim 2, .sweep m5 v5 7, .prim 8, .sweep m6 v6 3, .prim 2, .sweep m0 v0 17, .prim 8, .sweep m7 v7 2, .prim 2, .sweep m8 v8 4, .prim 8, .sweep m11 v11 3, .prim 2, .sweep m0 v0 23, .prim 8, .sweep m12 v12 2, .prim 2, .sweep m5 v5 13, .prim 8, .sweep m7 v7 3, .prim 2, .sweep m0 v0 29]
theorem s38 : prun table 1232 c38 = some e38 := by
  exact runActions_sound a38 c38 e38 (by rfl)
end BB6Coverage.Agent29PackedLate.M1
