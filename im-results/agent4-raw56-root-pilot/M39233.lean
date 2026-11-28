import M3923Pair
import M39234
namespace BB6.Agent4Raw56RootE11LB.M39233
open BB6Coverage

def table : PartialMachine := M3923Pair.table true

theorem cover_never : Cover NeverHalts table := M3923Pair.paired_cover.mp M39234.cover_never

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := cover_never.sound m hm
#print axioms cover_never
#print axioms never
end BB6.Agent4Raw56RootE11LB.M39233
