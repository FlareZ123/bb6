import Nov26Pair2
import BlockFARBridge
import ZipThreeHoleAudit
namespace Raw14036
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot BB6.Agent10Nov26
def p : PartialMachine := FAR.fromCodes [7,21,11,12,15,1,6,18,4,17,13,24]
theorem table_eq : p = leaf n12 := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  rw [table_eq] at hm
  exact n12_cover.sound m hm
#print axioms table_eq
#print axioms never
end Raw14036
