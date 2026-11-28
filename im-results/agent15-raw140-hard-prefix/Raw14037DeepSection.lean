import Raw14037RootBridge

namespace Raw14037DeepSection
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The next shared section state recorded by the Raw140 residual analysis. -/
def deep : BState :=
  ⟨1,false,U 1 2 ++ U 3 134 ++ U 5 410,[S 2,S 1,S 5]⟩

/-- Exact block-machine replay of the previously empirical hard half after the
symbolic ER/transfer prefix. -/
theorem macro_transferOut :
    execute M37 505387 Raw14037RootBridge.transferOut =
      some (1454281, deep) := by
  decide +kernel

theorem transferOut_run :
    run M37 1454281 Raw14037RootBridge.transferOut.prim =
      some deep.prim := by
  exact execute_sound M37 505387 1454281
    Raw14037RootBridge.transferOut deep macro_transferOut

#print axioms macro_transferOut
#print axioms transferOut_run
end Raw14037DeepSection
