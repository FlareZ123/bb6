import Raw140VariantTransfer

namespace Raw140SectionEntries
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def s31 : BState := ⟨1,false,U 1 2 ++ U 3 10 ++ U 5 25,[S 2,S 1,S 5]⟩
def s45 : BState := ⟨1,false,U 1 2 ++ U 3 6 ++ U 5 28,[S 2,S 1,S 5]⟩
def s85 : BState := ⟨1,false,U 1 2 ++ U 3 9 ++ U 5 26,[S 2,S 1,S 5]⟩

theorem macro31 : execute M31 2455 start = some (7313,s31) := by decide +kernel
theorem macro46 : execute M46 2455 start = some (7315,s31) := by decide +kernel
theorem macro45 : execute M45 2232 start = some (6508,s45) := by decide +kernel
theorem macro85 : execute M85 2411 start = some (7155,s85) := by decide +kernel

theorem entry31 : run M31 7315 primBlank = some s31.prim := by
  exact join (run_ext M31 (fill_extends _ _) _ _ _ base_start)
    (execute_sound M31 2455 7313 start s31 macro31)

theorem entry46 : run M46 7317 primBlank = some s31.prim := by
  exact join (run_ext M46 (fill_extends _ _) _ _ _ base_start)
    (execute_sound M46 2455 7315 start s31 macro46)

theorem entry45 : run M45 6510 primBlank = some s45.prim := by
  exact join (run_ext M45 (fill_extends _ _) _ _ _ base_start)
    (execute_sound M45 2232 6508 start s45 macro45)

theorem entry85 : run M85 7157 primBlank = some s85.prim := by
  exact join (run_ext M85 (fill_extends _ _) _ _ _ base_start)
    (execute_sound M85 2411 7155 start s85 macro85)

#print axioms entry31
#print axioms entry46
#print axioms entry45
#print axioms entry85
end Raw140SectionEntries
