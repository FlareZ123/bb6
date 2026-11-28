import Raw140VariantTransfer
namespace Raw14037ClusterEntry
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def section0 : BState :=
  ⟨1,false,U 1 2 ++ U 3 5 ++ U 5 29,[S 2,S 1,S 5]⟩

theorem macro37 :
    execute M37 2204 start = some (6410,section0) := by decide +kernel
theorem macro40 :
    execute M40 2208 start = some (6414,section0) := by decide +kernel
theorem macro44 :
    execute M44 2204 start = some (6408,section0) := by decide +kernel
theorem macro83 :
    execute M83 2206 start = some (6412,section0) := by decide +kernel

theorem entry37 : run M37 6412 primBlank = some section0.prim := by
  have h0 : run M37 2 primBlank = some start.prim :=
    run_ext M37 (fill_extends _ _) _ _ _ base_start
  exact join h0 (execute_sound M37 2204 6410 start section0 macro37)

theorem entry40 : run M40 6416 primBlank = some section0.prim := by
  have h0 : run M40 2 primBlank = some start.prim :=
    run_ext M40 (fill_extends _ _) _ _ _ base_start
  exact join h0 (execute_sound M40 2208 6414 start section0 macro40)

theorem entry44 : run M44 6410 primBlank = some section0.prim := by
  have h0 : run M44 2 primBlank = some start.prim :=
    run_ext M44 (fill_extends _ _) _ _ _ base_start
  exact join h0 (execute_sound M44 2204 6408 start section0 macro44)

theorem entry83 : run M83 6414 primBlank = some section0.prim := by
  have h0 : run M83 2 primBlank = some start.prim :=
    run_ext M83 (fill_extends _ _) _ _ _ base_start
  exact join h0 (execute_sound M83 2206 6412 start section0 macro83)

#print axioms entry37
#print axioms entry40
#print axioms entry44
#print axioms entry83
end Raw14037ClusterEntry
