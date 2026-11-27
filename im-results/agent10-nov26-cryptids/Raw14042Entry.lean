import Raw140Sweep
import Raw140VariantTransfer
namespace Raw14042Entry
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Sweep Raw140VariantTransfer
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def rootS0 : RState := ⟨2,true,[(S 6,1)],[]⟩
def rootS1 : RState := ⟨2,true,[(S 5,5),(S 6,8),(S 4,1)],[(S 6,1),(S 0,1),(S 5,1)]⟩
def rootS2 : RState := ⟨2,true,[(S 4,1),(S 5,3),(S 6,4),(S 4,1)],[(S 4,7),(S 6,1),(S 2,2),(S 1,1)]⟩
def rootS3 : RState := ⟨1,false,[(S 0,1),(S 4,1),(S 5,12),(S 6,2),(S 4,1)],[(S 4,1),(S 0,1),(S 5,1)]⟩
def rootS4 : RState := ⟨1,false,[(S 1,1),(S 5,1),(S 4,1),(S 5,14),(S 4,1)],[(S 6,2),(S 2,1)]⟩
def rootS5 : RState := ⟨1,true,[(S 5,32)],[(S 6,1),(S 4,2),(S 6,1),(S 4,1)]⟩
theorem rootE1 : execute M42 256 rootS0 = some (1045,rootS1) := by decide +kernel
theorem rootE2 : execute M42 256 rootS1 = some (779,rootS2) := by decide +kernel
theorem rootE3 : execute M42 256 rootS2 = some (769,rootS3) := by decide +kernel
theorem rootE4 : execute M42 256 rootS3 = some (773,rootS4) := by decide +kernel
theorem rootE5 : execute M42 152 rootS4 = some (2617,rootS5) := by decide +kernel
theorem entry : run M42 5985 primBlank = some rootS5.prim := by
  have h0 : run M42 2 primBlank = some rootS0.prim := run_ext M42 (fill_extends _ _) _ _ _ base_start
  have h1 := join h0 (execute_sound M42 256 1045 rootS0 rootS1 rootE1)
  have h2 := join h1 (execute_sound M42 256 779 rootS1 rootS2 rootE2)
  have h3 := join h2 (execute_sound M42 256 769 rootS2 rootS3 rootE3)
  have h4 := join h3 (execute_sound M42 256 773 rootS3 rootS4 rootE4)
  have h5 := join h4 (execute_sound M42 152 2617 rootS4 rootS5 rootE5)
  exact h5
#print axioms entry
end Raw14042Entry
