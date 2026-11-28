import Mod512Core
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent31F321Mod512
/-- Individually kernel-checked 64×512 subrectangle, with exact mask. -/
theorem chunk7 : ∀ x : Fin 64, ∀ y : Fin 512,
  closedAt (x.val+448) y.val := by decide +kernel
#print axioms chunk7
end BB6.Agent31F321Mod512
