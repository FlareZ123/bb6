import RawBoundaryNoCross
import DSectionTransfer
set_option maxHeartbeats 5000000

namespace BB6.RawBoundaryBridge
open BB6.Portfolio

/-- Every physical translated unary section inherits the exact all-k B
    return: both the elapsed primitive steps and absolute integer head. -/
theorem raw_full_B_exact_shifted (k : Nat) (h : Int) :
    BB6.Portfolio.run D0 (12*k*k+49*k+40)
      (some (F0Pure (3*k+2) h)) =
    some (F0Pure (8*k+9) (h - (5*(k:Int)+6))) := by
  have ht := BB6.Portfolio.run_transport D0 D0
    (BB6.Portfolio.translateCfg h) (BB6.Portfolio.translate_step D0 h)
    (12*k*k+49*k+40) (some (F0Pure (3*k+2) 0))
  rw [raw_full_B_exact_physical] at ht
  have he : (0:Int)+h = h := by omega
  have ho : -(5*(k:Int)+6)+h = h-(5*(k:Int)+6) := by omega
  simpa only [Option.map_some, translate_F0Pure, he, ho] using ht

#print axioms raw_full_B_exact_shifted
end BB6.RawBoundaryBridge
