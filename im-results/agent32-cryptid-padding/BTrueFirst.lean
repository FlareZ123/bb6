import Lean.Elab.Tactic.Omega
import PhysicalReturnObs
import PrefixNoF
import NoEarlierF

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

namespace BB6.Agent32BTrueFirst

open CryptidBoundary
open BB6.Agent32EDoubleFirst
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidFirstReturn

/-- Original-source all-k all-suffix B return is the first F/0 whose
    entire physical left half-tape is blank, independently of far zeros. -/
theorem full_B_true_physical_first (k : Nat) (ys : List Bool) :
    ∀ t, 0<t → t<12*k*k+49*k+40 →
      ¬PhysicalF0
        (run t (init (List.replicate (3*k) true ++ false::ys))) := by
  intro t hpos hbound hp
  by_cases hearly : t<12*k*k+41*k+31
  · exact (prefixB_positive_noF k ys t hpos hearly) hp.1
  · have hprefix :
        run (12*k*k+41*k+31)
          (init (List.replicate (3*k) true ++ false::ys)) =
        sweepB (4*k+3) ys := by
      rw [prefix_B]
      rfl
    have htime :
        t=(12*k*k+41*k+31)+(t-(12*k*k+41*k+31)) := by omega
    have hrest : t-(12*k*k+41*k+31)<2*(4*k+3)+3 := by omega
    rw [htime,run_add,hprefix] at hp
    exact (sweepB_firstF (4*k+3) ys
      (t-(12*k*k+41*k+31)) hrest) hp.1

#print axioms full_B_true_physical_first

end BB6.Agent32BTrueFirst
