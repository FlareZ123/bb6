import SpaceNeedleClosed
import NeedleTerminalDichotomySource
import NeedleTerminalDensityArithmetic
import NeedleLowHits

namespace BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

theorem terminal_feeder_iff (v k : Nat) :
    (∃ q, highLevelNext (.N (oddTower q v)) = some (.N (haltTower k))) ↔
    NeedleTerminalDensityArithmetic.Feeder (k+1) v := by
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨q, (predecessor_power_identity q v k).mp hq⟩
  · rintro ⟨q,hq⟩
    exact ⟨q,(predecessor_power_identity q v k).mpr hq⟩

theorem terminal_feeder_exponent_spacing {v k j : Nat} (hv : 2≤v) (hkj : k<j)
    (hk : ∃ q, highLevelNext (.N (oddTower q v)) = some (.N (haltTower k)))
    (hj : ∃ q, highLevelNext (.N (oddTower q v)) = some (.N (haltTower j))) :
    5*(v+1)*(v-2)<8*(j-k) := by
  have h := NeedleTerminalDensityArithmetic.feeder_spacing hv (show k+1<j+1 by omega)
    ((terminal_feeder_iff v k).mp hk) ((terminal_feeder_iff v j).mp hj)
  rwa [show j+1-(k+1)=j-k by omega] at h

#print axioms terminal_feeder_iff
#print axioms terminal_feeder_exponent_spacing
#print axioms predecessor_exception_or_square_bound
end BB6.Agent48.SpaceNeedle
