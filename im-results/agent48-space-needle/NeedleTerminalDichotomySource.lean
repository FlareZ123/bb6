import SpaceNeedleClosed
import NeedleTerminalDichotomy

namespace BB6.Agent48.SpaceNeedle

/-- Source-linked version of the quadratic terminal-feeder bound. The
    predecessor relation is taken directly from the pinned Cryptids source
    adapter, so the arithmetic theorem applies to actual highLevelNext edges. -/
theorem predecessor_exception_or_square_bound
    (q v k : Nat) (hv : 11 ≤ v)
    (h : highLevelNext (.N (oddTower q v)) = some (.N (haltTower k))) :
    ((k+2)%(v+1)=0 ∧ ((k+2)/(v+1))%2=0 ∧
      2*v=3^((k+2)/(v+1))+3) ∨ v*v≤8*(k+2) := by
  have hfeed := (predecessor_power_identity q v k).mp h
  exact NeedleTerminalDichotomy.terminal_exception_or_square_bound
    q v (k+1) hv (by simpa [Nat.add_assoc] using hfeed)

end BB6.Agent48.SpaceNeedle
