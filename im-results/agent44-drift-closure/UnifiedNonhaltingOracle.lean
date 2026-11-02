import RayOracle
import ZeroWriterOracle

namespace BB6Coverage

/-- One executable, source-audited sparse nonhalting oracle combining the
    existing fresh-ray criterion with arbitrary-direction zero-writing graphs.
    Both branches produce actual proof-carrying Cover.leaf objects. -/
def basicControlOracle (p : PartialMachine) : Bool :=
  rayOracle p || zeroWriterOracle p

theorem basicControlOracle_sound (p : PartialMachine) (bound : Nat)
    (h : basicControlOracle p = true) :
    Cover (DecidedBelow bound) p := by
  have hdisj : rayOracle p = true ∨ zeroWriterOracle p = true :=
    (Bool.or_eq_true _ _).mp (by simpa only [basicControlOracle] using h)
  rcases hdisj with hr | hz
  · exact rayOracle_sound p bound hr
  · exact zeroWriterOracle_sound p bound hz

/-- Direction-switching zero-writing controls require the second disjunct. -/
theorem alternating_zero_ray_rejected :
    rayOracle alternatingZeroTable = false := by decide

theorem alternating_zero_basic_accepted :
    basicControlOracle alternatingZeroTable = true := by decide

/-- The original right-sweeping write-one example is handled by the first. -/
theorem two_ray_basic_accepted :
    basicControlOracle twoRayTable = true := by decide

theorem alternating_zero_basic_leaf (bound : Nat) :
    Cover (DecidedBelow bound) alternatingZeroTable :=
  basicControlOracle_sound alternatingZeroTable bound alternating_zero_basic_accepted

theorem two_ray_basic_leaf (bound : Nat) :
    Cover (DecidedBelow bound) twoRayTable :=
  basicControlOracle_sound twoRayTable bound two_ray_basic_accepted

#print axioms basicControlOracle_sound
#print axioms alternating_zero_basic_leaf
#print axioms two_ray_basic_leaf

end BB6Coverage
