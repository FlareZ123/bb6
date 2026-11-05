import GatesTo299
import FastShield
set_option maxHeartbeats 0
namespace CascadeFastReturn
open CascadeSource CascadeSweep CascadeManyShield

private theorem orbit_append {x y z:Nat×Nat} (hr:Orbit x y)
    (he:Cstep y.1 y.2=some z) : Orbit x z := by
  induction hr generalizing z with
  | refl =>
    rcases z with ⟨c,d⟩
    exact Orbit.step he (Orbit.refl _)
  | step he0 htail ih =>
    exact Orbit.step he0 (ih he)

/-- The source forward ReachC closure injects into the older Cstep Orbit
    closure used by the FastShield family. -/
theorem reachC_to_orbit {x y:Nat×Nat} (hr:ReachC x y):Orbit x y:=by
  induction hr with
  | refl => exact Orbit.refl _
  | push hr he ih => exact orbit_append ih he

/-- Uniform extension of the previous genuine-root fatal family exclusion
    through index 256 to index 299 inclusive. -/
theorem fatal_unreachable_through_299 (n:Nat)
    (hn:4≤n) (hhi:n≤299) (hres:n%6=4∨n%6=5):
    ¬ReachC (2,0) (fatal n,0) := by
  by_cases hle:n≤256
  · intro hr
    exact CascadeFastShield.blank_excludes_surviving_through_256 n hn hle hres
      (reachC_to_orbit hr)
  · have h257 :257≤n:=by omega
    exact fatal_unreachable_257_to_299 n h257 hhi hres

#print axioms fatal_unreachable_through_299
end CascadeFastReturn
