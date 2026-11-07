import SpaceNeedleFifthRoot
import NeedleSixthRegular
import SixthNear
import NeedleRootDecisionSource
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace BB6.Agent48.SpaceNeedleSixthRoot
open BusyBeaver
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open BB6.Agent20.SpaceNeedleRootDecision

/-- A source-complete inverse computation certifies that the first exact
    exceptional feeder is absent from the real blank-start orbit. -/
theorem blank_never3446 : ¬ ReachN 3446 := by
  intro hr
  have hb := (exact_root_target 3446).mpr hr
  have hf : NeedleRootDecisionCore.reverseCheck finiteParents (3446+1) 3446 = false := by
    decide +kernel
  rw [hf] at hb
  contradiction

/-- The second exceptional feeder's full reverse cone dies after one edge. -/
theorem blank_never4006494 : ¬ ReachN 4006494 := by
  intro hr
  have hb := (exact_root_target 4006494).mpr hr
  have hf : NeedleRootDecisionCore.reverseCheck finiteParents (4006494+1) 4006494 = false := by
    decide +kernel
  rw [hf] at hb
  contradiction

private theorem smallSource : oddTower 214 3 = 3446 := by decide +kernel
private theorem largeSource : oddTower 62600 5 = 4006494 := by decide +kernel

/-- Sixth-linear exception-free incoming list is necessary and sufficient
    for the actual original blank-tape machine to halt. The existential over
    terminal exponent and genuine reachability remains unbounded. -/
theorem raw_halts_iff_reaches_sixth_regular :
    IsHalt target ↔
      ∃ k q v : Nat,
        ReachN (oddTower q v) ∧
        (v,q) ∈ NeedleSixthRegular.parents (k+1) := by
  rw [BB6.Agent48.SpaceNeedleFifthRoot.raw_halts_iff_reaches_fifth_regular]
  constructor
  · rintro ⟨k,q,v,hr,hlist,h5⟩
    have he := (NeedleQuinticEnum.quinticParents_spec q v (k+1)).mp hlist
    have hmodel : BB6.Agent48.FifthHigh.equation q v (k+1) := by
      unfold BB6.Agent48.FifthHigh.equation BB6.Agent48.FifthHigh.den
        BB6.Agent48.FifthHigh.bias
      change BB6.Agent48.Boundary.den v*q+
        BB6.Agent48.Boundary.bias v=(2:Nat)^(k+1)
      rw [BB6.Agent48.Boundary.model_eq]
      exact he
    rcases BB6.Agent48.SixthHigh.sixth_from_fifth q v (k+1) hmodel h5 with
      ⟨hq,hv,hK⟩ | ⟨hq,hv,hK⟩ | h6
    · subst q
      subst v
      have hbad : ReachN 3446 := by simpa only [smallSource] using hr
      exact False.elim (blank_never3446 hbad)
    · subst q
      subst v
      have hbad : ReachN 4006494 := by simpa only [largeSource] using hr
      exact False.elim (blank_never4006494 hbad)
    · exact ⟨k,q,v,hr,
        (NeedleSixthRegular.parents_spec q v (k+1)).mpr ⟨he,by omega⟩⟩
  · rintro ⟨k,q,v,hr,hlist⟩
    obtain ⟨he,h6⟩ := (NeedleSixthRegular.parents_spec q v (k+1)).mp hlist
    have h5 : 5*v≤k+4 := by omega
    exact ⟨k,q,v,hr,
      (NeedleQuinticEnum.quinticParents_spec q v (k+1)).mpr he,
      h5⟩

#print axioms blank_never3446
#print axioms blank_never4006494
#print axioms raw_halts_iff_reaches_sixth_regular
end BB6.Agent48.SpaceNeedleSixthRoot
