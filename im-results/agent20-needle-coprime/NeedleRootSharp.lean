import NeedleRootCubic
import NeedleSharperSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20.SpaceNeedleRootSharp
open BusyBeaver
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open BB6.Agent20.SpaceNeedleRootCubic
open BB6.Agent20.SpaceNeedleSharp

private def rootRun (n : Nat) : Option HighLevelState :=
  Nat.iterate
    (fun z : Option HighLevelState => z.bind highLevelNext)
    n (some highLevelStart)

private theorem run_succ (n : Nat) :
    rootRun (n+1) = (rootRun n).bind highLevelNext := by
  unfold rootRun
  rw [Nat.add_comm n 1, Function.iterate_add_apply]
  rfl

private theorem root_run_12 :
    rootRun 12 = some (.N 13098) := by decide

private theorem root_after_12 (j d : Nat)
    (h : rootRun (12+j) = some (.N d)) : 13098 ≤ d := by
  induction j generalizing d with
  | zero =>
    rw [Nat.add_zero, root_run_12] at h
    cases h
    omega
  | succ j ih =>
    have hj : 12+(j+1) = (12+j)+1 := by omega
    rw [hj,run_succ] at h
    cases hr : rootRun (12+j) with
    | none =>
      simp only [hr,Option.none_bind] at h
      contradiction
    | some st =>
      cases st with
      | N p =>
        have hh : highLevelNext (.N p) = some (.N d) := by
          simpa only [hr,Option.some_bind] using h
        have hp := ih p hr
        have hstep := highLevelNext_strict p d hh
        omega

/-- The unique low-exponent exceptional synthetic feeder cannot be visited
by the actual original blank-start Space Needle high-level trajectory. -/
theorem blank_never_7998 : ¬ ReachN 7998 := by
  rintro ⟨n,hn⟩
  change rootRun n = some (.N 7998) at hn
  by_cases hlow : n < 12
  · have hcases :
      n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨
      n=7 ∨ n=8 ∨ n=9 ∨ n=10 ∨ n=11 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 |
      h6 | h7 | h8 | h9 | h10 | h11
    all_goals subst n
    all_goals decide
  · have he : n=12+(n-12) := by omega
    rw [he] at hn
    have hg := root_after_12 (n-12) 7998 hn
    omega

theorem exceptional_source_counter : oddTower 61 6 = 7998 := by decide

/-- The raw blank-tape machine can halt exactly if the genuine blank-root
high-level orbit visits a feeder from the complete cubic inverse list,
and EVERY such genuine feeder obeys 3v+3 ≤ K without an exception. -/
theorem raw_halts_iff_reaches_sharp_feeder :
    IsHalt target ↔
      ∃ k q v : Nat,
        ReachN (oddTower q v) ∧
        (v,q) ∈ NeedleCubicEnum.cubicParents (k+1) ∧
        3*v+3 ≤ k+1 := by
  rw [raw_halts_iff_reaches_cubic_feeder]
  constructor
  · rintro ⟨k,q,v,hr,hlist⟩
    have hstep :=
      (BB6.Agent20.SpaceNeedleCubicEnumeration.original_terminal_cubic_list_iff
        q v k).mp hlist
    have hb := original_terminal_sharper_bound q v k hstep
    rcases hb with ⟨hq,hv,hk⟩ | hstrong
    · subst q
      subst v
      have hbad : ReachN 7998 := by
        simpa only [exceptional_source_counter] using hr
      exact False.elim (blank_never_7998 hbad)
    · exact ⟨k,q,v,hr,hlist,hstrong⟩
  · rintro ⟨k,q,v,hr,hlist,_⟩
    exact ⟨k,q,v,hr,hlist⟩

#print axioms blank_never_7998
#print axioms raw_halts_iff_reaches_sharp_feeder
end BB6.Agent20.SpaceNeedleRootSharp
