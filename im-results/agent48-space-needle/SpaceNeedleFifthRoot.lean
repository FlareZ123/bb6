import NeedleRootDecisionSource
import NeedleRootSharp
import NeedleQuinticEnumerateSource
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 4096
set_option maxHeartbeats 0

namespace BB6.Agent48.SpaceNeedleFifthRoot
open BusyBeaver
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open BB6.Agent20.SpaceNeedleRootDecision

/-- The unique large exceptional fifth-bound synthetic feeder. -/
def source42 : Nat :=
  oddTower 340282366920822406584691642613415018481 42

theorem source42_exact :
    source42 = 2993155353252668329380384070183193549327509602959358 := by
  decide +kernel

/-- Direct exact inverse computation: this feeder has no incoming legal
    high-level transition from any nonterminal counter. -/
theorem source42_has_no_parents :
    NeedleGeneralInverse.parents (source42+2) = [] := by
  rw [source42_exact]
  decide +kernel

/-- Every reachable noninitial counter has a source-legal incoming edge.
    The exceptional feeder has none, so it is never reached from blank. -/
theorem blank_never_source42 : ¬ ReachN source42 := by
  intro hr
  have hn : NeedleRootDecisionCore.Reached numericNext source42 :=
    (numericReached_iff_original source42).mpr hr
  have hne : source42 ≠ 1 := by
    rw [source42_exact]
    decide
  obtain ⟨p,_,hstep⟩ :=
    NeedleRootDecisionCore.reached_noninitial_parent numericNext source42 hn hne
  have hmem : p ∈ finiteParents source42 :=
    (finiteParents_spec p source42).mpr hstep
  have hnil : finiteParents source42 = [] := by
    unfold finiteParents
    rw [source42_has_no_parents]
    rfl
  rw [hnil] at hmem
  simp at hmem

/-- Source-exact blank-root halting criterion with every exceptional
    valuation family eliminated from authentic reachability. The
    existential over all k remains unbounded and unresolved. -/
theorem raw_halts_iff_reaches_fifth_regular :
    IsHalt target ↔
      ∃ k q v : Nat,
        ReachN (oddTower q v) ∧
        (v,q) ∈ NeedleQuinticEnum.quinticParents (k+1) ∧
        5*v ≤ k+4 := by
  rw [BB6.Agent20.SpaceNeedleRootCubic.raw_halts_iff_reaches_cubic_feeder]
  constructor
  · rintro ⟨k,q,v,hr,hlist⟩
    have he := (NeedleCubicEnum.cubicParents_spec q v (k+1)).mp hlist
    rcases NeedleQuinticEnum.quintic_valuation_bound q v (k+1) he with
      ⟨hq,hv,hK⟩ | ⟨hq,hv,hK⟩ | hb
    · subst q
      subst v
      have hbad : ReachN 7998 := by
        simpa only [BB6.Agent20.SpaceNeedleRootSharp.exceptional_source_counter]
          using hr
      exact False.elim (BB6.Agent20.SpaceNeedleRootSharp.blank_never_7998 hbad)
    · subst q
      subst v
      have hbad : ReachN source42 := by
        simpa only [source42] using hr
      exact False.elim (blank_never_source42 hbad)
    · exact ⟨k,q,v,hr,
        (NeedleQuinticEnum.quinticParents_spec q v (k+1)).mpr he,
        by omega⟩
  · rintro ⟨k,q,v,hr,hlist,_⟩
    have he := (NeedleQuinticEnum.quinticParents_spec q v (k+1)).mp hlist
    exact ⟨k,q,v,hr,(NeedleCubicEnum.cubicParents_spec q v (k+1)).mpr he⟩

#print axioms source42_has_no_parents
#print axioms blank_never_source42
#print axioms raw_halts_iff_reaches_fifth_regular
end BB6.Agent48.SpaceNeedleFifthRoot
