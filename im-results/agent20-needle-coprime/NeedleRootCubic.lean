import SpaceNeedleRawBridge
import NeedleCubicEnumerateSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20.SpaceNeedleRootCubic
open BusyBeaver
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open BB6.Agent20.SpaceNeedleCubicEnumeration

private theorem iterate_step {S : Type} (f : S → Option S)
    (n : Nat) (x : Option S) :
    Nat.iterate (fun z : Option S => z.bind f) (n+1) x =
      (Nat.iterate (fun z : Option S => z.bind f) n x).bind f := by
  rw [Nat.add_comm n 1, Function.iterate_add_apply]
  rfl

private theorem terminal_ne_start (k : Nat) : haltTower k ≠ 1 := by
  cases k with
  | zero => decide
  | succ k =>
    change 2*(haltTower k+1) ≠ 1
    omega

/-- A noninitial high-level state reached by the actual blank orbit
has a genuinely blank-reachable, immediately preceding state. -/
private theorem reached_noninitial_has_parent (d : Nat)
    (h : ReachN d) (hd : d ≠ 1) :
    ∃ p, ReachN p ∧ highLevelNext (.N p) = some (.N d) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero =>
    have hstart : d=1 := by
      simpa [ReachN, highLevelStart, Function.iterate_zero] using hn.symm
    exact False.elim (hd hstart)
  | succ n =>
    unfold CollatzReachesIn at hn
    rw [Nat.add_comm n 1, Function.iterate_add_apply] at hn
    cases hp : Nat.iterate
      (fun z : Option HighLevelState => z.bind highLevelNext)
      n (some highLevelStart) with
    | none =>
      simp only [hp, Option.bind_none] at hn
      contradiction
    | some ps =>
      cases ps with
      | N p =>
        have hstep : highLevelNext (.N p) = some (.N d) := by
          simpa only [hp, Option.bind_some] using hn
        exact ⟨p,⟨n,hp⟩,hstep⟩

/-- An exact blank-origin raw-machine halting criterion in which every
terminal feeder is drawn from an exhaustive, explicit O(K/3)-length list.
This is a classification of necessary AND sufficient reachable feeders,
and does not establish the existence or avoidance of any such feeder. -/
theorem raw_halts_iff_reaches_cubic_feeder :
    IsHalt target ↔
      ∃ k q v : Nat,
        ReachN (oddTower q v) ∧
        (v,q) ∈ NeedleCubicEnum.cubicParents (k+1) := by
  rw [original_raw_halts_iff_power]
  constructor
  · rintro ⟨d,k,hr,hpower⟩
    have hd : d=haltTower k := by
      have hp := haltTower_power k
      omega
    have hneq : d ≠ 1 := by
      rw [hd]
      exact terminal_ne_start k
    obtain ⟨p,hparent,hstep⟩ :=
      reached_noninitial_has_parent d hr hneq
    obtain ⟨q,v,hprev,_⟩ :=
      (highLevelNext_iff_oddTower p d).mp hstep
    refine ⟨k,q,v,?_,?_⟩
    · simpa only [hprev] using hparent
    · apply (original_terminal_cubic_list_iff q v k).mpr
      rw [←hd]
      simpa only [hprev] using hstep
  · rintro ⟨k,q,v,hparent,hlist⟩
    have hstep := (original_terminal_cubic_list_iff q v k).mp hlist
    obtain ⟨n,hr⟩ := hparent
    have htarget : ReachN (haltTower k) := by
      refine ⟨n+1, ?_⟩
      change CollatzReachesIn highLevelNext (n+1) highLevelStart (.N (haltTower k))
      unfold CollatzReachesIn
      rw [Nat.add_comm n 1, Function.iterate_add_apply]
      rw [hr]
      exact hstep
    exact ⟨haltTower k,k,htarget,haltTower_power k⟩

#print axioms raw_halts_iff_reaches_cubic_feeder
end BB6.Agent20.SpaceNeedleRootCubic
