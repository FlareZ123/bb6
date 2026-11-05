import NeedleRootDecisionCore
import NeedleGeneralInverseSource
import SpaceNeedleRawBridge
import Lean.Elab.Tactic.Omega

/-!
An exact per-target rooted reachability decision for the authentic pinned
Space Needle single-counter acceleration, from the real blank start N 1.
The source-import theorem preserves the unbounded terminal-exponent
existential. It is not a nonhalting proof.
-/

namespace BB6.Agent20.SpaceNeedleRootDecision
open BusyBeaver
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- Forget the single original HighLevelState.N constructor without changing
the underlying published transition. -/
def numericNext (d : Nat) : Option Nat :=
  match highLevelNext (.N d) with
  | none => none
  | some (.N e) => some e

theorem numericNext_spec (p d : Nat) :
    numericNext p=some d ↔ highLevelNext (.N p)=some (.N d) := by
  cases h : highLevelNext (.N p) with
  | none => simp [numericNext,h]
  | some s =>
      cases s with
      | N e => simp [numericNext,h]

/-- All one-step predecessors, with the exact algebraic source representation. -/
def finiteParents (d : Nat) : List Nat :=
  (NeedleGeneralInverse.parents (d+2)).map fun (v,q) => oddTower q v

theorem finiteParents_spec (p d : Nat) :
    p ∈ finiteParents d ↔ numericNext p=some d := by
  rw [numericNext_spec]
  rw [finiteParents, List.mem_map]
  rw [BB6.Agent20.SpaceNeedleGeneralInverse.original_source_inverse_iff]
  constructor
  · rintro ⟨⟨v,q⟩,hm,he⟩
    exact ⟨q,v,he.symm,hm⟩
  · rintro ⟨q,v,he,hm⟩
    exact ⟨(v,q),hm,he.symm⟩

theorem numericNext_strict (p d : Nat)
    (h : numericNext p=some d) : p<d :=
  highLevelNext_strict p d ((numericNext_spec p d).mp h)

/-- A source-level run defined recursively for comparison with the
original published iterate, which uses the same total Option semantics. -/
private def originalRun : Nat → Option HighLevelState
  | 0 => some highLevelStart
  | n+1 => (originalRun n).bind highLevelNext

private theorem originalRun_eq_iter (n : Nat) :
    originalRun n =
      Nat.iterate (fun z : Option HighLevelState => z.bind highLevelNext)
        n (some highLevelStart) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (originalRun n).bind highLevelNext = _
      rw [ih]
      rw [Nat.add_comm n 1, Function.iterate_add_apply]
      rfl

private theorem originalRun_eq_numeric (n : Nat) :
    originalRun n =
      (NeedleRootDecisionCore.run numericNext n).map HighLevelState.N := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (originalRun n).bind highLevelNext =
        ((NeedleRootDecisionCore.run numericNext n).bind numericNext).map HighLevelState.N
      rw [ih]
      cases hp : NeedleRootDecisionCore.run numericNext n with
      | none => simp [hp]
      | some p =>
          cases hh : highLevelNext (.N p) with
          | none => simp [hp,numericNext,hh]
          | some s =>
              cases s with
              | N e => simp [hp,numericNext,hh]

/-- The generic arithmetic rooted reachability predicate is precisely the
original source's CollatzReachesStar predicate for the blank N 1. -/
theorem numericReached_iff_original (d : Nat) :
    NeedleRootDecisionCore.Reached numericNext d ↔ ReachN d := by
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    change Nat.iterate
      (fun z : Option HighLevelState => z.bind highLevelNext)
      n (some highLevelStart) = some (.N d)
    rw [←originalRun_eq_iter n, originalRun_eq_numeric n,hn]
    rfl
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    change Nat.iterate
      (fun z : Option HighLevelState => z.bind highLevelNext)
      n (some highLevelStart) = some (.N d) at hn
    rw [←originalRun_eq_iter n, originalRun_eq_numeric n] at hn
    cases hp : NeedleRootDecisionCore.run numericNext n with
    | none => simp [hp] at hn
    | some p =>
        have he : p=d := by simpa [hp] using hn
        simpa [he] using hp

/-- Sound, complete, executable exact blank-root reachability for EVERY
fixed target counter d, from the original six-state machine's certified
high-level reduction. No uniform all-d nonreachability is asserted. -/
theorem exact_root_target (d : Nat) :
    NeedleRootDecisionCore.reverseCheck finiteParents (d+1) d=true
      ↔ ReachN d := by
  exact
    (NeedleRootDecisionCore.exact_fixed_target
      numericNext finiteParents finiteParents_spec numericNext_strict d).trans
      (numericReached_iff_original d)

/-- The authentic blank-tape halting problem is equivalent to an unbounded
existence over terminal exponents of the exact computable Boolean root test.
This is a lossless reformulation, not a decision of that existential. -/
theorem raw_halts_iff_boolean_root_test :
    IsHalt target ↔
      ∃ k : Nat,
        NeedleRootDecisionCore.reverseCheck finiteParents
          (haltTower k+1) (haltTower k) = true := by
  rw [original_raw_halts_iff_power]
  constructor
  · rintro ⟨d,k,hr,hpow⟩
    have hd : d=haltTower k := by
      have hp := haltTower_power k
      omega
    refine ⟨k, (exact_root_target (haltTower k)).mpr ?_⟩
    simpa only [hd] using hr
  · rintro ⟨k,hbool⟩
    have hr := (exact_root_target (haltTower k)).mp hbool
    exact ⟨haltTower k,k,hr,haltTower_power k⟩

#print axioms finiteParents_spec
#print axioms numericReached_iff_original
#print axioms exact_root_target
#print axioms raw_halts_iff_boolean_root_test
end BB6.Agent20.SpaceNeedleRootDecision
