import NeedleRootDecisionSource
import NeedleQuadraticEnumerateSource
import Lean.Elab.Tactic.Decide
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48.SpaceNeedleCancellationHoldouts
open BusyBeaver
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open NeedleInverse

/-- The r=3 and r=4 exact-cancellation terminal feeders. -/
def cancellationK3 : Nat := 2201
def cancellationV3 : Nat := 366
def cancellationQ3 : Nat := candidateQ cancellationV3 cancellationK3
def cancellationFeeder3 : Nat := oddTower cancellationQ3 cancellationV3

def cancellationK4 : Nat := 26263
def cancellationV4 : Nat := 3282
def cancellationQ4 : Nat := candidateQ cancellationV4 cancellationK4
def cancellationFeeder4 : Nat := oddTower cancellationQ4 cancellationV4

/-- These are genuine exact terminal predecessors, with K+1=r*(9^r+5)
    and v=(9^r+3)/2 for r=3 and r=4. -/
theorem cancellation_r3_equation :
    equation cancellationQ3 cancellationV3 cancellationK3 := by
  native_decide

theorem cancellation_r4_equation :
    equation cancellationQ4 cancellationV4 cancellationK4 := by
  native_decide

theorem cancellation_r3_source_step :
    highLevelNext (.N cancellationFeeder3) = some (.N (haltTower 2200)) := by
  apply (BB6.Agent48.SpaceNeedleQuadraticEnumeration.original_terminal_quadratic_list_iff
    cancellationQ3 cancellationV3 2200).mp
  exact (NeedleQuadraticEnum.quadraticParents_spec
    cancellationQ3 cancellationV3 cancellationK3).mpr cancellation_r3_equation

theorem cancellation_r4_source_step :
    highLevelNext (.N cancellationFeeder4) = some (.N (haltTower 26262)) := by
  apply (BB6.Agent48.SpaceNeedleQuadraticEnumeration.original_terminal_quadratic_list_iff
    cancellationQ4 cancellationV4 26262).mp
  exact (NeedleQuadraticEnum.quadraticParents_spec
    cancellationQ4 cancellationV4 cancellationK4).mpr cancellation_r4_equation

theorem cancellation_r3_regular_parent :
    (cancellationV3,cancellationQ3) ∈
      NeedleQuadraticEnum.quadraticRegularParents cancellationK3 := by
  apply (NeedleQuadraticEnum.quadraticRegularParents_spec
    cancellationQ3 cancellationV3 cancellationK3).mpr
  exact ⟨cancellation_r3_equation, by norm_num [cancellationK3,cancellationV3]⟩

theorem cancellation_r4_regular_parent :
    (cancellationV4,cancellationQ4) ∈
      NeedleQuadraticEnum.quadraticRegularParents cancellationK4 := by
  apply (NeedleQuadraticEnum.quadraticRegularParents_spec
    cancellationQ4 cancellationV4 cancellationK4).mpr
  exact ⟨cancellation_r4_equation, by norm_num [cancellationK4,cancellationV4]⟩

/-- The exact incoming-parent computation for r=3 and the r=4 reverse
    chain. The list entries are the full generic inverse, not a bounded
    or heuristic predecessor search. -/
def cancellationR4Parent1Q : Nat :=
  NeedleGeneralInverse.quotientCandidate 4 (cancellationFeeder4+2)
def cancellationR4Parent1 : Nat := oddTower cancellationR4Parent1Q 4
def cancellationR4Parent2Q : Nat :=
  NeedleGeneralInverse.quotientCandidate 0 (cancellationR4Parent1+2)
def cancellationR4Parent2 : Nat := oddTower cancellationR4Parent2Q 0
def cancellationR4Parent3Q : Nat :=
  NeedleGeneralInverse.quotientCandidate 1 (cancellationR4Parent2+2)
def cancellationR4Parent3 : Nat := oddTower cancellationR4Parent3Q 1

theorem cancellation_r3_incoming_parents :
    NeedleGeneralInverse.parents (cancellationFeeder3+2) = [] := by
  native_decide

theorem cancellation_r4_incoming_parents :
    NeedleGeneralInverse.parents (cancellationFeeder4+2) =
      [(4,cancellationR4Parent1Q)] := by
  native_decide

theorem cancellation_r4_parent1_incoming :
    NeedleGeneralInverse.parents (cancellationR4Parent1+2) =
      [(0,cancellationR4Parent2Q)] := by
  native_decide

theorem cancellation_r4_parent2_incoming :
    NeedleGeneralInverse.parents (cancellationR4Parent2+2) =
      [(1,cancellationR4Parent3Q)] := by
  native_decide

theorem cancellation_r4_parent3_incoming :
    NeedleGeneralInverse.parents (cancellationR4Parent3+2) = [] := by
  native_decide

#eval (NeedleGeneralInverse.parents (cancellationFeeder3+2)).map Prod.fst
#eval (NeedleGeneralInverse.parents (cancellationFeeder4+2)).map Prod.fst
#eval (NeedleGeneralInverse.parents (cancellationR4Parent1+2)).map Prod.fst
#eval (NeedleGeneralInverse.parents (cancellationR4Parent2+2)).map Prod.fst
#eval (NeedleGeneralInverse.parents (cancellationR4Parent3+2)).map Prod.fst

/-- The generic exact fixed-target checker proves that the r=3 feeder
    cannot lie on the original blank-root orbit. -/
theorem cancellation_r3_root_check_false :
    NeedleRootDecisionCore.reverseCheck
      BB6.Agent20.SpaceNeedleRootDecision.finiteParents
      (cancellationFeeder3+1) cancellationFeeder3 = false := by
  native_decide

theorem cancellation_r3_not_reachable :
    ¬ ReachN cancellationFeeder3 := by
  intro hreach
  have htrue :=
    (BB6.Agent20.SpaceNeedleRootDecision.exact_root_target
      cancellationFeeder3).mpr hreach
  rw [cancellation_r3_root_check_false] at htrue
  contradiction

/-- The r=4 feeder has a unique reverse chain with valuation sequence
    4, 0, 1, after which the exact parent list is empty. It is therefore
    unreachable from the original blank root. -/
theorem cancellation_r4_root_check_false :
    NeedleRootDecisionCore.reverseCheck
      BB6.Agent20.SpaceNeedleRootDecision.finiteParents
      (cancellationFeeder4+1) cancellationFeeder4 = false := by
  native_decide

theorem cancellation_r4_not_reachable :
    ¬ ReachN cancellationFeeder4 := by
  intro hreach
  have htrue :=
    (BB6.Agent20.SpaceNeedleRootDecision.exact_root_target
      cancellationFeeder4).mpr hreach
  rw [cancellation_r4_root_check_false] at htrue
  contradiction

#print axioms cancellation_r3_source_step
#print axioms cancellation_r4_source_step
#print axioms cancellation_r3_not_reachable
#print axioms cancellation_r4_not_reachable
end BB6.Agent48.SpaceNeedleCancellationHoldouts
