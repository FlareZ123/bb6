import W2JuncFullCount
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2Physical

open BB429OddExcursion BB429FinishScanEDelta
open BB429W4CZeroCount BB429W2JuncFullCount
open BB429PhysicalBridge BB6Coverage

/-- The C/0 monitor is observational: discard its count to obtain
    the original unguarded source execution. No finite tape cutoff. -/
theorem runCount_to_run (n : Nat) (c d : Zipper) (k : Nat)
    (h : runCount n c = some (d,k)) : BB429OddExcursion.run n c = some d := by
  induction n generalizing c d k with
  | zero =>
      simp only [runCount,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      rfl
  | succ n ih =>
      simp only [runCount] at h
      cases hs : one c with
      | none => simp [hs] at h
      | some p =>
          simp only [hs,Option.bind_some] at h
          cases hn : runCount n p with
          | none => simp [hn] at h
          | some x =>
              rcases x with ⟨z,j⟩
              simp only [hn,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨hzd,hjk⟩
              subst d
              simp only [BB429OddExcursion.run,hs,Option.bind_some]
              exact ih p z j hn

/-- Every physical tape exactly representing the even right-two source
    chart completes its full return in the original six-state machine. -/
theorem physical_w2_even_complete (k : Nat) (c : Config)
    (hrep : Represents (junc 0 (2*k) 2) c) :
    ∃ c', BB6Coverage.run target429 (38*k+204) c = some c' ∧
      Represents (junc 0 0 (4*k+18)) c' := by
  apply source_run_rep (38*k+204) (junc 0 (2*k) 2) c hrep
    (junc 0 0 (4*k+18))
  exact runCount_to_run (38*k+204) (junc 0 (2*k) 2)
    (junc 0 0 (4*k+18)) 2 (junc0_w2_all_even_count k)

/-- The analogous complete odd right-two physical passage. -/
theorem physical_w2_odd_complete (k : Nat) (c : Config)
    (hrep : Represents (junc 0 (2*k+1) 2) c) :
    ∃ c', BB6Coverage.run target429 (44*k+266) c = some c' ∧
      Represents (junc 0 0 (4*k+24)) c' := by
  apply source_run_rep (44*k+266) (junc 0 (2*k+1) 2) c hrep
    (junc 0 0 (4*k+24))
  exact runCount_to_run (44*k+266) (junc 0 (2*k+1) 2)
    (junc 0 0 (4*k+24)) 3 (junc0_w2_all_odd_count k)

#print axioms runCount_to_run
#print axioms physical_w2_even_complete
#print axioms physical_w2_odd_complete

end BB429W2Physical
