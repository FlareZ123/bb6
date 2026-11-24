import ExactTime
import ERemaining
import DObsSourceCandidate
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 180000
set_option maxHeartbeats 0

namespace BB6.Agent35I5Root

open CryptidBoundary
open BB6.Agent19.Physical
open BB6.BoundaryPadding
open BB6.Portfolio

/-- Exact raw-step horizon from the authentic D3 blank root through the
    1711 regular returns from its unary I5 section. -/
def horizon : Nat := 15 + DRegular.accumulated 1711 DRegular.seed5

/-- The source section used by Agent35's arithmetic seed is exactly the
    five-one unary section used by Agent19's root-time bridge. -/
private theorem seed5_is_source_unary :
    DRegularSource.sourceSection DRegular.seed5 = sourceUnary 5 := by
  decide

/-- The previously conditional 1711-return transport, now instantiated with
    the already source-certified universal eleven-row contract. -/
theorem i5_checkpoint :
    BB6.BoundaryPadding.ObsEq
      (CryptidBoundary.run (DRegular.accumulated 1711 DRegular.seed5)
        (sourceUnary 5))
      (DRegularSource.sourceSection DRegular.terminal5) := by
  simpa [seed5_is_source_unary] using
    (DRegularSource.first1711_source BB6.ERemaining.source_contract)

/-- Extract the state component of physical observational equality. -/
private theorem obs_state {c d : CryptidBoundary.Cfg}
    (h : BB6.BoundaryPadding.ObsEq c d) : c.st = d.st := by
  change BB6.Padding.CfgEq
    (BB6.BoundaryPadding.represent c)
    (BB6.BoundaryPadding.represent d) at h
  exact h.2.2.2

/-- The authenticated 1711-return endpoint is still live in source state F. -/
theorem i5_checkpoint_state :
    (CryptidBoundary.run (DRegular.accumulated 1711 DRegular.seed5)
      (sourceUnary 5)).st = 5 := by
  have h := obs_state i5_checkpoint
  simpa [DRegularSource.sourceSection, CryptidBoundary.init, goL] using h

/-- One additional source transition from the certified endpoint is live:
    the endpoint is F scanning 0, so its next transition enters state E. -/
theorem i5_checkpoint_next_live :
    (CryptidBoundary.run
      (DRegular.accumulated 1711 DRegular.seed5 + 1)
      (sourceUnary 5)).st ≠ 6 := by
  have hObs := BB6.BoundaryPadding.source_congr 1 i5_checkpoint
  have hstate := obs_state hObs
  have hrun :
      CryptidBoundary.run
        (DRegular.accumulated 1711 DRegular.seed5 + 1)
        (sourceUnary 5) =
      CryptidBoundary.run 1
        (CryptidBoundary.run
          (DRegular.accumulated 1711 DRegular.seed5)
          (sourceUnary 5)) := by
    exact CryptidBoundary.run_add _ _ _
  rw [hrun]
  intro hbad
  have hright :
      (CryptidBoundary.run 1
        (DRegularSource.sourceSection DRegular.terminal5)).st ≠ 6 := by
    simp [CryptidBoundary.run, CryptidBoundary.step,
      DRegularSource.sourceSection, CryptidBoundary.init]
  exact hright (hstate.symm.trans hbad)

private theorem frozen_step (c : CryptidBoundary.Cfg) (h : c.st = 6) :
    CryptidBoundary.step c = c := by
  cases c with
  | mk l bit r st =>
    change st = 6 at h
    subst st
    cases bit <;> rfl

private theorem frozen_run (c : CryptidBoundary.Cfg) (n : Nat)
    (h : c.st = 6) : CryptidBoundary.run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change CryptidBoundary.run n (CryptidBoundary.step c) = c
    rw [frozen_step c h]
    exact ih

/-- A live endpoint excludes every earlier visit to the absorbing frozen state. -/
private theorem no_frozen_before_live_endpoint
    (c : CryptidBoundary.Cfg) (N n : Nat) (hn : n ≤ N)
    (hlive : (CryptidBoundary.run N c).st ≠ 6) :
    (CryptidBoundary.run n c).st ≠ 6 := by
  intro hst
  have ht : n + (N - n) = N := by omega
  have hrun :
      CryptidBoundary.run N c =
        CryptidBoundary.run (N - n) (CryptidBoundary.run n c) := by
    calc
      _ = CryptidBoundary.run (n + (N - n)) c :=
        congrArg (fun m => CryptidBoundary.run m c) ht.symm
      _ = _ := CryptidBoundary.run_add _ _ _
  have hfinal : (CryptidBoundary.run N c).st = 6 := by
    rw [hrun, frozen_run (CryptidBoundary.run n c) (N - n) hst]
    exact hst
  exact hlive hfinal

/-- No source checkpoint at or before the 1711-return endpoint is frozen. -/
theorem no_frozen_through_1711 (n : Nat)
    (hn : n ≤ DRegular.accumulated 1711 DRegular.seed5 + 1) :
    (CryptidBoundary.run n (sourceUnary 5)).st ≠ 6 :=
  no_frozen_before_live_endpoint (sourceUnary 5)
    (DRegular.accumulated 1711 DRegular.seed5 + 1) n hn
    i5_checkpoint_next_live

/-- The literal D3 rooted machine cannot halt before the exact 1711-return
    source checkpoint, including its initial 15-step blank-to-I5 prefix. -/
theorem parsed_D3_no_halt_through_1711 (n : Nat)
    (hn : n ≤ horizon) :
    ¬ BB6.Portfolio.haltsAt
      (BB6.Portfolio.parseRLE BB6.Portfolio.rleD3)
      (0 : BB6.Portfolio.State) n := by
  by_cases hlt : n < 15
  · intro hh
    have hh' : BB6.Portfolio.haltsAt BB6.Portfolio.D3
        (0 : BB6.Portfolio.State) n := by
      simpa only [BB6.Portfolio.parsed_D3_eq] using hh
    have hd0 := (BB6.Portfolio.D3_exact_halt_time n).mp hh'
    have hp := BB6.Portfolio.no_halt_before_prefix
      BB6.Portfolio.D0 (BB6.Portfolio.blank (1 : BB6.Portfolio.State))
      (BB6.Portfolio.F0Pure 5 (-3)) 15 n
      BB6.Portfolio.blank_root_B_to_I5 hd0
    omega
  · have hge : 15 ≤ n := by omega
    let k := n - 15
    have hk : k ≤ DRegular.accumulated 1711 DRegular.seed5 := by
      dsimp [k, horizon] at *
      omega
    have htime : 15 + k = n := by omega
    intro hh
    have hh' : BB6.Portfolio.haltsAt
        (BB6.Portfolio.parseRLE BB6.Portfolio.rleD3)
        (0 : BB6.Portfolio.State) (15 + k) := by
      simpa [htime] using hh
    have hfrozen :=
      (BB6.Agent19.Physical.parsed_D3_exact_source_time k).mp hh'
    exact no_frozen_through_1711 (k + 1) (by omega) hfrozen.2

/-- The exact root horizon has 1459 decimal digits. -/
theorem horizon_ge_10pow1458 : 10^1458 ≤ horizon := by
  decide

theorem horizon_lt_10pow1459 : horizon < 10^1459 := by
  decide

/-- Readable numerical form of the source-certified D3 blank-root lower bound. -/
theorem parsed_D3_no_halt_10pow1458 (n : Nat) (hn : n ≤ 10^1458) :
    ¬ BB6.Portfolio.haltsAt
      (BB6.Portfolio.parseRLE BB6.Portfolio.rleD3)
      (0 : BB6.Portfolio.State) n :=
  parsed_D3_no_halt_through_1711 n
    (Nat.le_trans hn horizon_ge_10pow1458)

#print axioms i5_checkpoint
#print axioms i5_checkpoint_next_live
#print axioms no_frozen_through_1711
#print axioms parsed_D3_no_halt_through_1711
#print axioms horizon_ge_10pow1458
#print axioms horizon_lt_10pow1459
#print axioms parsed_D3_no_halt_10pow1458

end BB6.Agent35I5Root
