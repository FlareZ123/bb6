import SourceCostCombinators
import SourceExactPureBB424
import SourceExactPureDL424
import SourceExactPureCB424

/-!
# F424's complete exact original-Turing-machine cost soundness theorem

This is the concrete instantiation of the source-direct `ExactSymStep`
proof obligation. The proof is structurally only four cases; all machinery
is discharged in the three source-mode exact-cost modules, which use original
machine-specific 1,3,5,... and repeated-block primitive `ReachesIn` lemmas.

Do not treat this file as verified until full import-chain CI succeeds.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.SymRunEngine
open BB6.Agent11.SourceCost

namespace BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution

theorem sourcePure424_exact : ExactSymStep target_tm true := by
  intro s
  rcases s with ⟨mode,L,R⟩
  cases mode with
  | BB =>
    simpa only [costPure, stepPure] using sourcePureBB_exact L R
  | DL =>
    simpa only [costPure, stepPure] using sourcePureDL_exact L R
  | CB =>
    simpa only [costPure, stepPure] using sourcePureCB_exact L R
  | HALT =>
    rfl

/-- Source-rooted exact primitive-time induction for all fixed iteration
    counts, without any remaining `ExactSymStep` hypothesis. -/
theorem sourceIter424_exact (n : Nat) (s : SymState) :
    multiStep target_tm (evalSym target_tm s) (costIter true n s) =
      some (evalSym target_tm (iterStep stepPure n s)) :=
  costIter_exact_reaches sourcePure424_exact n s

#print axioms sourcePure424_exact
#print axioms sourceIter424_exact

end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution
