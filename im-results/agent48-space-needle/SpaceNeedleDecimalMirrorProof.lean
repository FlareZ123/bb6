import SpaceNeedleSourceMirror
import TerminalDecimalAll
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- Exact semantic proof over literal published scanEven and highLevelNext
definitions for arbitrarily high exponent decimal suffixes. This proves a
one-step predecessor exists within the high-level state space, and makes
no claim that it belongs to the blank-origin orbit. -/
theorem source_mirrored_every_decimal_suffix (e r bound : Nat) (hr : r < 10^e) :
    ∃ k d, bound ≤ k ∧ k%(10^e)=r ∧
      highLevelNext (.N d) = some (.N ((2:Nat)^k-2)) := by
  obtain ⟨k,q,v,hb,hm,heq⟩ := SpaceNeedleExp.every_decimal_suffix e r bound hr
  refine ⟨k,oddTower q v,hb,hm,?_⟩
  rw [original_step_on_oddTower]
  have hf := oddTower_factor q v
  simp only [Option.some.injEq, HighLevelState.N.injEq]
  omega

end BB6.Agent48.SpaceNeedle
#print axioms BB6.Agent48.SpaceNeedle.source_mirrored_every_decimal_suffix
