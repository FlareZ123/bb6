import SpaceNeedleClosed
import TerminalDecimalAll
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- Every decimal exponent suffix is represented arbitrarily high by a
terminal power of two with a one-step predecessor in the published
high-level Space Needle transition. No assertion of blank-root
reachability of those predecessors is made. -/
theorem every_decimal_suffix_has_predecessor (e r bound : Nat)
    (hr : r < 10^e) :
    ∃ k d, bound ≤ k ∧ k%(10^e)=r ∧
       highLevelNext (.N d) = some (.N ((2:Nat)^k-2)) := by
  obtain ⟨k,q,v,hb,hm,heq⟩ := SpaceNeedleExp.every_decimal_suffix e r bound hr
  refine ⟨k,oddTower q v,hb,hm,?_⟩
  apply (highLevelNext_iff_oddTower _ _).mpr
  refine ⟨q,v,rfl,?_⟩
  have hf := oddTower_factor q v
  omega

end BB6.Agent48.SpaceNeedle
#print axioms BB6.Agent48.SpaceNeedle.every_decimal_suffix_has_predecessor
