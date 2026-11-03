import SpaceNeedleClosed
import TerminalMod1000
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- For every residue modulo 1000 and every bound, there is a larger
power-of-two terminal target whose one-step predecessor exists in the
authentic high-level Space Needle transition. This does not establish
blank-tape reachability of that predecessor. -/
theorem every_mod1000_has_predecessor (r bound : Nat) (hr : r < 1000) :
    ∃ k d, bound ≤ k ∧ k%1000=r ∧
      highLevelNext (.N d) = some (.N ((2:Nat)^k-2)) := by
  obtain ⟨k,q,v,hb,hm,heq⟩ := SpaceNeedleExp.thousand_predecessors r bound hr
  refine ⟨k,oddTower q v,hb,hm,?_⟩
  apply (highLevelNext_iff_oddTower _ _).mpr
  refine ⟨q,v,rfl,?_⟩
  have hf := oddTower_factor q v
  omega

end BB6.Agent48.SpaceNeedle
#print axioms BB6.Agent48.SpaceNeedle.every_mod1000_has_predecessor
