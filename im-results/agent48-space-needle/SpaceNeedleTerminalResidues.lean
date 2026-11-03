import SpaceNeedleClosed
import TerminalResiduesArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- Source-dependent lift: a generic arithmetic predecessor is a genuine
one-call predecessor for the original Space Needle Collatz acceleration. -/
theorem source_lift (k : Nat) (h : SpaceNeedleExp.HasPredecessor k) :
    ∃ d, highLevelNext (.N d) = some (.N ((2:Nat)^k-2)) := by
  rcases h with ⟨q,hq⟩ | ⟨q,hq⟩
  · refine ⟨oddTower q 0, ?_⟩
    apply (highLevelNext_iff_oddTower _ _).mpr
    refine ⟨q,0,rfl,?_⟩
    simp only [oddTower] at *
    omega
  · refine ⟨oddTower q 11, ?_⟩
    apply (highLevelNext_iff_oddTower _ _).mpr
    refine ⟨q,11,rfl,?_⟩
    have hf := oddTower_factor q 11
    omega

/-- Every exponent residue modulo ten has arbitrarily large terminal
power targets with at least one high-level predecessor. This does not
assert that the predecessor belongs to the real blank-start orbit. -/
theorem every_mod_ten_has_predecessor (r bound : Nat) (hr : r < 10) :
    ∃ k d, bound ≤ k ∧ k%10=r ∧
       highLevelNext (.N d) = some (.N ((2:Nat)^k-2)) := by
  obtain ⟨hb,hm,hp⟩ := SpaceNeedleExp.selectK_correct r bound hr
  obtain ⟨d,hd⟩ := source_lift (SpaceNeedleExp.selectK r bound) hp
  exact ⟨SpaceNeedleExp.selectK r bound,d,hb,hm,hd⟩

end BB6.Agent48.SpaceNeedle
#print axioms BB6.Agent48.SpaceNeedle.every_mod_ten_has_predecessor
