import Mathlib
import SpaceNeedleClosed
import SpaceNeedlePotentialSource
import MixedPotentialGeneral
import NeedleMixedPotentialSource
import NoUpward

namespace BB6.Agent20NoUpwardSource
open BB6.Agent20NoUpward
open BB6.Agent20NeedlePotentialSource
open BB6.Agent20NeedleMixedPotentialSource

/-- A target may admit two different inverse valuations, but its
    lower-valuation parent cannot in turn have an incoming edge of
    the higher valuation, uniformly over all 2 <= v < w. -/
theorem no_upward_source {v w e f p q : Nat}
    (hv : 2 ≤ v) (hvw : v < w)
    (hvparent : SourceChain v 1 e f)
    (hwtarget : SourceChain w 1 e p)
    (hwparent : SourceChain w 1 f q) : False := by
  have horder : 2^v*(2*v-3) ≤ 2^w*(2*w-3) :=
    Nat.le_of_lt (potential_correction_strict hv hvw)
  have hnot : ¬ ((2^(w+1)+3) ∣
      3*(2^w*(2*w-3)-2^v*(2*v-3))) :=
    no_upward_division v w hv hvw
  have hnotInt : ¬ (((2^(w+1)+3 : Nat) : Int) ∣
      3*(((2^w*(2*w-3) : Nat) : Int)-
         ((2^v*(2*v-3) : Nat) : Int))) := by
    intro hx
    have hcast : ((2^w*(2*w-3)-2^v*(2*v-3) : Nat) : Int) =
      ((2^w*(2*w-3) : Nat) : Int) -
      ((2^v*(2*v-3) : Nat) : Int) := by
      exact Nat.cast_sub horder
    rw [←hcast] at hx
    have hnat : ((2^(w+1)+3) : Nat) ∣
        3*(2^w*(2*w-3)-2^v*(2*v-3)) := by
      exact_mod_cast hx
    exact hnot hnat
  exact no_immediate_switch hv (by omega) hvparent hwtarget hwparent hnotInt

#print axioms no_upward_source
end BB6.Agent20NoUpwardSource
