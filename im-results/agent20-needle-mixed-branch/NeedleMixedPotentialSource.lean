import Mathlib
import SpaceNeedleClosed
import IndexPotential
import SpaceNeedlePotentialSource
import MixedPotentialGeneral

namespace BB6.Agent20NeedleMixedPotentialSource
open BB6.Agent20MixedPotentialGeneral
open BB6.Agent20NeedlePotentialSource
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- Fully original-source mixed-label inverse-branch restriction, uniformly
    for all valuations v,w >= 2 and every reverse depth k. -/
theorem mixed_source_gap {v w k e f p q : Nat}
    (hv : 2 ≤ v) (hw : 2 ≤ w)
    (hV : SourceChain v k e f)
    (hWtarget : SourceChain w 1 e p)
    (hWparent : SourceChain w 1 f q) :
    ((2^(w+1)+3 : Nat) : Int) ∣
      (((2^(v+1)+3 : Nat) : Int)^k -
       ((2^(v+1) : Nat) : Int)^k) *
      (((2^w*(2*w-3) : Nat) : Int) -
       ((2^v*(2*v-3) : Nat) : Int)) := by
  have hp := allValuationsPotential hv hV
  have ht := allValuationsSource hw hWtarget
  have hf := allValuationsSource hw hWparent
  exact gap_from_potential hp ht hf

/-- In particular, two admissible valuation labels cannot interleave
    immediately when their cross-fixed-point gap is nonzero modulo D_w. -/
theorem no_immediate_switch {v w e f p q : Nat}
    (hv : 2 ≤ v) (hw : 2 ≤ w)
    (hV : SourceChain v 1 e f)
    (hWtarget : SourceChain w 1 e p)
    (hWparent : SourceChain w 1 f q)
    (hgap : ¬ (((2^(w+1)+3 : Nat) : Int) ∣
      3*(((2^w*(2*w-3) : Nat) : Int) -
         ((2^v*(2*v-3) : Nat) : Int)))) : False := by
  have h := mixed_source_gap hv hw hV hWtarget hWparent
  have heq : (2^(v+1)+3 : Nat) = 2^(v+1)+3 := rfl
  have h' : (((2^(w+1)+3 : Nat) : Int)) ∣
      3*(((2^w*(2*w-3) : Nat) : Int) -
         ((2^v*(2*v-3) : Nat) : Int)) := by
    convert h using 1 <;> norm_num [pow_one] <;> ring
  exact hgap h'

/-- Exact source-connected mixed-word residue transfer for one edge.
    The alternate label w need not be the current state's valuation. -/
theorem source_cross_step {v w q e : Nat}
    (hv : 2 ≤ v) (hw : 2 ≤ w)
    (he : highLevelNext (.N (oddTower q v))=some (.N e)) :
    (((2^(v+1)+3 : Nat) : Int)) *
      (3*((oddTower q v+2 : Nat) : Int) +
        ((2^w*(2*w-3) : Nat) : Int)) =
    (((2^(v+1) : Nat) : Int)) *
      (3*((e+2 : Nat) : Int) +
        ((2^w*(2*w-3) : Nat) : Int)) +
    3*(((2^w*(2*w-3) : Nat) : Int) -
       ((2^v*(2*v-3) : Nat) : Int)) := by
  have hs : SourceChain v 1 e (oddTower q v) :=
    SourceChain.step q he (SourceChain.zero _)
  have hp : (2^(v+1)) *
      (3*(e+2)+2^v*(2*v-3)) =
      (2^(v+1)+3) *
      (3*(oddTower q v+2)+2^v*(2*v-3)) := by
    simpa using allValuationsPotential hv hs
  exact cross_step_identity (by rfl) hp

#print axioms source_cross_step

#print axioms mixed_source_gap
#print axioms no_immediate_switch
end BB6.Agent20NeedleMixedPotentialSource
