import TerminalFirstForkClassification

set_option maxHeartbeats 0

namespace CascadeForcedThirdValuation
open CascadeResetInverse CascadeUniformFatal CascadeSweep

/-- Source-level third odd valuation is genuinely realizable in the
    narrow high-output window. This theorem uses the original,
    untruncated ResetParent grammar; in particular t=3 is NOT
    discarded in favor of a guessed maximal or minimal valuation.
    The arithmetic hypotheses are the direct uniform consequences of
    X=2*u+5 with a deep canonical #746 even-ray deficit. -/
theorem high_window_tthree_actual_parent
    (n p u d h : Nat)
    (hn : 257≤n)
    (hp : p=2^n)
    (hbig : 16*n+256<p)
    (hXlow : 511*p<64*(81*d))
    (hXhigh : 81*d<8*p+2*n+3)
    (hout : 2*u+5=81*d)
    (hdodd : d%2=1)
    (hparent : 16*d=p+h+n+2) :
    ResetParent h u := by
  have hindex : n=(n-3)+3 := by omega
  have hp8 : p=8*2^(n-3) := by
    calc
      p=2^n := hp
      _=2^((n-3)+3) := congrArg (fun j : Nat => 2^j) hindex
      _=8*2^(n-3) := by rw [Nat.pow_add];omega
  have hband : 6*2^(n-3)+1≤8*d ∧
      8*d≤8*2^(n-3)-1 := by
    constructor <;> omega
  right
  refine ⟨n-3,3,d,hdodd,?_,?_,?_⟩
  · simpa only [show (2:Nat)^3=8 by decide] using hband
  · simpa only [show (3:Nat)^(3+1)=81 by decide] using hout
  · simp only [show (2:Nat)^3=8 by decide]
    omega

#print axioms high_window_tthree_actual_parent
end CascadeForcedThirdValuation
