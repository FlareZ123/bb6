import ValuationSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34Valuation
open BB6.Agent46

/-- Exact original high-source y=3 exit has the same strict valuation
    and parity controls as high odd-source outputs with y>=5, but uses
    the shifted x+6 rather than x+y+1. -/
theorem odd_high_y_three_depth_parity (a k x v u : Nat)
    (ha : 3 ≤ a) (hk : 0 < k) (hregion : a < 2*k) (hodd : a%2=1)
    (hfact : x+6=2^v*(2*u+1))
    (hedge : secNext (a,k)=some (x,3)) :
    ∃ n : Nat, n+2 ≤ v ∧ n%2=x%2 := by
  have hi := (section_preimage_all_iff a k x 3).mp hedge
  have ha0 : a≠0 := by omega
  have ha1 : a≠1 := by omega
  have hk0 : k≠0 := by omega
  have hlow : ¬2*k≤a := by omega
  have heven : a%2≠0 := by omega
  simp only [sectionPreimageAll, if_neg ha0, if_neg ha1, if_neg hk0,
    if_neg hlow, if_neg heven] at hi
  rcases hi with ⟨_,n,hs,hcost⟩ | ⟨h5,_⟩
  · have hsum : 2^n*(2*a+6)=2^v*(2*u+1) := by
      have hs' : 2*(a-1)+8=2*a+6 := by omega
      rw [hs'] at hs
      exact hs.symm.trans hfact
    have hcost' : 2*k+a+3*n=x+1 := by omega
    have hparity : n%2=x%2 := by omega
    exact ⟨n,odd_input_depth_val a n v u hodd hsum,hparity⟩
  · omega

#print axioms odd_high_y_three_depth_parity
end BB6.Agent34Valuation
