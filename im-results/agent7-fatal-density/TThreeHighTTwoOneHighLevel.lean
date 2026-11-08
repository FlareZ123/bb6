import TThreeHighTTwoOne
import HighLevel746Underflow
set_option maxHeartbeats 0

namespace CascadeHighTTwo

theorem gap_odd_parent_has_highlevel_underflow (g:Nat) (h:GapOddParent g) :
  ∃x l t z, CascadeSweep.ReachC (2,0) (x,0) ∧ z%2=1 ∧
    6*2^l+1≤2^t*z ∧ 2^t*z≤8*2^l-1 ∧
    2*g+5=3^(t+1)*z ∧
    2*(2^t*z)=8*2^l+x+l+5 ∧
    Agent7HighLevel746.Steps
      (.C (2^t*z-3) 2) (.C g 0) := by
  rcases h with ⟨x,l,t,z,hx,hz,hlow,hup,hnum,heq⟩
  refine ⟨x,l,t,z,hx,hz,hlow,hup,hnum,heq,?_⟩
  exact Agent7HighLevel746.odd_parent_underflow_path g l t z hz hlow hnum

#print axioms gap_odd_parent_has_highlevel_underflow
end CascadeHighTTwo
