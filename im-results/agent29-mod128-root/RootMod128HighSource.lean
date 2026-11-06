import RootMod128Source
import RootMod128High

namespace BB6.Agent29New

/-- New all-time exclusion for an infinite two-parameter sector of the
original Machine C high stopping equation. This says nothing about
remaining high or low stopping indices. -/
theorem blank_no_high_stop_mod128 (j m k : Nat)
    (hm : 4≤m) (hj : j%8=5)
    (hres : (j+31)%128=(3*m)%128)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨hx,hs,hy⟩ := high_target_cylinder j m k hm hj hres hgate
  exact blank_no_two_link (2*j+3) k hx hs hy

#print axioms blank_no_high_stop_mod128
end BB6.Agent29New
