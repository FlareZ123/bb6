import OddSpecialHigh
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Special

/-- One more authentic forced predecessor brings this residue family into
    the source-certified first odd-special cylinder. -/
theorem blank_no_special_lift_a (u v:Nat) (hv:1≤v) :
    ¬ BB6.Agent3.CReach (16*u+13) (128*v+22) := by
  intro hr
  have hh := (BB6.Agent46.six_even_right_blank_reach_iff
    (16*u+13) (128*v+22)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have hx : (16*u+13)+(128*v+22)-2=16*(u+8*v+2)+1 := by omega
  have hy : ((128*v+22)-2)/2=64*v+10 := by omega
  rw [hx,hy] at hh
  exact blank_no_special_a (u+8*v+2) v hv hh

/-- The second source-certified odd-special cylinder also has a forced
    predecessor family one dyadic level above. -/
theorem blank_no_special_lift_b (u v:Nat) :
    ¬ BB6.Agent3.CReach (16*u+5) (128*v+86) := by
  intro hr
  have hh := (BB6.Agent46.six_even_right_blank_reach_iff
    (16*u+5) (128*v+86)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have hx : (16*u+5)+(128*v+86)-2=16*(u+8*v+5)+9 := by omega
  have hy : ((128*v+86)-2)/2=64*v+42 := by omega
  rw [hx,hy] at hh
  exact blank_no_special_b (u+8*v+5) v hh

#print axioms blank_no_special_lift_a
#print axioms blank_no_special_lift_b
end BB6.Agent19Special
