import Q185Affine
import GenericCritical

namespace BB6.Agent9Q185

/-- For every r, a genuine P1 critical reset gateway at n=2962+16384*r is unreachable from the blank seed. -/
theorem critical_2962_mod16384_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(185+1024*r)+2)-2*(16*(185+1024*r)+2)-10) := by
  apply BB6.Agent8Generic.critical_unreachable_of_shadow (185+1024*r)
    (by omega) (q185L0Nodes r) (q185L1Nodes r)
  · simp [q185L0Nodes] <;> omega
  · simp [q185L1Nodes] <;> omega
  · exact q185L0_closed r
  · exact q185L1_closed r
  · exact q185L0_small r
  · exact q185L1_small r
  · exact q185L0_no256 r
  · exact q185L1_no256 r

#print axioms critical_2962_mod16384_unreachable
end BB6.Agent9Q185
