import OneLCFast
namespace BB6.Agent4E0OneLCLate
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem joinExact (a n k t : Nat) (x y z : Fast) (ht : n+k=t)
    (h : runF a n x=some y) (g : runF a k y=some z) : runF a t x=some z := by
  subst t
  exact runF_join h g
#print axioms joinExact
end BB6.Agent4E0OneLCLate
