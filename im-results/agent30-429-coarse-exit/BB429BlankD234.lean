import BB429Resonance234All

namespace BB429.CoarseExit

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

/-- Exact authentic-blank entry into the first positive Cantor resonance.
    The #429 accelerated blank orbit reaches the prepared d=234 state at
    scale m=2 after 4389 macro steps.  This is kernel reduction by decide,
    not an external trace assumption. -/
theorem blank_hits_d234_m2 :
    run 4389 (0,0) = some (prepared 2 234) := by
  decide

/-- Root-connected consequence of the complete d=234 closure: after entering
    prepared(2,234), the authentic blank orbit reaches another section within
    the all-scale theorem's 49-step bound. -/
theorem blank_d234_section :
    ∃ k p, 4389<k ∧ k≤4438 ∧
      run k (0,0)=some p ∧ isSection p := by
  obtain ⟨k,p,hk,hk49,hr,hs⟩ := d234_all 2
  refine ⟨4389+k,p,by omega,?_,?_,hs⟩
  · omega
  · rw [run_add,blank_hits_d234_m2,Option.bind_some,hr]

#print axioms blank_hits_d234_m2
#print axioms blank_d234_section

end BB429.CoarseExit
