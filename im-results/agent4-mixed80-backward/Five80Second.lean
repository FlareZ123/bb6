import Five80Source
set_option maxHeartbeats 0
namespace A4Five80

theorem source_stop_m51_u20_unreachable (u m k:Nat)
    (hu:u%80=20) (hm:m%80=51)
    (eqn:k+u+3*m+4=4^(m+1)*(u+2)) :
    ¬ BB6CLine.Reach (2*u+1,k,0) := by
  obtain ⟨ha,hk⟩ := stop_parameters_mod80_20_51 u m k hu hm eqn
  exact source_no80 (2*u+1) k ha hk

#print axioms source_stop_m51_u20_unreachable
end A4Five80
