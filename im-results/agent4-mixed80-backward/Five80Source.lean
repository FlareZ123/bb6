import Five80Stop
import SourceBridge
set_option maxHeartbeats 0
namespace A4Five80

theorem source_blank_never_bad80 (s : Nat × Nat × Nat)
    (hr : BB6CLine.Reach s) : ¬bad s.1 s.2.1 s.2.2 := by
  induction hr with
  | init => exact root_good
  | next x y hx hstep ih =>
    rcases x with ⟨a,k,c⟩
    rcases y with ⟨a',k',c'⟩
    intro hb
    have he : A4Backward.nextC (a,k,c) = some (a',k',c') := by
      rw [A4Backward.nextC_source_equal]
      exact hstep
    exact ih (backward_step a k c a' k' c' he hb)

theorem source_no80 (a k : Nat)
    (ha:a%80=41) (hk:k%80=15) :
    ¬ BB6CLine.Reach (a,k,0) := by
  intro hr
  apply source_blank_never_bad80 (a,k,0) hr
  simp only [bad,low]
  exact Or.inl ⟨ha,by simpa using hk⟩

theorem source_stop_m11_u60_unreachable (u m k:Nat)
    (hu:u%80=60) (hm:m%80=11)
    (eqn:k+u+3*m+4=4^(m+1)*(u+2)) :
    ¬ BB6CLine.Reach (2*u+1,k,0) := by
  obtain ⟨ha,hk⟩ := stop_parameters_mod80 u m k hu hm eqn
  exact source_no80 (2*u+1) k ha hk

#print axioms source_blank_never_bad80
#print axioms source_no80
#print axioms source_stop_m11_u60_unreachable
end A4Five80
