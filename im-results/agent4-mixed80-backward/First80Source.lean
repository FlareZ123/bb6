import First80
import SourceBridge
set_option maxHeartbeats 0
namespace A4First80

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

theorem source_no_first80 (k : Nat) (hk : k%80=71) :
    ¬BB6CLine.Reach (1,k,0) := by
  intro hr
  apply source_blank_never_bad80 (1,k,0) hr
  simp only [bad,low]
  exact Or.inl ⟨by decide,by simpa using hk⟩

#print axioms source_blank_never_bad80
#print axioms source_no_first80
end A4First80
