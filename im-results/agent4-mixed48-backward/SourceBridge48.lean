import BackwardMod48
import SourceBridge
set_option maxHeartbeats 0
namespace A4Backward48

theorem source_blank_never_bad48 (s : Nat × Nat × Nat)
    (h : BB6CLine.Reach s) : ¬ bad s.1 s.2.1 s.2.2 := by
  induction h with
  | init =>
      simp [bad,low]
  | next x y hx hstep ih =>
      rcases x with ⟨a,k,c⟩
      rcases y with ⟨a',k',c'⟩
      intro hb
      have he : A4Backward.nextC (a,k,c) = some (a',k',c') := by
        rw [A4Backward.nextC_source_equal]
        exact hstep
      exact ih (backward_step a k c a' k' c' he hb)

theorem source_no_low48 (a k : Nat)
    (hres : (a%16=3 ∧ k%24=7) ∨ (a%16=11 ∧ k%24=19))
    (h : BB6CLine.Reach (a,k,0)) : False := by
  apply source_blank_never_bad48 (a,k,0) h
  simpa [bad,low] using hres

#print axioms source_blank_never_bad48
#print axioms source_no_low48
end A4Backward48
