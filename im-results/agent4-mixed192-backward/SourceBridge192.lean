import BackwardMod192
import CLine

set_option maxHeartbeats 0

namespace A4Backward192

/-- Transport the universal reverse core to the unchanged original Machine C acceleration. -/
theorem source_blank_never_bad192 (s : Nat × Nat × Nat)
    (h : BB6CLine.Reach s) : ¬ bad s.1 s.2.1 s.2.2 := by
  induction h with
  | init =>
      simp [bad, low]
  | next x y hx hstep ih =>
      rcases x with ⟨a,k,c⟩
      rcases y with ⟨a',k',c'⟩
      intro hb
      have he : A4Backward.nextC (a,k,c) = some (a',k',c') := by
        rw [A4Backward.nextC_source_equal]
        exact hstep
      exact ih (backward_step a k c a' k' c' he hb)

theorem source_no_35_61 (a k : Nat)
    (ha : a % 192 = 35) (hk : k % 192 = 61)
    (h : BB6CLine.Reach (a,k,0)) : False := by
  exact source_blank_never_bad192 (a,k,0) h (by simp [bad,low,ha,hk])

#print axioms source_blank_never_bad192
#print axioms source_no_35_61

end A4Backward192
