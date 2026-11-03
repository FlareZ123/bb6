import BackwardModB
import SourceBridge

set_option maxHeartbeats 0
namespace A4BackwardB

theorem source_blank_never_badB (s : Nat × Nat × Nat)
    (h : BB6CLine.Reach s) : ¬badB s.1 s.2.1 s.2.2 := by
  induction h with
  | init => simp [badB,lowB]
  | next x y hx hstep ih =>
      rcases x with ⟨a,k,c⟩
      rcases y with ⟨a',k',c'⟩
      intro hb
      have he : A4Backward.nextC (a,k,c) = some (a',k',c') := by
        rw [A4Backward.nextC_source_equal]
        exact hstep
      exact ih (backward_step a k c a' k' c' he hb)

theorem source_no_cylinder_29_79 (a k : Nat)
    (ha : a%96=29) (hk : k%96=79)
    (h : BB6CLine.Reach (a,k,0)) : False := by
  have hh := source_blank_never_badB (a,k,0) h
  apply hh
  simp [badB,lowB,ha,hk]

theorem source_no_cylinder_77_31 (a k : Nat)
    (ha : a%96=77) (hk : k%96=31)
    (h : BB6CLine.Reach (a,k,0)) : False := by
  have hh := source_blank_never_badB (a,k,0) h
  apply hh
  simp [badB,lowB,ha,hk]

#print axioms source_blank_never_badB
#print axioms source_no_cylinder_29_79
#print axioms source_no_cylinder_77_31
end A4BackwardB
