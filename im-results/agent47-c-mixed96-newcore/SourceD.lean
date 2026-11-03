import SourceBridge
import NewCoreD

set_option maxHeartbeats 0

namespace NewCore

theorem nextC_source_equal (a k c : Nat) :
    nextC (a,k,c) = BB6CLine.nextC (a,k,c) := by
  exact A4Backward.nextC_source_equal a k c

theorem source_blank_never_badD (s : Nat × Nat × Nat)
    (h : BB6CLine.Reach s) : ¬badD s.1 s.2.1 s.2.2 := by
  induction h with
  | init =>
      simp [badD,lowD]
  | next x y hx hstep ih =>
      rcases x with ⟨a,k,c⟩
      rcases y with ⟨a',k',c'⟩
      intro hb
      have he : nextC (a,k,c) = some (a',k',c') := by
        rw [nextC_source_equal]
        exact hstep
      exact ih (backward_stepD a k c a' k' c' he hb)

theorem source_no_cylinder_37_55 (a k : Nat)
    (ha : a%96=37) (hk : k%96=55)
    (h : BB6CLine.Reach (a,k,0)) : False := by
  have hh := source_blank_never_badD (a,k,0) h
  apply hh
  simp only [badD, show (0:Nat)<2 by omega, ↓reduceIte,lowD]
  left
  omega

theorem source_no_cylinder_85_7 (a k : Nat)
    (ha : a%96=85) (hk : k%96=7)
    (h : BB6CLine.Reach (a,k,0)) : False := by
  have hh := source_blank_never_badD (a,k,0) h
  apply hh
  simp only [badD, show (0:Nat)<2 by omega, ↓reduceIte,lowD]
  left
  omega

#print axioms nextC_source_equal
#print axioms source_blank_never_badD
#print axioms source_no_cylinder_37_55
#print axioms source_no_cylinder_85_7

end NewCore
