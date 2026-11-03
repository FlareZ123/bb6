import SourceBridge
import NewCoreC

set_option maxHeartbeats 0

namespace NewCore

theorem nextC_source_equal (a k c : Nat) :
    nextC (a,k,c) = BB6CLine.nextC (a,k,c) := by
  exact A4Backward.nextC_source_equal a k c

theorem source_blank_never_badC (s : Nat × Nat × Nat)
    (h : BB6CLine.Reach s) : ¬badC s.1 s.2.1 s.2.2 := by
  induction h with
  | init =>
      simp [badC,lowC]
  | next x y hx hstep ih =>
      rcases x with ⟨a,k,c⟩
      rcases y with ⟨a',k',c'⟩
      intro hb
      have he : nextC (a,k,c) = some (a',k',c') := by
        rw [nextC_source_equal]
        exact hstep
      exact ih (backward_stepC a k c a' k' c' he hb)

theorem source_no_cylinder_5_55 (a k : Nat)
    (ha : a%96=5) (hk : k%96=55)
    (h : BB6CLine.Reach (a,k,0)) : False := by
  have hh := source_blank_never_badC (a,k,0) h
  apply hh
  simp only [badC, show (0:Nat)<2 by omega, ↓reduceIte,lowC]
  left
  omega

theorem source_no_cylinder_53_7 (a k : Nat)
    (ha : a%96=53) (hk : k%96=7)
    (h : BB6CLine.Reach (a,k,0)) : False := by
  have hh := source_blank_never_badC (a,k,0) h
  apply hh
  simp only [badC, show (0:Nat)<2 by omega, ↓reduceIte,lowC]
  left
  omega

#print axioms nextC_source_equal
#print axioms source_blank_never_badC
#print axioms source_no_cylinder_5_55
#print axioms source_no_cylinder_53_7

end NewCore
