import Low124Sharp
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem blank_prefix_0 :
    BB6.Agent8Section.run secNext 0 (some (5,1))=some (5,1) := by decide
private theorem blank_prefix_1 :
    BB6.Agent8Section.run secNext 1 (some (5,1))=some (3,4) := by decide
private theorem blank_prefix_2 :
    BB6.Agent8Section.run secNext 2 (some (5,1))=some (4,7) := by decide
private theorem blank_prefix_3 :
    BB6.Agent8Section.run secNext 3 (some (5,1))=some (20,4) := by decide
private theorem blank_prefix_4 :
    BB6.Agent8Section.run secNext 4 (some (5,1))=some (12,10) := by decide

/-- True blank-origin corollary of the sharp four-level original-section
inverse barrier, valid for all rectangle parameters including b=0 and b=1. -/
theorem blank_no_rectangle_124_all (a b : Nat) :
    ¬ CReach (64*a+1) (128*b+124) := by
  rintro ⟨time,ht⟩
  by_cases hsmall : time<5
  · have hcases : time=0 ∨ time=1 ∨ time=2 ∨ time=3 ∨ time=4 := by omega
    rcases hcases with h|h|h|h|h
    · subst time
      rw [blank_prefix_0] at ht
      simp only [Option.some.injEq,Prod.mk.injEq] at ht
      omega
    · subst time
      rw [blank_prefix_1] at ht
      simp only [Option.some.injEq,Prod.mk.injEq] at ht
      omega
    · subst time
      rw [blank_prefix_2] at ht
      simp only [Option.some.injEq,Prod.mk.injEq] at ht
      omega
    · subst time
      rw [blank_prefix_3] at ht
      simp only [Option.some.injEq,Prod.mk.injEq] at ht
      omega
    · subst time
      rw [blank_prefix_4] at ht
      simp only [Option.some.injEq,Prod.mk.injEq] at ht
      omega
  · have heq : time=(time-5)+5 := by omega
    rw [heq] at ht
    exact (rectangle_124_all_start_sharp a b).2 (5,1) (time-5) ht

/-- Complete infinite two-dimensional source rectangle, with no
unnecessary counter-size threshold. -/
theorem blank_no_rectangle_124 (x y : Nat)
    (hx : x%64=1) (hy : y%128=124) : ¬ CReach x y := by
  have hxa : x=64*(x/64)+1 := by omega
  have hyb : y=128*(y/128)+124 := by omega
  rw [hxa,hyb]
  exact blank_no_rectangle_124_all (x/64) (y/128)

#print axioms rectangle_124_all_start_sharp
#print axioms blank_no_rectangle_124_all
#print axioms blank_no_rectangle_124
end BB6.Agent3
