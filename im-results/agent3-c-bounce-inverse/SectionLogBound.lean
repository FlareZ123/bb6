import BounceLogBound
import FastSectionDef
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Every one-step original Machine C section output has a finite,
    logarithmically depth-bounded, explicitly arithmetic inverse witness.
    This predicate deliberately DOES NOT call the recursive source bounce. -/
def sectionBounded (a k x y : Nat) : Prop :=
  if a=0 then
    if k=0 then False
    else if k=1 then x=0 ∧ y=4
    else boundedBounce 1 (2*k+1) x y
  else if a=1 then
    if k=0 then x=5 ∧ y=1
    else if k=1 then x=2 ∧ y=3
    else if k=2 then x=2 ∧ y=5
    else if k=3 then x=0 ∧ y=7
    else boundedBounce 4 (2*k-3) x y
  else if k=0 then x=a-2 ∧ y=2
  else if 2*k≤a then x=a-2*k ∧ y=2*k+2
  else boundedBounce (a-1) (2*k-a+3) x y

/-- Exact original-source section iff a finite bounded arithmetic
    disjunction. The universal bounce witness depth is bounded by
    Nat.log2 (x+y+6), irrespective of the size of a or k. -/
theorem section_bounded_exact (a k x y : Nat) :
    secNext (a,k)=some (x,y) ↔ sectionBounded a k x y := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,sectionBounded,ha0,hk0]
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,sectionBounded,ha0,hk0,hk1]
        constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
      · have hb := bounce_full_log_bounded 1 (2*k+1) x y
        simpa [secNext,exactSection,sectionBounded,ha0,hk0,hk1] using hb
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,sectionBounded,ha0,ha1,hk0]
        constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,sectionBounded,ha0,ha1,hk0,hk1]
          constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,sectionBounded,ha0,ha1,hk0,hk1,hk2]
            constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,sectionBounded,ha0,ha1,hk0,hk1,hk2,hk3]
              constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
            · have hb := bounce_full_log_bounded 4 (2*k-3) x y
              simpa [secNext,exactSection,sectionBounded,ha0,ha1,hk0,hk1,hk2,hk3] using hb
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,sectionBounded,ha0,ha1,hk0]
        constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
      · by_cases hlow : 2*k≤a
        · simp [secNext,exactSection,sectionBounded,ha0,ha1,hk0,hlow]
          constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
        · have hb := bounce_full_log_bounded (a-1) (2*k-a+3) x y
          simpa [secNext,exactSection,sectionBounded,ha0,ha1,hk0,hlow] using hb

/-- Executable arithmetic-only check of a single section edge. Natural
    bounded existential synthesis is constructive and needs no classical
    decidability postulate. -/
def boundedEdge (a k x y : Nat) : Bool := by
  exact @decide (sectionBounded a k x y)
    (by unfold sectionBounded boundedBounce; infer_instance)

theorem boundedEdge_correct (a k x y : Nat) :
    boundedEdge a k x y = true ↔ secNext (a,k)=some (x,y) := by
  simp [boundedEdge,decide_eq_true_eq]
  exact (section_bounded_exact a k x y).symm

#print axioms section_bounded_exact
#print axioms boundedEdge_correct
end BB6.Agent3
