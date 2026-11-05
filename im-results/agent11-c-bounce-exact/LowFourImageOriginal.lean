import BounceLowRangeOriginal
import BounceOddExact
import FastSectionDef
import Lean.Elab.Tactic.Omega
namespace BB6.Agent11Fast
open BB6.Agent46

def fourImageCriterion (a k x:Nat) : Prop :=
  if a=0 then
    if k=0 then False
    else if k=1 then x=0
    else ∃n:Nat, x+4=2^n*8 ∧ (2*k+1)+8+3*n=x+8
  else if a=1 then False
  else if k=0 then False
  else if 2*k≤a then x=a-2*k ∧ k=1
  else if a%2=0 then
    ∃n:Nat, x+4=2^n*(2*(a-1)+6) ∧
      (2*k-a+3)+(2*(a-1)+6)+3*n=x+8
  else False

theorem fourImage_exact (a k x:Nat):
  secNext (a,k)=some (x,4) ↔ fourImageCriterion a k x := by
  by_cases ha0:a=0
  · by_cases hk0:k=0
    · simp [fourImageCriterion,secNext,exactSection,ha0,hk0]
    · by_cases hk1:k=1
      · simp [fourImageCriterion,secNext,exactSection,ha0,hk0,hk1]
        constructor <;> intro h <;> exact h.symm
      · have h := bounce_odd_output_exact 1 (2*k+1) x 4 (by decide) (by decide)
        simpa [fourImageCriterion,secNext,exactSection,ha0,hk0,hk1]
          using h
  · by_cases ha1:a=1
    · by_cases hk0:k=0
      · simp [fourImageCriterion,secNext,exactSection,ha0,ha1,hk0]
      · by_cases hk1:k=1
        · simp [fourImageCriterion,secNext,exactSection,ha0,ha1,hk0,hk1]
        · by_cases hk2:k=2
          · simp [fourImageCriterion,secNext,exactSection,ha0,ha1,hk0,hk1,hk2]
          · by_cases hk3:k=3
            · simp [fourImageCriterion,secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3]
            · have hb:(bounce 4 (2*k-3)).2≠some (x,4) := by
                intro h
                have he:=bounce_even_three_or_high (2*k-3) 4 x 4 (by decide) h
                omega
              simp [fourImageCriterion,secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3,hb]
    · by_cases hk0:k=0
      · simp [fourImageCriterion,secNext,exactSection,ha0,ha1,hk0]
      · by_cases hreg:2*k≤a
        · simp [fourImageCriterion,secNext,exactSection,ha0,ha1,hk0,hreg]
          constructor
          · rintro ⟨hx,hy⟩
            omega
          · rintro ⟨hx,hk⟩
            constructor <;> omega
        · by_cases heven:a%2=0
          · have hkOdd:(a-1)%2=1 := by omega
            have h:=bounce_odd_output_exact (a-1) (2*k-a+3) x 4 hkOdd (by decide)
            simpa [fourImageCriterion,secNext,exactSection,ha0,ha1,hk0,hreg,heven]
              using h
          · have hkEven:(a-1)%2=0:=by omega
            have hb:(bounce (a-1) (2*k-a+3)).2≠some (x,4) := by
              intro h
              have hh:=bounce_even_three_or_high (2*k-a+3) (a-1) x 4 hkEven h
              omega
            simp [fourImageCriterion,secNext,exactSection,ha0,ha1,hk0,hreg,heven,hb]

#print axioms fourImage_exact
end BB6.Agent11Fast
