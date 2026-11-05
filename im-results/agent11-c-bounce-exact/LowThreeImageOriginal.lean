import BounceLowRangeOriginal
import FastSectionDef
import Lean.Elab.Tactic.Omega
namespace BB6.Agent11Fast
open BB6.Agent46

def threeImageCriterion (a k x:Nat) : Prop :=
  if a=0 then False
  else if a=1 then
    if k=0 then False
    else if k=1 then x=2
    else if k=2 then False
    else if k=3 then False
    else ∃ n:Nat, x+6=2^n*16 ∧ (2*k-3)+14+3*n=x+8
  else if k=0 then False
  else if 2*k≤a then False
  else if a%2=0 then False
  else ∃n:Nat, x+6=2^n*(2*(a-1)+8) ∧
    (2*k-a+3)+(2*(a-1)+6)+3*n=x+8

theorem threeImage_exact (a k x:Nat):
    secNext (a,k)=some (x,3) ↔ threeImageCriterion a k x := by
  by_cases ha0:a=0
  · by_cases hk0:k=0
    · simp [threeImageCriterion,secNext,exactSection,ha0,hk0]
    · by_cases hk1:k=1
      · simp [threeImageCriterion,secNext,exactSection,ha0,hk0,hk1]
      · have ho := bounce_odd_min_four (2*k+1) 1 x 3 (by decide)
        have hno:(bounce 1 (2*k+1)).2≠some (x,3) := by
          intro h
          have hh:=ho h
          omega
        simp [threeImageCriterion,secNext,exactSection,ha0,hk0,hk1,hno]
  · by_cases ha1:a=1
    · by_cases hk0:k=0
      · simp [threeImageCriterion,secNext,exactSection,ha0,ha1,hk0]
      · by_cases hk1:k=1
        · simp [threeImageCriterion,secNext,exactSection,ha0,ha1,hk0,hk1]
          constructor <;> intro h <;> exact h.symm
        · by_cases hk2:k=2
          · simp [threeImageCriterion,secNext,exactSection,ha0,ha1,hk0,hk1,hk2]
          · by_cases hk3:k=3
            · simp [threeImageCriterion,secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3]
            · have he:=bounce_three_exact 4 (2*k-3) x (by decide)
              simpa [threeImageCriterion,secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3]
                using he
    · by_cases hk0:k=0
      · simp [threeImageCriterion,secNext,exactSection,ha0,ha1,hk0]
      · by_cases hreg:2*k≤a
        · simp [threeImageCriterion,secNext,exactSection,ha0,ha1,hk0,hreg]
          omega
        · by_cases heven:a%2=0
          · have hkOdd:(a-1)%2=1 := by omega
            have hno:(bounce (a-1) (2*k-a+3)).2≠some (x,3) := by
              intro h
              have hh:=bounce_odd_min_four (2*k-a+3) (a-1) x 3 hkOdd h
              omega
            simp [threeImageCriterion,secNext,exactSection,ha0,ha1,hk0,hreg,
              heven,hno]
          · have hkEven:(a-1)%2=0 := by omega
            have he:=bounce_three_exact (a-1) (2*k-a+3) x hkEven
            simpa [threeImageCriterion,secNext,exactSection,ha0,ha1,hk0,hreg,
              heven] using he

#print axioms threeImage_exact
end BB6.Agent11Fast
