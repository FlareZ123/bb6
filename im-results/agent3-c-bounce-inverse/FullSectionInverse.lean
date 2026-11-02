import BounceEvenExact
import BounceOddExact
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Complete exact predecessor predicate for a section output with y>=5.
    Each recursive source branch is represented by two integer equations
    sharing one unbounded recursion-depth witness n. -/
def sectionPreimageCriterion (a k x y : Nat) : Prop :=
  if a=0 then
    if k=0 then False
    else if k=1 then x=0 ∧ y=4
    else ∃ n : Nat,
      x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y
  else if a=1 then
    if k=0 then False
    else if k=1 then False
    else if k=2 then x=2 ∧ y=5
    else if k=3 then x=0 ∧ y=7
    else ∃ n : Nat,
      x+y+1=2^n*16 ∧ (2*k-3)+16+3*n=x+2*y+2
  else if k=0 then False
  else if 2*k≤a then x=a-2*k ∧ y=2*k+2
  else if a%2=0 then ∃ n : Nat,
    x+y=2^n*(2*(a-1)+6) ∧
    (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y
  else ∃ n : Nat,
    x+y+1=2^n*(2*(a-1)+8) ∧
    (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2

/-- A source-complete, machine-specific exact inverse for every possible
    section output whose right coordinate is >=5, with no bounce-depth cutoff.
    In particular, the arithmetic condition SUFFICES for a genuine edge. -/
theorem complete_section_inverse (a k x y : Nat) (hy:5≤y) :
    secNext (a,k)=some (x,y) ↔ sectionPreimageCriterion a k x y := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageCriterion,secNext,exactSection,ha0,hk0]
    · by_cases hk1 : k=1
      · simp [sectionPreimageCriterion,secNext,exactSection,ha0,hk0,hk1]
        omega
      · have ho := bounce_odd_output_exact 1 (2*k+1) x y (by decide) (by omega)
        simpa [sectionPreimageCriterion,secNext,exactSection,ha0,hk0,hk1] using ho
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,secNext,exactSection,ha0,ha1,hk0]
        omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageCriterion,secNext,exactSection,ha0,ha1,hk0,hk1]
          omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageCriterion,secNext,exactSection,ha0,ha1,hk0,hk1,hk2]
            constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
          · by_cases hk3 : k=3
            · simp [sectionPreimageCriterion,secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3]
              constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
            · have he := bounce_even_output_exact 4 (2*k-3) x y (by decide) (by omega)
              simpa [sectionPreimageCriterion,secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] using he
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,secNext,exactSection,ha0,ha1,hk0]
        omega
      · by_cases hlow : 2*k≤a
        · simp [sectionPreimageCriterion,secNext,exactSection,ha0,ha1,hk0,hlow]
          constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
        · by_cases haEven : a%2=0
          · have hkOdd : (a-1)%2=1 := by omega
            have ho := bounce_odd_output_exact (a-1) (2*k-a+3) x y hkOdd (by omega)
            simpa [sectionPreimageCriterion,secNext,exactSection,ha0,ha1,hk0,hlow,haEven] using ho
          · have hkEven : (a-1)%2=0 := by omega
            have he := bounce_even_output_exact (a-1) (2*k-a+3) x y hkEven (by omega)
            simpa [sectionPreimageCriterion,secNext,exactSection,ha0,ha1,hk0,hlow,haEven] using he

#print axioms complete_section_inverse
end BB6.Agent46
