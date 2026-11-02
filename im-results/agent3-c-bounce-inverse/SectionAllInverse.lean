import BounceAllExact
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Exact arithmetic preimage grammar for EVERY successful Machine C section
    return, including small right counters 1, 2, 3 and 4. Every existential
    depth is unbounded, and both directions are genuine original-source edges. -/
def sectionPreimageAll (a k x y : Nat) : Prop :=
  if a=0 then
    if k=0 then False
    else if k=1 then x=0 ∧ y=4
    else 4≤y ∧ ∃ n:Nat,
      x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y
  else if a=1 then
    if k=0 then x=5 ∧ y=1
    else if k=1 then x=2 ∧ y=3
    else if k=2 then x=2 ∧ y=5
    else if k=3 then x=0 ∧ y=7
    else
      (y=3 ∧ ∃ n:Nat, x+6=2^n*16 ∧
        (2*k-3)+16+3*n=x+10) ∨
      (5≤y ∧ ∃ n:Nat, x+y+1=2^n*16 ∧
        (2*k-3)+16+3*n=x+2*y+2)
  else if k=0 then x=a-2 ∧ y=2
  else if 2*k≤a then x=a-2*k ∧ y=2*k+2
  else if a%2=0 then
    4≤y ∧ ∃ n:Nat,
      x+y=2^n*(2*(a-1)+6) ∧
      (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y
  else
    (y=3 ∧ ∃ n:Nat, x+6=2^n*(2*(a-1)+8) ∧
      (2*k-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
    (5≤y ∧ ∃ n:Nat,
      x+y+1=2^n*(2*(a-1)+8) ∧
      (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2)

/-- Original-source exact if-and-only-if for all source/target coordinates.
    Covers all exceptional and recursive branches, without any target guard
    or inverse-depth cutoff. -/
theorem section_preimage_all_iff (a k x y : Nat) :
    secNext (a,k)=some (x,y) ↔ sectionPreimageAll a k x y := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,secNext,exactSection,ha0,hk0]
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,secNext,exactSection,ha0,hk0,hk1]
        constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
      · have ho := bounce_full_exact 1 (2*k+1) x y
        simpa [sectionPreimageAll,secNext,exactSection,ha0,hk0,hk1] using ho
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,secNext,exactSection,ha0,ha1,hk0]
        constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,secNext,exactSection,ha0,ha1,hk0,hk1]
          constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,secNext,exactSection,ha0,ha1,hk0,hk1,hk2]
            constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3]
              constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
            · have he := bounce_full_exact 4 (2*k-3) x y
              simpa [sectionPreimageAll,secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] using he
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,secNext,exactSection,ha0,ha1,hk0]
        constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
      · by_cases hlow : 2*k≤a
        · simp [sectionPreimageAll,secNext,exactSection,ha0,ha1,hk0,hlow]
          constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1.symm,h2.symm⟩
        · by_cases haeven : a%2=0
          · have ho := bounce_full_exact (a-1) (2*k-a+3) x y
            have hodd : (a-1)%2=1 := by omega
            simpa [sectionPreimageAll,secNext,exactSection,ha0,ha1,hk0,hlow,haeven,hodd] using ho
          · have he := bounce_full_exact (a-1) (2*k-a+3) x y
            have hev : (a-1)%2=0 := by omega
            simpa [sectionPreimageAll,secNext,exactSection,ha0,ha1,hk0,hlow,haeven,hev] using he

#print axioms section_preimage_all_iff
end BB6.Agent46
