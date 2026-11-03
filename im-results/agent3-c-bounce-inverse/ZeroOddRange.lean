import ZeroEvenOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Every odd zero-first section output lies strictly in the 3 mod 4
    sector and is at least seven, for every original source input. -/
theorem zero_first_odd_necessary (a k y : Nat)
    (ho : y%2=1) (h : secNext (a,k)=some (0,y)) :
    7≤y ∧ y%4=3 := by
  have hi := (section_preimage_all_iff a k 0 y).mp h
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hi
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hi
        omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at hi
        rcases hi with ⟨_,n,hs,_⟩
        have hh : 2^n*8=2*(2^n*4) := by ac_rfl
        rw [hh] at hs
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hi
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hi
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hi
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hi
              omega
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hi
              rcases hi with ⟨_,n,hs,_⟩ | ⟨hy,n,hs,_⟩
              · have hp : 1≤2^n := Nat.one_le_pow n 2 (by decide)
                omega
              · have heq : 2^n*16=4*(2^n*4) := by omega
                rw [heq] at hs
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hi
        omega
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_pos hlow] at hi
          rcases hi with ⟨_,hy⟩
          omega
        · by_cases haeven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos haeven] at hi
            rcases hi with ⟨_,n,hs,_⟩
            have heq : 2^n*(2*(a-1)+6)=
                2*(2^n*((a-1)+3)) := by
              calc
                2^n*(2*(a-1)+6) =
                    2^n*(2*((a-1)+3)) := by congr 1 <;> omega
                _ = 2*(2^n*((a-1)+3)) := by ac_rfl
            rw [heq] at hs
            omega
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg haeven] at hi
            rcases hi with ⟨_,n,hs,_⟩ | ⟨hy,n,hs,_⟩
            · have hp : 1≤2^n := Nat.one_le_pow n 2 (by decide)
              have hbound : 2*(a-1)+8≤2^n*(2*(a-1)+8) := by
                calc
                  2*(a-1)+8 ≤ (2*(a-1)+8)*2^n :=
                    Nat.le_mul_of_pos_right _ hp
                  _ = 2^n*(2*(a-1)+8) := by ac_rfl
              omega
            · have hav : (a-1)%2=0 := by omega
              let v : Nat := (a-1)/2
              have hfactor : 2*(a-1)+8=4*(v+2) := by
                dsimp [v]; omega
              rw [hfactor] at hs
              have hmul : 2^n*(4*(v+2))=4*(2^n*(v+2)) := by ac_rfl
              rw [hmul] at hs
              omega

/-- Every odd target congruent 3 modulo 4 and at least 7 is the
    output of an explicit real Machine C source return. -/
theorem zero_first_odd_sufficient (m : Nat) (hm : 1≤m) :
    ∃ a k, secNext (a,k)=some (0,4*m+3) := by
  by_cases h1 : m=1
  · subst m
    exact ⟨1,3,by decide⟩
  · have hm2 : 2≤m := by omega
    let a : Nat := 2*m-1
    let k : Nat := 3*m
    have ha0 : a≠0 := by dsimp [a]; omega
    have ha1 : a≠1 := by dsimp [a]; omega
    have hk0 : k≠0 := by dsimp [k]; omega
    have hreg : ¬2*k≤a := by dsimp [a,k]; omega
    have hodd : a%2≠0 := by dsimp [a]; omega
    have hsum : 0+(4*m+3)+1=2^0*(2*(a-1)+8) := by
      dsimp [a]; simp; omega
    have hcost : (2*k-a+3)+(2*(a-1)+8)+3*0=
        0+2*(4*m+3)+2 := by dsimp [a,k]; omega
    have hc : sectionPreimageAll a k 0 (4*m+3) := by
      simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
        if_neg hk0,if_neg hreg,if_neg hodd]
      exact Or.inr ⟨by omega,⟨0,hsum,hcost⟩⟩
    exact ⟨a,k,(section_preimage_all_iff a k 0 (4*m+3)).mpr hc⟩

/-- Exact one-step image classification in the odd zero-first quadrant. -/
theorem zero_first_odd_image_iff (y : Nat) (ho:y%2=1) :
    (∃ a k, secNext (a,k)=some (0,y)) ↔ 7≤y ∧ y%4=3 := by
  constructor
  · rintro ⟨a,k,h⟩
    exact zero_first_odd_necessary a k y ho h
  · rintro ⟨hy,hm⟩
    let m : Nat := (y-3)/4
    have hm1 : 1≤m := by dsimp [m]; omega
    have he : y=4*m+3 := by dsimp [m]; omega
    obtain ⟨a,k,hs⟩ := zero_first_odd_sufficient m hm1
    exact ⟨a,k,by simpa only [he] using hs⟩

/-- Source-connected all-time exclusion from the AUTHENTIC blank (5,1)
    section: no (0,4m+1) state can occur on the real return orbit. -/
theorem blank_no_zero_one_mod_four (n m : Nat) :
    BB6.Agent8Section.run secNext n (some (5,1)) ≠ some (0,4*m+1) := by
  intro h
  cases n with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ n =>
    cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at h
    | some p =>
      rcases p with ⟨a,k⟩
      have hs : secNext (a,k)=some (0,4*m+1) := by
        simpa [BB6.Agent8Section.run,hp] using h
      have he := zero_first_odd_necessary a k (4*m+1) (by omega) hs
      omega

#print axioms zero_first_odd_image_iff
#print axioms blank_no_zero_one_mod_four
end BB6.Agent3
