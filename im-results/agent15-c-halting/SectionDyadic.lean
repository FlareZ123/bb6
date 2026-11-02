import SectionAffineInverse
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

/-- Every successful section return with right counter two has a
    predecessor with right counter zero. -/
theorem section_right_two_source (a k x : Nat)
    (h : secNext (a,k)=some (x,2)) : k=0 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · exact hk0
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2=some (x,2) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        have hh := BB6Agent38.bounce_positive _ _ _ _ hb
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · exact hk0
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
            · have hb : (bounce 4 (2*k-3)).2=some (x,2) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              have hh := BB6Agent38.bounce_positive _ _ _ _ hb
              omega
    · by_cases hk0 : k=0
      · exact hk0
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,2) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          have hh := BB6Agent38.bounce_positive _ _ _ _ hb
          omega

/-- No section with second coordinate exactly two is blank reachable. -/
theorem blank_no_right_two (time x : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,2) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some p =>
          rcases p with ⟨a,k⟩
          have ht : secNext (a,k)=some (x,2) := by
            simpa [BB6.Agent8Section.run,hp] using h
          have hk := section_right_two_source a k x ht
          have hpos := BB6Agent38.blank_section_positive t a k hp
          omega

private theorem pow_atleast_four (n : Nat) : 4≤2^(n+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : (n+1)+2=(n+2)+1 := by omega
      rw [he,Nat.pow_succ]
      omega

private theorem pow_congruent_zero (n : Nat) : (2^(n+2))%4=0 := by
  have hpow : 2^(n+2)=2^n*4 := by
    rw [Nat.pow_add]
  rw [hpow]
  omega

/-- An infinite-depth exact reverse-affine obstruction: every genuine
    blank section avoids all left counter 3 mod4 / dyadic-minus-two
    right counters, regardless of inverse depth. -/
theorem blank_no_three_dyadic (time a n : Nat) (ha : a%4=3) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
       some (a,2^(n+2)-2) := by
  induction n generalizing a time with
  | zero =>
      have hpow : (2:Nat)^(0+2)-2=2 := by decide
      simpa only [hpow] using blank_no_right_two time a
  | succ n ih =>
      intro h
      have hpow : 4≤2^(n+2) := pow_atleast_four n
      have hpowS : 4≤2^((n+1)+2) := pow_atleast_four (n+1)
      have hmod : (2^((n+1)+2))%4=0 := pow_congruent_zero (n+1)
      let y := 2^((n+1)+2)-2
      have hy : 4≤y := by
        have he : (n+1)+2=(n+2)+1 := by omega
        have hbound : 8≤2^((n+1)+2) := by
          rw [he,Nat.pow_succ]
          omega
        dsimp [y]
        omega
      have heven : y%2=0 := by
        dsimp [y]
        omega
      have hsum : (a+y)%4=1 := by
        dsimp [y]
        omega
      have hpred : (y-2)/2 = 2^(n+2)-2 := by
        dsimp [y]
        have he : (n+1)+2=(n+2)+1 := by omega
        rw [he,Nat.pow_succ]
        omega
      have haPred : (a+y-2)%4=3 := by omega
      cases time with
      | zero =>
          simp [BB6.Agent8Section.run] at h
          omega
      | succ t =>
          cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
          | none => simp [BB6.Agent8Section.run,hp] at h
          | some p =>
              rcases p with ⟨b,k⟩
              have ht : secNext (b,k)=some (a,y) := by
                simpa [BB6.Agent8Section.run,hp,y] using h
              obtain ⟨hb,hk⟩ :=
                (section_sum_one_even_iff_affine b k a y hy heven hsum).mp ht
              have hprev : BB6.Agent8Section.run secNext t (some (5,1)) =
                  some (a+y-2,2^(n+2)-2) := by
                rw [hb,hk,hpred] at hp
                exact hp
              exact ih t (a+y-2) haPred hprev

#print axioms section_right_two_source
#print axioms blank_no_right_two
#print axioms blank_no_three_dyadic
end BB6.Agent15
