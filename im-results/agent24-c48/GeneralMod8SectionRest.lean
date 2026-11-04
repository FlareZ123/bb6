import GeneralMod8Section
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

private theorem odd_bounce_sum_even (c b x y : Nat)
    (hb : (bounce b c).2=some (x,y)) (hodd : b%2=1) :
    (x+y)%2=0 := by
  obtain ⟨n,hsum,_⟩ := bounce_odd_output_invariants c b x y hodd hb
  have hfactor : 2*b+6=2*(b+3) := by omega
  have hsum' : x+y=2*(2^n*(b+3)) := by
    calc
      x+y=2^n*(2*b+6) := hsum
      _ = 2^n*(2*(b+3)) := by rw [hfactor]
      _ = 2*(2^n*(b+3)) := by ac_rfl
  omega

theorem section_evenodd_sum3_inverse (a k x y : Nat)
    (hy : 5≤y) (hyodd : y%2=1) (hmod : (x+y)%8=3)
    (h : secNext (a,k)=some (x,y)) :
    a=(x+y-5)/2 ∧ k=(x+3*y-9)/4 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
        omega
      · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        have heven := odd_bounce_sum_even (2*k+1) 1 x y hb (by decide)
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
          omega
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
            omega
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
              omega
            · have hb : (bounce 4 (2*k-3)).2=some (x,y) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              have heq := even_bounce_mod8_forces_terminal
                (2*k-3) 4 x y hb (by decide) (by omega) hmod
              omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hregion] using h
          by_cases he : a%2=0
          · have hodd : (a-1)%2=1 := by omega
            have heven := odd_bounce_sum_even (2*k-a+3) (a-1) x y hb hodd
            omega
          · have hodd : (a-1)%2=0 := by omega
            obtain ⟨hsum,hcounter⟩ :=
              even_bounce_mod8_forces_terminal (2*k-a+3) (a-1)
                x y hb hodd (by omega) hmod
            constructor <;> omega

#print axioms section_evenodd_sum3_inverse
end BB6.Agent46
