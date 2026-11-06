import OddSevenGeneralAlgebra
import BounceInverse
import FastSectionDef
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent19Seven
open BB6.Agent46

private theorem odd_bounce_sum_even_general (c b x y:Nat)
    (hb:(bounce b c).2=some (x,y)) (ho:b%2=1) : (x+y)%2=0 := by
  obtain ⟨n,hsum,_⟩ := bounce_odd_output_invariants c b x y ho hb
  have hs : x+y=2*(2^n*(b+3)) := by
    calc
      x+y=2^n*(2*b+6) := hsum
      _=2^n*(2*(b+3)) := by rw [show 2*b+6=2*(b+3) by omega]
      _=2*(2^n*(b+3)) := by ac_rfl
  omega

/-- Uniform necessary inverse grammar for every odd/even Machine C
    source output whose sum+1 has exact 2-adic valuation four. -/
theorem section_sumseven_mod32_inverse (a k x y:Nat)
    (hx:x%2=1) (hy:y%2=0) (hy6:6≤y)
    (hmod:(x+y+1)%32=16) (hbig:48≤x+y+1)
    (h:secNext (a,k)=some (x,y)) :
    (a=x+y-2 ∧ y=2*k+2) ∨
    (4*a+12=x+y+1 ∧ 2*k+a+10=x+2*y) := by
  by_cases ha0 : a=0
  · by_cases hk0:k=0
    · simp [secNext,exactSection,ha0,hk0] at h <;> omega
    · by_cases hk1:k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h <;> omega
      · have hb:(bounce 1 (2*k+1)).2=some (x,y) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        have he := odd_bounce_sum_even_general (2*k+1) 1 x y hb (by decide)
        omega
  · by_cases ha1:a=1
    · by_cases hk0:k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h <;> omega
      · by_cases hk1:k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h <;> omega
        · by_cases hk2:k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h <;> omega
          · by_cases hk3:k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h <;> omega
            · have hb:(bounce 4 (2*k-3)).2=some (x,y) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              obtain ⟨n,hsum,_⟩ :=
                bounce_even_output_invariants (2*k-3) 4 x y
                  (by decide) (by omega) hb
              cases n with
              | zero =>
                  simp at hsum
                  omega
              | succ n =>
                  have hs:x+y+1=32*(2^n) := by
                    calc
                      x+y+1=2^(n+1)*(2*4+8) := hsum
                      _=(2^n*2)*16 := by rw [Nat.pow_succ] <;> omega
                      _=32*(2^n) := by omega
                  omega
    · have ha2:2≤a := by omega
      by_cases hk0:k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h <;> omega
      · by_cases hregion:2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          exact Or.inl (by constructor <;> omega)
        · have hb:(bounce (a-1) (2*k-a+3)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hregion] using h
          by_cases hae:a%2=0
          · have ho:(a-1)%2=1 := by omega
            have he := odd_bounce_sum_even_general (2*k-a+3) (a-1) x y hb ho
            omega
          · have hao:a%2=1 := by omega
            obtain ⟨n,hsum,hcost⟩ :=
              bounce_even_output_invariants (2*k-a+3) (a-1)
                x y (by omega) (by omega) hb
            obtain ⟨_,ha,hk⟩ := general_source_bounce_depth_one
              x y a k n hx hy hao (by omega) hmod hsum hcost
            exact Or.inr ⟨ha,hk⟩

#print axioms section_sumseven_mod32_inverse
end BB6.Agent19Seven
