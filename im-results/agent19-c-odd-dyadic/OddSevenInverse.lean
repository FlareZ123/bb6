import OddSevenAlgebra
import OddSpecialLift
import BounceInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Seven
open BB6.Agent46

private theorem odd_bounce_output_even (c b x y : Nat)
    (hb : (bounce b c).2=some (x,y)) (ho : b%2=1) :
    (x+y)%2=0 := by
  obtain ⟨n,hsum,_⟩ := bounce_odd_output_invariants c b x y ho hb
  have hfactor : 2*b+6=2*(b+3) := by omega
  have hs : x+y=2*(2^n*(b+3)) := by
    calc
      x+y=2^n*(2*b+6) := hsum
      _=2^n*(2*(b+3)) := by rw [hfactor]
      _=2*(2^n*(b+3)) := by ac_rfl
  omega

/-- Complete necessary predecessor classification across sum-7 mod8. -/
theorem section_sumseven_target_inverse (a k u v : Nat)
    (hv:1≤v) (h: secNext (a,k)=some (32*u+1,256*v+46)) :
    (a=32*u+256*v+45 ∧ k=128*v+22) ∨
    (a=8*u+64*v+9 ∧ k=12*u+224*v+37) := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
        omega
      · have hb : (bounce 1 (2*k+1)).2=some (32*u+1,256*v+46) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        have he := odd_bounce_output_even (2*k+1) 1 (32*u+1) (256*v+46)
          hb (by decide)
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
            · have hb : (bounce 4 (2*k-3)).2=some (32*u+1,256*v+46) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              obtain ⟨n,hsum,_⟩ :=
                bounce_even_output_invariants (2*k-3) 4
                  (32*u+1) (256*v+46) (by decide) (by omega) hb
              cases n with
              | zero =>
                  simp at hsum
                  omega
              | succ n =>
                  have hs : 32*u+256*v+48=32*(2^n) := by
                    calc
                      32*u+256*v+48=2^(n+1)*(2*4+8) := hsum
                      _=(2^n*2)*16 := by rw [Nat.pow_succ]; omega
                      _=32*(2^n) := by omega
                  omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          left
          constructor <;> omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some
            (32*u+1,256*v+46) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hregion] using h
          by_cases hae : a%2=0
          · have hodd : (a-1)%2=1 := by omega
            have hbad := odd_bounce_output_even (2*k-a+3) (a-1)
              (32*u+1) (256*v+46) hb hodd
            omega
          · have haodd : a%2=1 := by omega
            obtain ⟨n,hsum,hcost⟩ :=
              bounce_even_output_invariants (2*k-a+3) (a-1)
                (32*u+1) (256*v+46) (by omega) (by omega) hb
            have hs : 32*u+256*v+48=2^n*(2*(a-1)+8) := by omega
            obtain ⟨_,ha,hk⟩ :=
              source_bounce_target_algebra u v a k n haodd (by omega) hs hcost
            exact Or.inr ⟨ha,hk⟩

#print axioms section_sumseven_target_inverse
end BB6.Agent19Seven
