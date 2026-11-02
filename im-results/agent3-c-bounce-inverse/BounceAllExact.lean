import BounceEvenExact
import BounceOddExact
import BounceEvenThree
import BounceEvenNoFour
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- No odd-middle bounce returns with right counter three, regardless of
    recursion depth. Every odd terminal exit has right counter >=4. -/
theorem bounce_odd_no_three (K c x : Nat) (hK:K%2=1) :
    (bounce K c).2≠some (x,3) := by
  induction c using Nat.strongRecOn generalizing K x with
  | ind c ih =>
    intro hb
    by_cases hlow : c<4
    · simp [bounce,hlow] at hb
    · by_cases hs : c≤2*K+6
      · have hh:=hb
        rw [bounce] at hh
        simp only [if_neg hlow,if_pos hK,if_pos hs] at hh
        have heq := Option.some.inj hh
        have hp := Prod.mk.inj heq
        omega
      · have hlt:c-(2*K+3)<c := by omega
        have hh : (bounce (2*K+3) (c-(2*K+3))).2=some (x,3) := by
          have hh:=hb
          rw [bounce] at hh
          simpa only [if_neg hlow,if_pos hK,if_neg hs] using hh
        exact ih (c-(2*K+3)) hlt (2*K+3) x (by omega) hh

/-- Completely characterize every successful odd-middle bounce output,
    including small-counter cases. No guard is required on y. -/
theorem bounce_odd_full_exact (K c x y : Nat) (hK : K%2=1) :
    (bounce K c).2=some (x,y) ↔
      4≤y ∧ ∃ n : Nat, x+y=2^n*(2*K+6) ∧
        c+(2*K+6)+3*n=x+2*y := by
  constructor
  · intro hb
    have hp := BB6Agent38.bounce_positive c K x y hb
    have hn3 := bounce_odd_no_three K c x hK
    have hy : 4≤y := by
      by_contra h
      have he : y=3 := by omega
      subst y
      exact hn3 hb
    exact ⟨hy,(bounce_odd_output_exact K c x y hK hy).mp hb⟩
  · rintro ⟨hy,hs⟩
    exact (bounce_odd_output_exact K c x y hK hy).mpr hs

/-- Completely characterize every successful even-middle bounce output,
    including its special y=3 exit, with arbitrary recursion depth. -/
theorem bounce_even_full_exact (K c x y : Nat) (hK : K%2=0) :
    (bounce K c).2=some (x,y) ↔
      (y=3 ∧ ∃ n : Nat, x+6=2^n*(2*K+8) ∧
        c+(2*K+8)+3*n=x+10) ∨
      (5≤y ∧ ∃ n : Nat, x+y+1=2^n*(2*K+8) ∧
        c+(2*K+8)+3*n=x+2*y+2) := by
  constructor
  · intro hb
    have hp := BB6Agent38.bounce_positive c K x y hb
    by_cases h3 : y=3
    · left
      subst y
      exact ⟨rfl,(bounce_three_exact K c x hK).mp hb⟩
    · have hn4 := bounce_even_no_four K c x hK
      have hy : 5≤y := by
        by_contra h
        have he : y=4 := by omega
        subst y
        exact hn4 hb
      right
      exact ⟨hy,(bounce_even_output_exact K c x y hK hy).mp hb⟩
  · rintro (⟨h3,h⟩ | ⟨hy,h⟩)
    · subst y
      exact (bounce_three_exact K c x hK).mpr h
    · exact (bounce_even_output_exact K c x y hK hy).mpr h

/-- The entire original source bounce relation is equivalent to a finite
    parity case split with at most one unbounded exponent witness. -/
theorem bounce_full_exact (K c x y : Nat) :
    (bounce K c).2=some (x,y) ↔
      (K%2=1 ∧ 4≤y ∧ ∃ n : Nat,
        x+y=2^n*(2*K+6) ∧
        c+(2*K+6)+3*n=x+2*y) ∨
      (K%2=0 ∧
        ((y=3 ∧ ∃ n : Nat, x+6=2^n*(2*K+8) ∧
          c+(2*K+8)+3*n=x+10) ∨
         (5≤y ∧ ∃ n : Nat, x+y+1=2^n*(2*K+8) ∧
          c+(2*K+8)+3*n=x+2*y+2))) := by
  by_cases hodd : K%2=1
  · rw [bounce_odd_full_exact K c x y hodd]
    constructor
    · rintro ⟨hy,hr⟩
      exact Or.inl ⟨hodd,hy,hr⟩
    · rintro (⟨_,hy,hr⟩ | ⟨he,_⟩)
      · exact ⟨hy,hr⟩
      · omega
  · have heven : K%2=0 := by omega
    rw [bounce_even_full_exact K c x y heven]
    constructor
    · intro h
      exact Or.inr ⟨heven,h⟩
    · rintro (⟨ho,_,_⟩ | ⟨_,h⟩)
      · omega
      · exact h

#print axioms bounce_odd_full_exact
#print axioms bounce_even_full_exact
#print axioms bounce_full_exact
end BB6.Agent46
