import UniformS25Residual
import BounceInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

private theorem mod8_power2_even (n : Nat) (hn : 1≤n) :
    ∃ u : Nat, 2^n=2*u := by
  obtain ⟨m,hm⟩ : ∃ m, n=m+1 := ⟨n-1,by omega⟩
  refine ⟨2^m,?_⟩
  rw [hm,Nat.pow_succ]
  omega

/-- A general original-bounce valuation theorem. For odd bounce input
    and output sum four modulo eight, every successful bounce is terminal:
    no positive recursive bounce depth is possible. -/
theorem odd_bounce_mod8_forces_terminal (c b x y : Nat)
    (hb : (bounce b c).2=some (x,y))
    (hodd : b%2=1) (hmod : (x+y)%8=4) :
    x+y=2*b+6 ∧ c=y := by
  obtain ⟨n,hsum,hcost⟩ := bounce_odd_output_invariants
    c b x y hodd hb
  by_cases hn : n=0
  · subst n
    simp at hsum hcost
    constructor <;> omega
  · obtain ⟨u,hu⟩ := mod8_power2_even n (by omega)
    obtain ⟨v,hv⟩ : ∃ v : Nat, 2*b+6=4*v :=
      ⟨(b+3)/2,by omega⟩
    have hdiv : x+y=8*(u*v) := by
      calc
        x+y=2^n*(2*b+6) := hsum
        _ = (2*u)*(4*v) := by rw [hu,hv]
        _ = (2*4)*(u*v) := by ac_rfl
        _ = 8*(u*v) := by rfl
    omega

/-- General dual valuation theorem: an even bounce with output
    sum three modulo eight and output right counter at least four
    terminates without any recursive bounce. -/
theorem even_bounce_mod8_forces_terminal (c b x y : Nat)
    (hb : (bounce b c).2=some (x,y))
    (heven : b%2=0) (hy : 4≤y) (hmod : (x+y)%8=3) :
    x+y+1=2*b+8 ∧ c=y+1 := by
  obtain ⟨n,hsum,hcost⟩ := bounce_even_output_invariants
    c b x y heven hy hb
  by_cases hn : n=0
  · subst n
    simp at hsum hcost
    constructor <;> omega
  · obtain ⟨u,hu⟩ := mod8_power2_even n (by omega)
    obtain ⟨v,hv⟩ : ∃ v : Nat, 2*b+8=4*v :=
      ⟨b/2+2,by omega⟩
    have hdiv : x+y+1=8*(u*v) := by
      calc
        x+y+1=2^n*(2*b+8) := hsum
        _ = (2*u)*(4*v) := by rw [hu,hv]
        _ = (2*4)*(u*v) := by ac_rfl
        _ = 8*(u*v) := by rfl
    omega

#print axioms odd_bounce_mod8_forces_terminal
#print axioms even_bounce_mod8_forces_terminal

end BB6.Agent46
