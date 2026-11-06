import Lean.Elab.Tactic.Omega

namespace BB429PowerMinusThreeArithmetic

/-- Coordinates on a secondary inverse branch from a power-minus-three
terminal spine. Both large parameters are divisible by 64. -/
def Side (P Q x y t : Nat) : Prop :=
  P%64=0 ∧ Q%64=0 ∧
  x+3*t+12=P+Q ∧
  y+2*Q+6*t+3=2*P

theorem even_t (P Q x y t : Nat)
    (h : Side P Q x y t) (ht : t%2=0) :
    x%2=0 ∧ y%8≠2 := by
  rcases h with ⟨hp,hq,hx,hy⟩
  omega

theorem one_mod_eight (P Q x y t : Nat)
    (h : Side P Q x y t) (ht : t%8=1) :
    x%8=1 ∧ y%4=3 := by
  rcases h with ⟨hp,hq,hx,hy⟩
  omega

theorem three_mod_sixteen (P Q x y t : Nat)
    (h : Side P Q x y t) (ht : t%16=3) :
    x%16=11 ∧ y%8=3 := by
  rcases h with ⟨hp,hq,hx,hy⟩
  omega

theorem eleven_mod_thirtytwo (P Q x y t : Nat)
    (h : Side P Q x y t) (ht : t%32=11) :
    x%32=19 ∧ y%8=3 := by
  rcases h with ⟨hp,hq,hx,hy⟩
  omega

#print axioms even_t
#print axioms one_mod_eight
#print axioms three_mod_sixteen
#print axioms eleven_mod_thirtytwo
end BB429PowerMinusThreeArithmetic
