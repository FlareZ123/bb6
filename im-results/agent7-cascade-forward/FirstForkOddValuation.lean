import FirstForkOddT45

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield

theorem near_top_odd_only_one_three (n u A k t d : Nat) (hn:5≤n)
    (hclose:u+A=4*2^n) (htight:64*A+164≤13*2^n)
    (hnot:(2*u+5)%2187≠0)
    (hband:6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1)
    (hout:2*u+5=3^(t+1)*d) : t=1 ∨ t=3 := by
  by_cases hz:t=0
  · subst t
    have hsize:8*A≤5*2^n:=by omega
    have hb:3*2^n≤u := by omega
    have hu:u≤4*2^n:=by omega
    have hout0:2*u+5=3*d:=by simpa using hout
    exact False.elim (odd_tzero_in_dyadic_gap n u (by omega) hb hu
      ⟨k,d,by simpa using hband,hout0⟩)
  by_cases h1:t=1
  · exact Or.inl h1
  by_cases h2:t=2
  · subst t
    have hp:2^2=4:=by decide
    have hout2:2*u+5=27*d:=by simpa using hout
    have hb2:6*2^k+1≤4*d ∧ 4*d≤8*2^k-1:=by simpa [hp] using hband
    exact False.elim ((near_top_no_odd_ttwo n u A (by omega) hclose
      (by omega)) ⟨k,d,hb2,hout2⟩)
  by_cases h3:t=3
  · exact Or.inr h3
  by_cases h4:t=4
  · subst t
    have hp:2^4=16:=by decide
    have hout4:2*u+5=243*d:=by simpa using hout
    have hb4:6*2^k+1≤16*d ∧ 16*d≤8*2^k-1:=by simpa [hp] using hband
    exact False.elim ((near_top_no_odd_tfour n u A (by omega)
      hclose htight) ⟨k,d,hb4,hout4⟩)
  by_cases h5:t=5
  · subst t
    have hp:2^5=32:=by decide
    have hout5:2*u+5=729*d:=by simpa using hout
    have hb5:6*2^k+1≤32*d ∧ 32*d≤8*2^k-1:=by simpa [hp] using hband
    exact False.elim ((near_top_no_odd_tfive n u A hn
      hclose htight) ⟨k,d,hb5,hout5⟩)
  have hge:6≤t:=by omega
  have hex:t+1=7+(t-6):=by omega
  have hpow:3^(t+1)%2187=0:=by
    rw [hex,Nat.pow_add]
    simp
  have hbad:(2*u+5)%2187=0:=by
    rw [hout,Nat.mul_mod,hpow]
    simp
  exact False.elim (hnot hbad)

#print axioms near_top_odd_only_one_three
end CascadeFirstFork
