import Std

namespace SheepOddInverse

theorem mod_double_rep (m x:Nat) (hm:0<m) :
    x % (2*m)=x%m ∨ x % (2*m)=x%m +m := by
  let A:=x % (2*m)
  have hA : A < 2*m := Nat.mod_lt x (by omega)
  have hreduce : A%m=x%m := by
    dsimp [A]
    apply Nat.mod_mod_of_dvd x
    exact ⟨2,by omega⟩
  by_cases hlow : A<m
  · left
    have h:=Nat.mod_eq_of_lt hlow
    dsimp [A] at *
    omega
  · right
    have hhigh : A-m<m := by omega
    have hmod := Nat.mod_eq_sub_mod (a:=A) (b:=m) (by omega)
    rw [Nat.mod_eq_of_lt hhigh] at hmod
    dsimp [A] at *
    omega

theorem mod_toggle (m x:Nat) (hm:0<m) :
    (x+m)%(2*m) =
    (if x%(2*m)<m then x%(2*m)+m else x%(2*m)-m) := by
  let A:=x%(2*m)
  have hA : A<2*m := Nat.mod_lt x (by omega)
  have hs : (x+m)%(2*m)=(A+m)%(2*m) := by
    simpa only [A] using (Nat.mod_add_mod x (2*m) m).symm
  change (x+m)%(2*m) = (if A<m then A+m else A-m)
  by_cases hlow : A<m
  · simp [hlow]
    rw [hs, Nat.mod_eq_of_lt (by omega : A+m<2*m)]
  · simp [hlow]
    rw [hs]
    have hbig : A+m>=2*m := by omega
    rw [Nat.mod_eq_sub_mod hbig]
    have hsm : A+m-(2*m)<2*m := by omega
    rw [Nat.mod_eq_of_lt hsm]
    omega

theorem mod_double_lift (m a b:Nat) (hm:0<m) (hab:a%m=b%m) :
    a%(2*m)=b%(2*m) ∨ (a+m)%(2*m)=b%(2*m) := by
  have ha:=mod_double_rep m a hm
  have hb:=mod_double_rep m b hm
  have ht:=mod_toggle m a hm
  have hrem : a%(2*m)<2*m := Nat.mod_lt a (by omega)
  have hremb : b%(2*m)<2*m := Nat.mod_lt b (by omega)
  by_cases hlt : a%(2*m)<m
  · simp [hlt] at ht
    rcases ha with ha|ha <;> rcases hb with hb|hb <;> omega
  · simp [hlt] at ht
    rcases ha with ha|ha <;> rcases hb with hb|hb <;> omega

theorem mod_add_multiple (base m q:Nat) : (base+m*q)%m=base%m := by
  simp [Nat.add_mod]

theorem odd_multiplier_toggle (m c w d:Nat) (hc:c%2=1) :
    (c*(w+m)+d)%(2*m)=(c*w+d+m)%(2*m) := by
  have hcdecomp : c=2*(c/2)+1 := by
    have := Nat.mod_add_div c 2
    omega
  have hcm : c*m = (2*m)*(c/2)+m := by
    calc
      c*m=(2*(c/2)+1)*m := by rw [← hcdecomp]
      _ = (2*m)*(c/2)+m := by rw [Nat.add_mul]; ac_rfl
  have hh : c*(w+m)+d = (c*w+d+m)+(2*m)*(c/2) := by
    rw [Nat.mul_add,hcm]
    omega
  rw [hh]
  exact mod_add_multiple (c*w+d+m) (2*m)

/-- Construct an inverse image of an affine odd-slope map modulo every 2^k. -/
def solve (k c d y:Nat) : Nat :=
  match k with
  | 0 => 0
  | k+1 =>
      let w:=solve k c d y
      if (c*w+d)%(2^(k+1))=y%(2^(k+1)) then w else w+2^k

theorem solve_correct (k c d y:Nat) (hc:c%2=1) :
    (c*(solve k c d y)+d)%2^k=y%2^k := by
  induction k with
  | zero => simp only [solve, Nat.pow_zero, Nat.mod_one]
  | succ k ih =>
      let w:=solve k c d y
      have h0 : (c*w+d)%2^k=y%2^k := ih
      have hpos : 0<2^k := Nat.pow_pos (by decide)
      have hsucc : 2^(k+1)=2*(2^k) := by
        rw [Nat.pow_succ]; ac_rfl
      have hmod := mod_double_lift (2^k) (c*w+d) y hpos h0
      have htoggle := odd_multiplier_toggle (2^k) c w d hc
      simp only [← hsucc] at hmod htoggle
      change (c*(if (c*w+d)%(2^(k+1))=y%(2^(k+1))
          then w else w+2^k)+d)%2^(k+1)=y%2^(k+1)
      by_cases htest : (c*w+d)%(2^(k+1))=y%(2^(k+1))
      · simp [htest]
      · simp [htest]
        rcases hmod with hsame | hshift
        · exact False.elim (htest hsame)
        · exact htoggle.trans hshift

#print axioms solve_correct

theorem solve_lt (k c d y:Nat) : solve k c d y < 2^k := by
  induction k with
  | zero => simp [solve]
  | succ k ih =>
      change (if (c*solve k c d y+d)%(2^(k+1))=y%(2^(k+1))
        then solve k c d y else solve k c d y+2^k) < 2^(k+1)
      rw [Nat.pow_succ]
      split
      · omega
      · omega

#print axioms solve_lt

end SheepOddInverse
