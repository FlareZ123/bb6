import GenericIter
namespace BB6.GeneralParity

theorem period_multiple (a b c n m : Nat)
  (hp : ∀ z : Nat, Iter a b c n (z+m)%m=Iter a b c n z%m)
  (z d : Nat) : Iter a b c n (z+m*d)%m=Iter a b c n z%m := by
  induction d with
  | zero => simp
  | succ d ih =>
    have he : z+m*(d+1)=(z+m*d)+m := by
      simp [Nat.mul_succ]
      omega
    rw [he,hp,ih]

theorem mod_same_add_divides (x m c : Nat) (h : (x+c)%m=x%m) : m ∣ c := by
  have hs:=Nat.sub_mod_eq_zero_of_mod_eq h
  have he:x+c-x=c := by omega
  rw [he] at hs
  exact Nat.dvd_of_mod_eq_zero hs

end BB6.GeneralParity
