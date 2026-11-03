import AffineBarrier

namespace BB6.Agent10IterBarrier

theorem mod_same_add_divides (x m c : Nat) (h : (x+c)%m=x%m) : m ∣ c := by
  have hs:=Nat.sub_mod_eq_zero_of_mod_eq h
  have he:x+c-x=c := by omega
  rw [he] at hs
  exact Nat.dvd_of_mod_eq_zero hs

end BB6.Agent10IterBarrier
