import PeriodDiv

namespace BB6.Agent10IterBarrier

theorem period_multiple (n m : Nat)
    (hperiod : ∀ z : Nat, F n (z+m)%m=F n z%m)
    (z d : Nat) : F n (z+m*d)%m=F n z%m := by
  induction d with
  | zero => simp
  | succ d ih =>
    have he : z+m*(d+1)=(z+m*d)+m := by
      simp [Nat.mul_succ]
      omega
    rw [he,hperiod,ih]

end BB6.Agent10IterBarrier
