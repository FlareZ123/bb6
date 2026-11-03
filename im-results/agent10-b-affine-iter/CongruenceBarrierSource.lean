import AffineBarrierSource
import CongruenceBarrier

namespace BB6.Agent10IterBarrier

/-- Any nontrivial finite congruence factor of an authentic B scalar iterate is mod 7. -/
theorem source_periodic_modulus_divides_seven (n m : Nat)
    (hn : 0<n) (hm : 0<m)
    (hp : ∀ z : Nat, BB6.OneDim.iterG n (z+m)%m=BB6.OneDim.iterG n z%m) :
    m ∣ 7 := by
  apply periodic_modulus_divides_seven n m hn hm
  intro z
  rw [F_eq_old_iter, F_eq_old_iter, BB6.Agent10B.iterG_eq_source,
      BB6.Agent10B.iterG_eq_source]
  exact hp z

#print axioms source_periodic_modulus_divides_seven
end BB6.Agent10IterBarrier
