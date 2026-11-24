import BB429Branch9Diagonal

namespace BB429Branch9J9
open BB429NewResidue BB429DyadicTransport BB429DyadicSource BB429Branch9Diagonal

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The genuine branch-9 diagonal has N=8*2^9+9-11=4094.
    Every one of its 1023 exceptional side indices is rejected. -/
theorem allSideRejected : ∀ k : Fin 1023,
    search basicTest 18 (sideA 9 4094 k.val) (sideB 9 4094 k.val) = false := by decide

theorem no_diagonal_J9 (a b : Nat)
    (ha : a+3=12*2^4094)
    (hb : b+24*2^4094+24*2^9=48*2^4094+15) : ¬Reach a b := by
  apply no_diagonal_of_certificate 9 4094 18 (by decide) (by decide) (by decide) ?_ 4094 a b (by decide) ha
  · simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using hb
  · intro k hk
    exact allSideRejected ⟨k,by omega⟩

#print axioms allSideRejected
#print axioms no_diagonal_J9
end BB429Branch9J9
