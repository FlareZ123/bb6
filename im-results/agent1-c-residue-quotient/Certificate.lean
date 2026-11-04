import AllRows
import FirstM58Proof

namespace CQuotient192

/-- Entire first Machine C stopping family m≡58 mod64 is excluded
    from the authentic blank-entry accelerated orbit. -/
theorem first_m58_unreachable
    (m k : Nat) (hm : m % 64 = 58)
    (hk : k+3*m+4 = 2^(2*m+3)) :
    ¬ BB6CLine.Reach (1,k,0) := by
  exact first_m58_if_closed (fun p x y => all_closed p x y) m k hm hk

#print axioms first_m58_unreachable
end CQuotient192
