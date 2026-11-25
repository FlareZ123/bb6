import ReverseBlock
import WeightedDigitGap

namespace BB6.Agent45ReverseBlock

open BB6.Agent45WeightedDigitGap (digitWeight corr_le_mul)

/-- Under the wider fit bound, every legal block parent lies in the
    two-element quotient window floor(X/(q+k)), floor(X/(q+k))+1. -/
theorem candidate_window (q k X B r : Nat)
    (hfit : 2^(k+1)≤q+k) (hr : r<q)
    (he : X+corr k B=(q+k)*B+r) :
    X/(q+k)≤B ∧ B≤X/(q+k)+1 := by
  apply word_near (q+k) k X B r
  · omega
  · exact hfit
  · omega
  · exact he

/-- The reverse-block remainder is exactly the little-endian
    C++ remainder X-q*B-digitWeight(k,B). -/
theorem candidate_remainder_eq (q k X B : Nat)
    (hB : B<2^k)
    (hvalid : (q+k)*B ≤ X+corr k B) :
    X+corr k B-(q+k)*B = X-q*B-digitWeight k B := by
  have hc := corr_le_mul k B hB
  have hprod : (q+k)*B=q*B+k*B := Nat.add_mul q k B
  unfold digitWeight
  omega

#print axioms candidate_window
#print axioms candidate_remainder_eq

end BB6.Agent45ReverseBlock
