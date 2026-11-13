import PacketP2ResetSource

set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

namespace BB6.P2ResetRegularReentry

open CryptidBoundary

/-- The two-E reset packet has a regularSection return when its index is
    divisible by three: the reset creates a q=0 B packet, whose next
    source-certified B return absorbs the remaining unary prefix. -/
theorem e_two_reset_regular_reentry (t q : Nat) :
    run (BB6.Agent2PacketP2Reset.eTwoTime (3*t) q +
      12*(8*t+1)*(8*t+1)+49*(8*t+1)+40)
      (BB6.Agent31PacketSource.packet (3*(3*t)+4) q 2
        (false :: List.replicate 6 true)) =
      BB6.Agent2BoundaryBZero.regularSection (64*t+2*q+23) 3 2 := by
  exact BB6.Agent2PacketP2Reset.e_two_k0_regular t q

#print axioms e_two_reset_regular_reentry

end BB6.P2ResetRegularReentry
