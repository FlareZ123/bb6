import RootWallArithmetic
import P1InverseLog

namespace BB6.Agent50L1All
open BB6.Agent47P1
open BB6.Agent1Quarter
open BB6.Agent1UpperTail

/-- Authentic upper-tail preservation of the full odd-cone mass. -/
theorem upper_tail_mass (b0 d0 m0 b d m n : Nat)
    (h: UpperTail b0 d0 m0 b d m n) :
    b+d+2*m=b0+d0+2*m0 := by
  induction h with
  | root => omega
  | step b d m n k c hprev hb hb4 hd hi hk hc ih =>
    have hm := inverseAt_odd_cost b d 0 k c
      (by omega) hb4 hd hi hc
    omega

#print axioms upper_tail_mass
end BB6.Agent50L1All
