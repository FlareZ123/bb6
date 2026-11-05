import NoC1Source

namespace BB6.Agent45Exception
open BB6.P1Reduction

/-- The q=29 exact two-feeder shadow cone has no exceptional G(k,1)
input at any encoded odd hub with the already certified m≤10 bound.
The target L is 472 or 473; the weak L≤473 premise covers both. -/
theorem q29_no_special_G_one
    (L m b d w z alpha k : Nat)
    (hL : L≤473) (hm : m≤10)
    (hw : 4≤w) (hz : 0<z)
    (hbeven : b%2=0) (hbpos : 0<b)
    (hmass : b+d+2*m+2*L+3=56*2^464)
    (hoff : L+m=w+z)
    (hcoord : b+4*w=alpha*2^(464-m))
    (hG : G k 1=(b,d)) : False := by
  have hlow : 10≤464-m-2 := by omega
  have hpow := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hlow
  have hbase : 2^10 = (1024:Nat) := by decide
  have hmargin : 2*(L+m)<2^(464-m-2) := by omega
  exact encoded_no_special_G_one 464 L m b d w z alpha k (by omega)
    hw hz hbeven hbpos hmass hoff hcoord hmargin hG

#print axioms q29_no_special_G_one
end BB6.Agent45Exception
