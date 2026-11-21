import OddConeMass
import InverseIff

namespace BB6.Agent9RootCost

open BB6.Agent1Quarter
open BB6.Agent47P1

/-- A source edge in an odd cone has a one-dimensional coordinate recurrence.
    Here K=(b0+d0+7)/2, x=d/2, and the child coordinate is (c+4)/2. -/
theorem rootCostPotentialStep
    (b0 d0 b d m t k c K : Nat)
    (hK : 2*K = b0+d0+7)
    (hcone : OddCone b0 d0 b d m)
    (hb : 8≤b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hc : c%2=1) :
    2^(m+t+1)*((c+4)/2) + 2^m*m = 2^m*(K+d/2) := by
  have hmass := odd_cone_mass b0 d0 b d m hcone
  have hpow := (inverseAt_iff_power_mass b d t k c (by omega) hb4 hd).mp hi
  have hd2 : d = 2*(d/2)+1 := by omega
  have hb2 : b = 2*(b/2) := by omega
  have hc2 : 2*(c/2+2)=c+3 := by omega
  have hc4 : (c+4)/2 = c/2+2 := by omega
  have hsource : d+b/2+3 = K+d/2-m := by omega
  have hrec : 2^(t+1)*(c/2+2)=K+d/2-m := by
    calc
      2^(t+1)*(c/2+2)
          = 2^t*(2*(c/2+2)) := by rw [pow_succ]; ring
      _ = 2^t*(c+3) := by rw [hc2]
      _ = d+b/2+3 := hpow.1.symm
      _ = K+d/2-m := hsource
  have hpowadd : 2^(m+t+1)=2^m*2^(t+1) := by
    calc
      2^(m+t+1)=2^(m+(t+1)) := by congr 1; omega
      _ = 2^m*2^(t+1) := by rw [pow_add]
  have hsum : (K+d/2-m)+m=K+d/2 := by omega
  calc
    2^(m+t+1)*((c+4)/2)+2^m*m
        = (2^m*2^(t+1))*(c/2+2)+2^m*m := by rw [hpowadd,hc4]
    _ = 2^m*(2^(t+1)*(c/2+2))+2^m*m := by ring
    _ = 2^m*(K+d/2-m)+2^m*m := by rw [hrec]
    _ = 2^m*((K+d/2-m)+m) := by rw [← Nat.mul_add]
    _ = 2^m*(K+d/2) := by rw [hsum]

/-- The potential R=2^m*(d/2) therefore changes by 2^m*(K-m). -/
theorem rootCostPotentialDelta
    (b0 d0 b d m t k c K : Nat)
    (hK : 2*K = b0+d0+7)
    (hcone : OddCone b0 d0 b d m)
    (hb : 8≤b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hc : c%2=1) :
    2^(m+t+1)*((c+4)/2) = 2^m*(d/2) + 2^m*(K-m) := by
  have hstep := rootCostPotentialStep b0 d0 b d m t k c K hK hcone hb hb4 hd hi hc
  have hmass := odd_cone_mass b0 d0 b d m hcone
  have hsplit : (d/2)+(K-m)=K+d/2-m := by omega
  have hcancel :
      2^(m+t+1)*((c+4)/2) = 2^m*(K+d/2-m) := by
    have hsum : (K+d/2-m)+m=K+d/2 := by omega
    have hrewrite :
        2^m*(K+d/2-m)+2^m*m = 2^m*(K+d/2) := by
      rw [← Nat.mul_add, hsum]
    exact Nat.add_right_cancel (hstep.trans hrewrite.symm)
  calc
    2^(m+t+1)*((c+4)/2)
        = 2^m*((d/2)+(K-m)) := by rw [hcancel]; congr 1; omega
    _ = 2^m*(d/2)+2^m*(K-m) := by rw [Nat.mul_add]

#print axioms rootCostPotentialStep
#print axioms rootCostPotentialDelta

end BB6.Agent9RootCost
