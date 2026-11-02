import OddConeMass
import P1InverseLog
namespace BB6.Agent1Quarter
open BB6.Agent47P1

theorem odd_cone_shift_code (b0 d0 b d m t k c : Nat)
    (hcone:OddCone b0 d0 b d m)
    (hb:8≤b) (hmod:b%4=0) (hd:d%2=1)
    (hi:inverseAt b d t=some (k,c)) (hk:2≤k) (hc:c%2=1) :
    2^t * (2*(((c+4)+(2*k-4)/2+3)+(m+t+1))) =
    2^t*(b0+d0+7)+(d+b/2+3) := by
  have hroot:= odd_cone_mass b0 d0 b d m hcone
  have hmass := inverseAt_odd_cost b d t k c (by omega) hmod hd hi hc
  have hpow := inverseAt_power b d t k c hi
  have hl : 2*(((c+4)+(2*k-4)/2+3)+(m+t+1)) = b0+d0+c+10 := by omega
  calc
    2^t*(2*(((c+4)+(2*k-4)/2+3)+(m+t+1))) = 2^t*(b0+d0+c+10) := by rw [hl]
    _ = 2^t*(b0+d0+7)+2^t*(c+3) := by
      have hs : b0+d0+c+10=(b0+d0+7)+(c+3) := by omega
      rw [hs,Nat.mul_add]
    _ = 2^t*(b0+d0+7)+(d+b/2+3) := by rw [hpow]

#print axioms odd_cone_shift_code
end BB6.Agent1Quarter
