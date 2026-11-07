import RightFiveEnergyParam

namespace BB6.Agent50NearDouble
open BB6.Agent28 BB6.Agent50EnergyParam

/-- A dyadic logarithmic witness instantly converts the parametric cost
sieve into a direct near-double-n lower bound, with no source-length or
reset-count restriction. -/
theorem source_right_five_near_double_cost
    (n k b m z : Nat) (hn : 14≤n)
    (hdepth : 2*k≤n)
    (hsmall : 8*(n+2)≤2^k)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z) :
    2*n+2-2*k<m := by
  let M := n-2*k
  have hM : M≤n := by dsimp [M]; omega
  have hidx : M+2*k=n := by dsimp [M]; omega
  have hsquare : (8*(n+2))*(8*(n+2)) ≤ (2^k)*(2^k) :=
    Nat.mul_le_mul hsmall hsmall
  have hpowSq : (2^k)*(2^k)=2^(2*k) := by
    rw [show 2*k=k+k by omega, Nat.pow_add]
  have hNum : 64*(n+2)*(n+2)*2^M≤2^n := by
    have hh : 64*(n+2)*(n+2) ≤ 2^(2*k) := by
      calc
        _ = (8*(n+2))*(8*(n+2)) := by
          calc
            _ = (64)*(n+2)*(n+2) := rfl
            _ = (8*8)*((n+2)*(n+2)) := by
              rw [show (64:Nat)=8*8 by decide]
              ac_rfl
            _ = (8*(n+2))*(8*(n+2)) := by ac_rfl
        _ ≤ (2^k)*(2^k) := hsquare
        _ = 2^(2*k) := hpowSq
    have hprod := Nat.mul_le_mul_right (2^M) hh
    have hpowsum : 2^(2*k)*2^M=2^n := by
      rw [←Nat.pow_add]
      congr 1
      omega
    omega
  have hcost := source_right_five_parametric_cost_gap
    n M b m z hn hM hNum h
  dsimp [M] at hcost
  omega

#print axioms BB6.Agent50NearDouble.source_right_five_near_double_cost

end BB6.Agent50NearDouble
