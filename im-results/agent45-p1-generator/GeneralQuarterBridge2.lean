import P1Gate

namespace BB6.Agent45Quarter2

/-- A universal authentic P1 blank-critical reduction, with s = 7Y-q
    expressed in the subtraction-safe shifted form t = s-2. -/
theorem critical_of_quarter_hub_shift2 (r q : Nat)
    (hr : 18 ≤ r) (hmax : 2*r ≤ 1048560) (heven : r%2=0)
    (hY : 32*(q+r+1) ≤ 2^(262144*q+(r-18)))
    (hno : ¬ BB6.Agent1.Reach
      (524288*(7*2^(262144*q+(r-18))-(q+2))+(1048560-2*r)) 3) :
    ¬ BB6.Agent1.Reach 2 (14*2^(262144*q+r)-2*(262144*q+r)-10) := by
  let n : Nat := 262144*q+r
  let Y : Nat := 2^(262144*q+(r-18))
  let t : Nat := 7*Y-(q+2)
  have hY' : 32*(q+r+1)≤Y := hY
  have hp : 2^n = 262144*Y := by
    have hn : n=(262144*q+(r-18))+18 := by omega
    rw [hn,Nat.pow_add]
    simp only [show (2:Nat)^18=262144 by decide]
    simp [Y, Nat.mul_comm]
  have ht : t+(q+2)=7*Y := by dsimp [t]; omega
  have hb : 10≤14*2^n-2*n-10 := by rw [hp]; dsimp [n]; omega
  have hm : (14*2^n-2*n-10)%4=2 := by rw [hp]; dsimp [n]; omega
  intro hreach
  have hcrit := BB6.Agent50P1.critical_target_implies_three
    (14*2^n-2*n-10) hb hm (by simpa [n] using hreach)
  have hroot : (14*2^n-2*n-10)-6=524288*t+(1048560-2*r) := by
    rw [hp]
    dsimp [n]
    omega
  rw [hroot] at hcrit
  exact hno (by simpa [t,Y] using hcrit)

#print axioms BB6.Agent45Quarter2.critical_of_quarter_hub_shift2
end BB6.Agent45Quarter2
