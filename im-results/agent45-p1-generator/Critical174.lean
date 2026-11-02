import Quarter174Final

namespace BB6.Agent45Quarter174
/-- All genuine blank P1 halting-critical indices n=262144*q+174 are excluded. -/
theorem no_critical_174 (q : Nat) :
    ¬ BB6.Agent1.Reach 2 (14*2^(262144*q+174)-2*(262144*q+174)-10) := by
  let n : Nat := 262144*q+174
  let Y : Nat := 2^(262144*q+(174-18))
  let t : Nat := 7*Y-(q+1)
  have hY : 32*(q+174+1)≤Y := by
    simpa [Y] using Y_bound_174 q
  have hp : 2^n = 262144*Y := by
    have hn : n=(262144*q+(174-18))+18 := by omega
    rw [hn,Nat.pow_add]
    simp only [show (2:Nat)^18=262144 by decide]
    simp [Y, Nat.mul_comm]
  have ht : t+(q+1)=7*Y := by dsimp [t]; omega
  have hb : 10≤14*2^n-2*n-10 := by rw [hp]; omega
  have hm : (14*2^n-2*n-10)%4=2 := by rw [hp]; dsimp [n]; omega
  intro hr
  have hcrit := BB6.Agent50P1.critical_target_implies_three
    (14*2^n-2*n-10) hb hm (by simpa [n] using hr)
  have hroot : (14*2^n-2*n-10)-6=524288*t+523924 := by
    rw [hp]
    dsimp [n]
    omega
  rw [hroot] at hcrit
  exact (no_hub_174 q) (by simpa [t,Y] using hcrit)

#print axioms BB6.Agent45Quarter174.no_critical_174
end BB6.Agent45Quarter174
