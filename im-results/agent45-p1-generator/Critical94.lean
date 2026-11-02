import Cert94

namespace BB6.Agent45Generator

/-- Excludes every authentic P1 blank-reachability critical index n=65536*q+94.
Relies on the original source-checked critical_target_implies_three and finite
certified inverse cone in Cert94. This does not decide P1 or BB(6). -/
theorem no_critical_94 (q : Nat) :
    ¬ BB6.Agent1.Reach 2 (14*2^(65536*q+94)-2*(65536*q+94)-10) := by
  let n : Nat := 65536*q+94
  let X : Nat := 2^(65536*q+(94-16))
  let t : Nat := 7*X-(q+1)
  have hX : 32*(q+1)≤X := by
    simpa [X] using X_bound q 94 (by omega)
  have hp : 2^n = 65536*X := by
    have hn : n=(65536*q+(94-16))+16 := by omega
    rw [hn,Nat.pow_add]
    simp only [show (2:Nat)^16=65536 by decide]
    simp [X, Nat.mul_comm]
  have ht : t+(q+1)=7*X := by dsimp [t]; omega
  have hb : 10≤14*2^n-2*n-10 := by rw [hp]; omega
  have hm : (14*2^n-2*n-10)%4=2 := by rw [hp]; dsimp [n]; omega
  intro hr
  have hcrit := BB6.Agent50P1.critical_target_implies_three
    (14*2^n-2*n-10) hb hm (by simpa [n] using hr)
  have hroot : (14*2^n-2*n-10)-6=131072*t+130868 := by
    rw [hp]
    dsimp [n]
    omega
  rw [hroot] at hcrit
  exact (no_hub_94 q) (by simpa [t,X] using hcrit)

#print axioms BB6.Agent45Generator.no_critical_94
end BB6.Agent45Generator
