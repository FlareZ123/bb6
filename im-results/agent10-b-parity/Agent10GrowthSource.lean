import BOneDim
import Agent10BSource
import Agent10Growth

namespace BB6.Agent10B

/-- Universal superexponential growth in the original Machine B reset-index grammar. -/
theorem scalarA_exponential_step (n : Nat) :
    10*2^((BB6.OneDim.scalarA n)/2) ≤ BB6.OneDim.scalarA (n+1)+4 := by
  have hh := G_all_time_exp (BB6.OneDim.scalarA n)
  rw [iterG_eq_source] at hh
  let z := BB6.OneDim.iterG (BB6.OneDim.scalarA n) 0
  have hz : z%2≤1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0 < 2))
  change 10*2^((BB6.OneDim.scalarA n)/2) ≤ (z+9-3*(z%2))+4
  omega

#print axioms scalarA_exponential_step
end BB6.Agent10B
