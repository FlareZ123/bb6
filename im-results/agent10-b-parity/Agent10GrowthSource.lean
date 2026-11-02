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


/-- Two exact finite starting reset indices are small enough for kernel reduction. -/
theorem A2_exact : BB6.OneDim.scalarA 2 = 227097 := by decide

/-- An explicit colossal lower bound for the *syntactic* third successor index. -/
theorem A3_huge : 10*2^113548 ≤ BB6.OneDim.scalarA (2+1) + 4 := by
  have h := scalarA_exponential_step 2
  rw [A2_exact] at h
  have hn : 227097/2=113548 := by decide
  rw [hn] at h
  exact h

#print axioms A2_exact
#print axioms A3_huge

#print axioms scalarA_exponential_step
end BB6.Agent10B
