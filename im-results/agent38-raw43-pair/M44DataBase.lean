import M44Pred0
import M44Pred1
import M44Delta0
import M44Delta1
import M44Rows
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 10000
namespace BB6.Agent38M44
def cert : Cert := ⟨114,1898,⟨pred0,delta0⟩,⟨pred1,delta1⟩,allRows⟩
theorem initLeft : pushWord cert.left [3,0,7] 0 = some 3 := by decide
theorem initRight : pushWord cert.right W0 0 = some 12 := by decide
theorem initGood : cert.good 0 3 12 = true := by decide
theorem emptyL : (17,0) ∈ cert.left.pred.get 0 := by decide
theorem emptyR : (17,0) ∈ cert.right.pred.get 0 := by decide
end BB6.Agent38M44
