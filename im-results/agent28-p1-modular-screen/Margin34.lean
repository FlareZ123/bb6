import MarginCert
namespace BB6.Agent28CarryBudget
open BB6.Agent43CarryCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem margin34 : MarginSafe (7*2^34-(34+3)) (requiredMargin 34 30) 0 [1] 30 [] :=
  margin_sound _ _ _ _ _ _ (by decide +kernel)
#print axioms margin34
end BB6.Agent28CarryBudget
