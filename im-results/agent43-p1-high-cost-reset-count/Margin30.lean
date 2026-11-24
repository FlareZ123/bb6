import MarginCert
namespace BB6.Agent43CarryCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem margin30 : MarginSafe (7*2^30-(30+3)) (requiredMargin 30 82) 0 [1] 82 [] :=
  margin_sound _ _ _ _ _ _ (by decide)
#print axioms margin30
end BB6.Agent43CarryCert
