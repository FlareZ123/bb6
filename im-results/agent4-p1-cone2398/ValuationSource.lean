import GInverse
import ValuationBound

namespace BB6.Agent4Cone

/-- A source-level uniform bound on *every* positive-output G inverse branch
whenever the shifted output counter has a finite 2-adic valuation certificate. -/
theorem GAncestor_valuation_bound (b d k c m : Nat)
    (h : BB6.P1Reduction.GAncestor b d k c)
    (hn : (d+b/2+3)%2^(m+1) ≠ 0) :
    ∃ t : Nat, t≤m ∧ d+b/2+3 = 2^t*(c+3) :=
  inverse_power_depth_bound (d+b/2+3) c m
    (BB6.P1Reduction.GAncestor_power b d k c h) hn

#print axioms BB6.Agent4Cone.GAncestor_valuation_bound
end BB6.Agent4Cone
