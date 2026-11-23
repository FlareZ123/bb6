import ValSixMixedNormalize

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace BB6.Agent34QEvenH5Probe

/-- The odd-bounce parent Q in the q-even R-parent classification. -/
def qEvenQ (t z : Nat) : Nat × Nat :=
  (3720+3556*t-7586*z, 6173+5902*t-12591*z)

/-- hcong = 1 control: (t,z)=(20,7), with 7t+10 ≤ 32z ≤ 12+11t. -/
#eval qEvenQ 20 7
#eval BB6.Agent3ValSix.valSixMixedNormalize (qEvenQ 20 7).1 (qEvenQ 20 7).2
#eval BB6.Agent3ValSix.valSixMixedRootDecision (qEvenQ 20 7).1 (qEvenQ 20 7).2

/-- hcong = 5 sample: (t,z)=(12,3), also satisfying the high-stop inequalities. -/
#eval qEvenQ 12 3
#eval BB6.Agent3ValSix.valSixMixedNormalize (qEvenQ 12 3).1 (qEvenQ 12 3).2
#eval BB6.Agent3ValSix.valSixMixedRootDecision (qEvenQ 12 3).1 (qEvenQ 12 3).2

end BB6.Agent34QEvenH5Probe
