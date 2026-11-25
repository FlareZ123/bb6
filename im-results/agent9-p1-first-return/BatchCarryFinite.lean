import BatchCarryBit
namespace BB6.Agent9BatchCarry
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem batch10002_15000 : check 15 20007 10002 15000=true := by decide +kernel
theorem critical_reset_no_reach_10002_15000 :
    ∀ n, 10002≤n → n≤15000 → n%2=0 → ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) :=
  checked_interval 15 20007 10002 15000 (by decide) (by decide) (by decide) (by decide) batch10002_15000
#print axioms batch10002_15000
#print axioms critical_reset_no_reach_10002_15000
end BB6.Agent9BatchCarry
