import PairCarrySource
namespace BB6.Agent9PairCarry
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem pair15002_22500 : pairCheck 14 15003 15002 22500=true := by decide +kernel

theorem critical_reset_no_reach_15002_22500 :
    ∀ n, 15002≤n → n≤22500 → n%2=0 → ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) :=
  pair_checked_interval 14 15003 15002 22500 (by decide) (by decide) (by decide)
    (by decide) (by decide) pair15002_22500

#print axioms pair15002_22500
#print axioms critical_reset_no_reach_15002_22500
end BB6.Agent9PairCarry
