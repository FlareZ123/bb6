import AdaptiveP1Gate
import Q41Finite

namespace BB6.Agent8Q41Adaptive26
open BB6.Agent8Q41 BB6.Agent8AdaptiveP1

/-- Certified absence of valuations reaching the local precision 26-m. -/
theorem bound26_0 :
    graph0.all (fun p => decide (p.1≤25 ∧ ¬2^(26-p.1)∣p.2)) = true := by decide

theorem bound26_1 :
    graph1.all (fun p => decide (p.1≤25 ∧ ¬2^(26-p.1)∣p.2)) = true := by decide

theorem precise0 (m z : Nat) (h : (m,z)∈graph0) : ¬2^(26-m)∣z := by
  have b := (List.all_eq_true.mp bound26_0) (m,z) h
  exact (of_decide_eq_true b).2

theorem precise1 (m z : Nat) (h : (m,z)∈graph1) : ¬2^(26-m)∣z := by
  have b := (List.all_eq_true.mp bound26_1) (m,z) h
  exact (of_decide_eq_true b).2

/-- Original-source P1 gateway excluded at q=41+2^26*r for every r. -/
theorem no_critical_q41_plus_2pow26 (r : Nat) :
    ¬ BB6.Agent1.Reach 2
     (14*2^(16*(41+2^26*r)+2)-2*(16*(41+2^26*r)+2)-10) := by
  exact all_lifted_gateways_excluded_adaptive 26 41 r 25
    (by decide) (by decide) (by decide)
    graph0 graph1 root0 root1 closed0 closed1 small0 small1
    precise0 precise1 nodiv0 nodiv1

/-- Direct exponent family n=658+2^30*r. -/
theorem blank_no_critical_658_plus_2pow30 (r : Nat) :
    ¬ BB6.Agent1.Reach 2
     (14*2^(658+2^30*r)-2*(658+2^30*r)-10) := by
  have h := no_critical_q41_plus_2pow26 r
  have heq : 16*(41+2^26*r)+2 = 658+2^30*r := by omega
  simpa only [heq] using h

#print axioms no_critical_q41_plus_2pow26
#print axioms blank_no_critical_658_plus_2pow30
end BB6.Agent8Q41Adaptive26
