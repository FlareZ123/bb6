import UniformP1GateK
import Q41Finite

namespace BB6.Agent8Q41Precision8
open BB6.Agent8Q41 BB6.Agent8PrecisionP1K

/-- Both q=41 feeder graphs avoid the 256-divisibility class. -/
theorem bound8_0 :
    graph0.all (fun p => decide (p.1≤25 ∧ ¬256∣p.2)) = true := by decide

theorem bound8_1 :
    graph1.all (fun p => decide (p.1≤25 ∧ ¬256∣p.2)) = true := by decide

theorem no256_0 (m z : Nat) (h : (m,z)∈graph0) : ¬256∣z := by
  have b := (List.all_eq_true.mp bound8_0) (m,z) h
  exact (of_decide_eq_true b).2

theorem no256_1 (m z : Nat) (h : (m,z)∈graph1) : ¬256∣z := by
  have b := (List.all_eq_true.mp bound8_1) (m,z) h
  exact (of_decide_eq_true b).2

/-- Source-authentic P1 blank-root exclusion at every q=41+2^33*r. -/
theorem no_critical_q41_plus_2pow33 (r : Nat) :
    ¬ BB6.Agent1.Reach 2
     (14*2^(16*(41+2^33*r)+2)-2*(16*(41+2^33*r)+2)-10) := by
  exact all_lifted_gateways_excluded_K 8 41 r 25
    (by decide) (by decide) (by decide)
    graph0 graph1 root0 root1 closed0 closed1 small0 small1 no256_0 no256_1

/-- Equivalent family of exponents n=658+2^37*r. -/
theorem blank_no_critical_658_plus_2pow37 (r : Nat) :
    ¬ BB6.Agent1.Reach 2
     (14*2^(658+2^37*r)-2*(658+2^37*r)-10) := by
  have h := no_critical_q41_plus_2pow33 r
  have heq : 16*(41+2^33*r)+2 = 658+2^37*r := by omega
  simpa only [heq] using h

#print axioms no_critical_q41_plus_2pow33
#print axioms blank_no_critical_658_plus_2pow37
end BB6.Agent8Q41Precision8
