import UniformP1GateSmall
import Q33Finite
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
namespace BB6.Agent8Q41
open BB6.Agent9Q33 BB6.Agent8PrecisionP1Small

def graph0 : List (Nat×Nat) := [
  (0,496),
  (2,456),
  (4,364),
  (4,447),
  (5,349),
  (5,557),
  (6,425),
  (7,380),
  (7,547),
  (8,525),
  (9,598),
  (10,635),
  (11,486),
  (11,654),
  (12,580),
  (12,664),
  (13,459),
  (13,501),
  (14,483),
  (14,504),
  (15,411),
  (15,580),
  (16,465),
  (16,629),
  (17,572),
  (17,654),
  (18,626),
  (18,667),
  (19,504),
  (19,674),
  (20,593),
  (20,678),
  (21,510),
  (21,638),
  (22,405),
  (22,597),
  (22,661),
  (23,374),
  (23,470),
  (23,502),
  (23,545),
  (23,641),
  (23,673),
  (24,530),
  (24,578),
  (24,594),
  (25,437),
  (25,461),
  (25,469)
]

theorem root0 : (0,496) ∈ graph0 := by decide

theorem check0 : checkGraph 664 graph0 = true := by decide

theorem bound0 :
  graph0.all (fun p => decide (p.1 ≤ 25 ∧ ¬1024∣p.2)) = true := by decide

theorem small0 (m z : Nat) (hm : (m,z) ∈ graph0) : m ≤ 25 := by
  have hb := (List.all_eq_true.mp bound0) (m,z) hm
  exact (of_decide_eq_true hb).1

theorem nodiv0 (m z : Nat) (hm : (m,z) ∈ graph0) : ¬1024∣z := by
  have hb := (List.all_eq_true.mp bound0) (m,z) hm
  exact (of_decide_eq_true hb).2

theorem closed0 (m z t v zp : Nat)
    (hm : (m,z) ∈ graph0) (hd : z=2^t*v)
    (hn : 2*zp+1 = 664+m+t+v) :
    (m+t+1,zp) ∈ graph0 := by
  have hmod : ¬1024∣z := nodiv0 m z hm
  have ht : t<10 := by
    by_cases hh : t<10
    · exact hh
    have hp : 1024∣2^t := by
      have h := Nat.pow_dvd_pow 2 (by omega : 10≤t)
      simpa using h
    exact False.elim (hmod (Nat.dvd_trans hp ⟨v,hd⟩))
  exact checkGraph_sound 664 graph0 check0 m z t v zp hm ht hd hn

def graph1 : List (Nat×Nat) := [
  (0,414),
  (1,539),
  (2,436),
  (2,602),
  (3,551),
  (3,634),
  (4,484),
  (4,609),
  (5,576),
  (7,479),
  (8,575),
  (9,372),
  (11,346),
  (11,430),
  (12,342),
  (12,384),
  (13,509),
  (13,530),
  (14,424),
  (14,593),
  (15,387),
  (15,551),
  (16,533),
  (16,615),
  (17,352),
  (17,393),
  (18,367),
  (18,537),
  (19,344),
  (19,429),
  (20,343),
  (20,556),
  (21,364),
  (21,428),
  (21,620),
  (23,434),
  (23,450),
  (23,498),
  (24,389),
  (24,397),
  (24,421)
]

theorem root1 : (0,414) ∈ graph1 := by decide

theorem check1 : checkGraph 665 graph1 = true := by decide

theorem bound1 :
  graph1.all (fun p => decide (p.1 ≤ 25 ∧ ¬1024∣p.2)) = true := by decide

theorem small1 (m z : Nat) (hm : (m,z) ∈ graph1) : m ≤ 25 := by
  have hb := (List.all_eq_true.mp bound1) (m,z) hm
  exact (of_decide_eq_true hb).1

theorem nodiv1 (m z : Nat) (hm : (m,z) ∈ graph1) : ¬1024∣z := by
  have hb := (List.all_eq_true.mp bound1) (m,z) hm
  exact (of_decide_eq_true hb).2

theorem closed1 (m z t v zp : Nat)
    (hm : (m,z) ∈ graph1) (hd : z=2^t*v)
    (hn : 2*zp+1 = 665+m+t+v) :
    (m+t+1,zp) ∈ graph1 := by
  have hmod : ¬1024∣z := nodiv1 m z hm
  have ht : t<10 := by
    by_cases hh : t<10
    · exact hh
    have hp : 1024∣2^t := by
      have h := Nat.pow_dvd_pow 2 (by omega : 10≤t)
      simpa using h
    exact False.elim (hmod (Nat.dvd_trans hp ⟨v,hd⟩))
  exact checkGraph_sound 665 graph1 check1 m z t v zp hm ht hd hn

/-- Entire q=41+2^35*r family excluded at the authentic blank-root P1
critical gateway, using the two finite certificates above. -/
theorem no_critical_q41_plus_2pow35 (r : Nat) :
    ¬ BB6.Agent1.Reach 2
     (14*2^(16*(41+2^35*r)+2)-2*(16*(41+2^35*r)+2)-10) := by
  exact all_lifted_gateways_excluded_small 41 r 25 (by decide) (by decide)
    graph0 graph1 root0 root1 closed0 closed1 small0 small1 nodiv0 nodiv1

/-- Equivalent direct exponent family n=658+2^39*r. -/
theorem blank_no_critical_658_plus_2pow39 (r : Nat) :
    ¬ BB6.Agent1.Reach 2
     (14*2^(658+2^39*r)-2*(658+2^39*r)-10) := by
  have h := no_critical_q41_plus_2pow35 r
  have heq : 16*(41+2^35*r)+2 = 658+2^39*r := by omega
  simpa only [heq] using h

#print axioms no_critical_q41_plus_2pow35
#print axioms blank_no_critical_658_plus_2pow39
end BB6.Agent8Q41
