import Q33Finite
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB6.Agent9Q41
open BB6.Agent9Q33

/-- A kernel-checked graph-to-source interface; this does not use native_decide. -/
theorem closed_of_check (L : Nat) (nodes : List (Nat×Nat))
    (hc : checkGraph L nodes = true)
    (hb : nodes.all (fun p => decide (p.1≤41 ∧ ¬1024∣p.2)) = true)
    (m z t v zp : Nat) (hm : (m,z)∈nodes)
    (hdiv : z=2^t*v) (hn : 2*zp+1=L+m+t+v) :
    (m+t+1,zp)∈nodes := by
  have hnode := (List.all_eq_true.mp hb) (m,z) hm
  have hnodiv : ¬1024∣z := (of_decide_eq_true hnode).2
  have ht : t<10 := by
    by_cases hh : t<10
    · exact hh
    have hp : 1024∣2^t := by
      have hd : (2:Nat)^10∣2^t := Nat.pow_dvd_pow 2 (by omega)
      simpa using hd
    exact False.elim (hnodiv (Nat.dvd_trans hp ⟨v,hdiv⟩))
  exact checkGraph_sound L nodes hc m z t v zp hm ht hdiv hn

/-- Exact complete scalar closure for q=41, feeder 0. -/
def nodes0 : List (Nat×Nat) := [
  (0,496), (2,456), (4,364), (4,447), (5,349), (5,557),
  (6,425), (7,380), (7,547), (8,525), (9,598), (10,635),
  (11,486), (11,654), (12,580), (12,664), (13,459), (13,501),
  (14,483), (14,504), (15,411), (15,580), (16,465), (16,629),
  (17,572), (17,654), (18,626), (18,667), (19,504), (19,674),
  (20,593), (20,678), (21,510), (21,638), (22,405), (22,597),
  (22,661), (23,374), (23,470), (23,502), (23,545), (23,641),
  (23,673), (24,530), (24,578), (24,594), (25,437), (25,461),
  (25,469)
]

theorem root0 : (0,496)∈nodes0 := by decide
theorem check0 : checkGraph 664 nodes0 = true := by decide
theorem boundCheck0 :
    nodes0.all (fun p => decide (p.1≤41 ∧ ¬1024∣p.2)) = true := by decide
theorem closed0 (m z t v zp : Nat)
    (hm : (m,z)∈nodes0) (hd : z=2^t*v)
    (hn : 2*zp+1=664+m+t+v) :
    (m+t+1,zp)∈nodes0 :=
  closed_of_check 664 nodes0 check0 boundCheck0 m z t v zp hm hd hn
theorem small0 (m z : Nat) (hm : (m,z)∈nodes0) : m≤41 := by
  have h := (List.all_eq_true.mp boundCheck0) (m,z) hm
  exact (of_decide_eq_true h).1
theorem no1024_0 (m z : Nat) (hm : (m,z)∈nodes0) : ¬1024∣z := by
  have h := (List.all_eq_true.mp boundCheck0) (m,z) hm
  exact (of_decide_eq_true h).2

/-- Exact complete scalar closure for q=41, feeder 1. -/
def nodes1 : List (Nat×Nat) := [
  (0,414), (1,539), (2,436), (2,602), (3,551), (3,634),
  (4,484), (4,609), (5,576), (7,479), (8,575), (9,372),
  (11,346), (11,430), (12,342), (12,384), (13,509), (13,530),
  (14,424), (14,593), (15,387), (15,551), (16,533), (16,615),
  (17,352), (17,393), (18,367), (18,537), (19,344), (19,429),
  (20,343), (20,556), (21,364), (21,428), (21,620), (23,434),
  (23,450), (23,498), (24,389), (24,397), (24,421)
]

theorem root1 : (0,414)∈nodes1 := by decide
theorem check1 : checkGraph 665 nodes1 = true := by decide
theorem boundCheck1 :
    nodes1.all (fun p => decide (p.1≤41 ∧ ¬1024∣p.2)) = true := by decide
theorem closed1 (m z t v zp : Nat)
    (hm : (m,z)∈nodes1) (hd : z=2^t*v)
    (hn : 2*zp+1=665+m+t+v) :
    (m+t+1,zp)∈nodes1 :=
  closed_of_check 665 nodes1 check1 boundCheck1 m z t v zp hm hd hn
theorem small1 (m z : Nat) (hm : (m,z)∈nodes1) : m≤41 := by
  have h := (List.all_eq_true.mp boundCheck1) (m,z) hm
  exact (of_decide_eq_true h).1
theorem no1024_1 (m z : Nat) (hm : (m,z)∈nodes1) : ¬1024∣z := by
  have h := (List.all_eq_true.mp boundCheck1) (m,z) hm
  exact (of_decide_eq_true h).2

#print axioms closed0
#print axioms closed1
end BB6.Agent9Q41
