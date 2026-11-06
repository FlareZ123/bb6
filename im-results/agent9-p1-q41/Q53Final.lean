import Q41Finite
import UniformUniversalCylinder

namespace BB6.Agent9Q53
open BB6.Agent9Q41
def nodes0 : List (Nat×Nat) := [
  (0,640), (2,588), (4,469), (4,576), (5,503), (5,664), (6,440),
  (6,574), (6,762), (8,467), (8,514), (8,541), (9,473), (9,665),
  (9,702), (10,441), (10,783), (11,437), (11,608), (11,653), (11,824),
  (12,737), (12,845), (13,802), (13,856), (14,510), (14,537), (14,835),
  (14,862), (15,486), (15,635), (15,703), (15,852), (16,454), (16,542),
  (16,678), (16,861), (17,445), (17,489), (17,557), (17,866), (18,869),
  (19,653), (19,871)
]
theorem root0 : (0,640)∈nodes0 := by decide
theorem check0 : BB6.Agent9Q33.checkGraph 856 nodes0 = true := by decide
theorem boundCheck0 :
  nodes0.all (fun p => decide (p.1≤41 ∧ ¬1024∣p.2)) = true := by decide
theorem closed0 (m z t v zp : Nat) (hm : (m,z)∈nodes0)
    (hd:z=2^t*v) (hn:2*zp+1=856+m+t+v) :
    (m+t+1,zp)∈nodes0 :=
  BB6.Agent9Q41.closed_of_check 856 nodes0 check0 boundCheck0 m z t v zp hm hd hn
theorem small0 (m z : Nat) (hm : (m,z)∈nodes0) : m≤41 := by
  have h := (List.all_eq_true.mp boundCheck0) (m,z) hm
  exact (of_decide_eq_true h).1
theorem no1024_0 (m z : Nat) (hm : (m,z)∈nodes0) : ¬1024∣z := by
  have h := (List.all_eq_true.mp boundCheck0) (m,z) hm
  exact (of_decide_eq_true h).2

def nodes1 : List (Nat×Nat) := [
  (0,534), (1,695), (2,562), (2,776), (3,710), (3,817), (4,570),
  (4,838), (5,527), (5,715), (5,849), (6,479), (6,573), (6,640),
  (6,694), (6,788), (6,855), (7,751), (7,778), (7,825), (8,605),
  (8,807), (8,844), (9,512), (9,854), (11,453), (11,561), (12,660),
  (12,714), (13,439), (13,466), (13,764), (13,791), (14,437), (14,613),
  (14,654), (14,830), (15,443), (15,626), (15,762), (15,850), (16,531),
  (16,599), (16,643), (16,657), (17,438)
]
theorem root1 : (0,534)∈nodes1 := by decide
theorem check1 : BB6.Agent9Q33.checkGraph 857 nodes1 = true := by decide
theorem boundCheck1 :
  nodes1.all (fun p => decide (p.1≤41 ∧ ¬1024∣p.2)) = true := by decide
theorem closed1 (m z t v zp : Nat) (hm : (m,z)∈nodes1)
    (hd:z=2^t*v) (hn:2*zp+1=857+m+t+v) :
    (m+t+1,zp)∈nodes1 :=
  BB6.Agent9Q41.closed_of_check 857 nodes1 check1 boundCheck1 m z t v zp hm hd hn
theorem small1 (m z : Nat) (hm : (m,z)∈nodes1) : m≤41 := by
  have h := (List.all_eq_true.mp boundCheck1) (m,z) hm
  exact (of_decide_eq_true h).1
theorem no1024_1 (m z : Nat) (hm : (m,z)∈nodes1) : ¬1024∣z := by
  have h := (List.all_eq_true.mp boundCheck1) (m,z) hm
  exact (of_decide_eq_true h).2

/-- Original P1 gateway exclusion in the infinite q=53+2^51*r cylinder. -/
theorem blank_no_critical_850_plus_2pow55 (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(53+2^(10+41)*r)+2) -
       2*(16*(53+2^(10+41)*r)+2)-10) := by
  exact BB6.Agent9UniformUniversal.universal_blank_critical_cylinder
    53 (by decide) nodes0 nodes1 root0 root1
    closed0 closed1 small0 small1 no1024_0 no1024_1 r

#print axioms blank_no_critical_850_plus_2pow55
end BB6.Agent9Q53
