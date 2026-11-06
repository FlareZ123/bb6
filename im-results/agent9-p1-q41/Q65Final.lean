import Q41Finite
import UniformUniversalCylinder

namespace BB6.Agent9Q65
open BB6.Agent9Q41
def nodes0 : List (Nat×Nat) := [
  (0,784), (2,720), (4,574), (4,705), (5,550), (5,878), (6,571),
  (6,801), (6,965), (7,549), (7,664), (7,746), (7,812), (7,927),
  (7,1009), (8,859), (8,900), (8,933), (9,714), (9,957), (9,994),
  (10,611), (10,753), (10,885), (10,1025), (11,570), (11,641), (11,707),
  (11,777), (11,834), (11,905), (11,971), (11,1041), (12,814), (12,946),
  (13,672), (13,738), (14,866), (14,899), (15,715), (15,980), (16,615),
  (16,1021), (17,839), (17,1042), (18,553), (18,1053), (19,543), (19,793),
  (19,809), (19,1059)
]
theorem root0 : (0,784)∈nodes0 := by decide
theorem check0 : BB6.Agent9Q33.checkGraph 1048 nodes0 = true := by decide
theorem boundCheck0 :
  nodes0.all (fun p => decide (p.1≤41 ∧ ¬1024∣p.2)) = true := by decide
theorem closed0 (m z t v zp : Nat) (hm : (m,z)∈nodes0)
    (hd:z=2^t*v) (hn:2*zp+1=1048+m+t+v) :
    (m+t+1,zp)∈nodes0 :=
  BB6.Agent9Q41.closed_of_check 1048 nodes0 check0 boundCheck0 m z t v zp hm hd hn
theorem small0 (m z : Nat) (hm : (m,z)∈nodes0) : m≤41 := by
  have h := (List.all_eq_true.mp boundCheck0) (m,z) hm
  exact (of_decide_eq_true h).1
theorem no1024_0 (m z : Nat) (hm : (m,z)∈nodes0) : ¬1024∣z := by
  have h := (List.all_eq_true.mp boundCheck0) (m,z) hm
  exact (of_decide_eq_true h).2

def nodes1 : List (Nat×Nat) := [
  (0,654), (1,851), (2,688), (2,950), (3,869), (3,1000), (4,763),
  (4,960), (5,612), (5,776), (5,1006), (7,647), (7,680), (7,721),
  (8,604), (8,851), (8,888), (9,558), (9,698), (9,830), (9,972),
  (11,640), (11,772), (12,585), (12,651), (13,690), (13,723), (14,627),
  (14,892), (15,571), (15,977), (16,817), (16,1020), (17,542), (17,1042)
]
theorem root1 : (0,654)∈nodes1 := by decide
theorem check1 : BB6.Agent9Q33.checkGraph 1049 nodes1 = true := by decide
theorem boundCheck1 :
  nodes1.all (fun p => decide (p.1≤41 ∧ ¬1024∣p.2)) = true := by decide
theorem closed1 (m z t v zp : Nat) (hm : (m,z)∈nodes1)
    (hd:z=2^t*v) (hn:2*zp+1=1049+m+t+v) :
    (m+t+1,zp)∈nodes1 :=
  BB6.Agent9Q41.closed_of_check 1049 nodes1 check1 boundCheck1 m z t v zp hm hd hn
theorem small1 (m z : Nat) (hm : (m,z)∈nodes1) : m≤41 := by
  have h := (List.all_eq_true.mp boundCheck1) (m,z) hm
  exact (of_decide_eq_true h).1
theorem no1024_1 (m z : Nat) (hm : (m,z)∈nodes1) : ¬1024∣z := by
  have h := (List.all_eq_true.mp boundCheck1) (m,z) hm
  exact (of_decide_eq_true h).2

/-- Original P1 gateway exclusion in the infinite q=65+2^51*r cylinder. -/
theorem blank_no_critical_1042_plus_2pow55 (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(65+2^(10+41)*r)+2) -
       2*(16*(65+2^(10+41)*r)+2)-10) := by
  exact BB6.Agent9UniformUniversal.universal_blank_critical_cylinder
    65 (by decide) nodes0 nodes1 root0 root1
    closed0 closed1 small0 small1 no1024_0 no1024_1 r

#print axioms blank_no_critical_1042_plus_2pow55
end BB6.Agent9Q65
