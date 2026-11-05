import Q33AffineNodes

namespace BB6.Agent9Affine

theorem closed0 (r m z t v zp : Nat)
    (hm : (m,z) ∈ decode r nodes0) (hd : z=2^t*v)
    (hn : 2*zp+1=16*(33+P*r)+8+m+t+v) :
    (m+t+1,zp)∈decode r nodes0 := by
  have hn' : 2*zp+1=16*P*r+536+m+t+v := by
    simp only [Nat.mul_add,Nat.mul_assoc] at hn ⊢
    omega
  exact check_sound 536 P nodes0 check0 r m z t v zp hm hd hn'

theorem closed1 (r m z t v zp : Nat)
    (hm : (m,z) ∈ decode r nodes1) (hd : z=2^t*v)
    (hn : 2*zp+1=16*(33+P*r)+9+m+t+v) :
    (m+t+1,zp)∈decode r nodes1 := by
  have hn' : 2*zp+1=16*P*r+537+m+t+v := by
    simp only [Nat.mul_add,Nat.mul_assoc] at hn ⊢
    omega
  exact check_sound 537 P nodes1 check1 r m z t v zp hm hd hn'

theorem bounds0 (r m z : Nat) (hm : (m,z) ∈ decode r nodes0) :
    m≤41 ∧ ¬1024∣z :=
  check_bounds 536 P nodes0 check0 r m z hm

theorem bounds1 (r m z : Nat) (hm : (m,z) ∈ decode r nodes1) :
    m≤41 ∧ ¬1024∣z :=
  check_bounds 537 P nodes1 check1 r m z hm

theorem root0 (r : Nat) : (0,12*(33+P*r)+4)∈decode r nodes0 := by
  apply List.mem_map.mpr
  refine ⟨(0,400,12*P), ?_, ?_⟩
  · decide
  · change (0,400+12*P*r)=(0,12*(33+P*r)+4)
    simp [Nat.mul_add,Nat.mul_assoc]
    omega

theorem root1 (r : Nat) : (0,10*(33+P*r)+4)∈decode r nodes1 := by
  apply List.mem_map.mpr
  refine ⟨(0,334,10*P), ?_, ?_⟩
  · decide
  · change (0,334+10*P*r)=(0,10*(33+P*r)+4)
    simp [Nat.mul_add,Nat.mul_assoc]
    omega

#print axioms closed0
#print axioms closed1
#print axioms root0
#print axioms root1
end BB6.Agent9Affine
