import Lean
namespace BB6.Agent8Cylinder

def l0_281Nodes (r : Nat) : List (Nat × Nat) :=
  [(0,3376+12288*r),(2,3096+11264*r),(4,2464+8960*r),(4,3027+11008*r),(5,2359+8576*r),(5,3767+13696*r),(6,2870+10432*r),(8,2409+8752*r),(9,3460+12568*r),(10,3986+14476*r)]

theorem l0_281_positive (r m z : Nat)
    (h : (m,z) ∈ l0_281Nodes r) : 0<z := by
  simp only [l0_281Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_281_no256 (r m z : Nat)
    (h : (m,z) ∈ l0_281Nodes r) : ¬ 256 ∣ z := by
  simp only [l0_281Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_281_small (r m z : Nat)
    (h : (m,z) ∈ l0_281Nodes r) : m≤10 := by
  simp only [l0_281Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_281_closed (r m z t v zp : Nat)
    (hmem : (m,z) ∈ l0_281Nodes r)
    (hdiv : z=2^t*v)
    (hnext : 2*zp+1=16*(281+1024*r)+8+m+t+v) :
    (m+t+1,zp) ∈ l0_281Nodes r := by
  have hzpos : 0<z := l0_281_positive r m z hmem
  have hnodiv : ¬256 ∣ z := l0_281_no256 r m z hmem
  have hvpos : 0<v := by
    by_cases h0 : v=0
    · simp [h0] at hdiv
      omega
    · omega
  have ht : t<8 := by
    by_cases hh : t<8
    · exact hh
    have h8 : 8≤t := by omega
    have hd : (2:Nat)^8 ∣ 2^t := Nat.pow_dvd_pow 2 h8
    have hd' : 256 ∣ 2^t := by simpa using hd
    have hzz : 256 ∣ z := by
      rcases hd' with ⟨a,ha⟩
      refine ⟨a*v, ?_⟩
      simp [hdiv, ha, Nat.mul_assoc, Nat.mul_comm]
    exact False.elim (hnodiv hzz)
  have hcases : t=0∨t=1∨t=2∨t=3∨t=4∨t=5∨t=6∨t=7 := by omega
  simp only [l0_281Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hm,hz⟩
  all_goals simp only [hm,hz] at hdiv hnext ⊢
  all_goals rcases hcases with h|h|h|h|h|h|h|h <;> subst t <;>
    simp_all [l0_281Nodes] <;> omega


def l1_281Nodes (r : Nat) : List (Nat × Nat) :=
  [(0,2814+10240*r),(1,3659+13312*r),(2,2956+10752*r),(2,4082+14848*r),(3,3731+13568*r),(3,4294+15616*r),(4,3274+11904*r),(4,4119+14976*r),(5,3891+14144*r),(6,3073+11168*r),(6,4200+15264*r),(7,4355+15824*r),(8,4433+16104*r),(9,2781+10100*r),(10,2519+9146*r),(10,3647+13242*r)]

theorem l1_281_positive (r m z : Nat)
    (h : (m,z) ∈ l1_281Nodes r) : 0<z := by
  simp only [l1_281Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_281_no256 (r m z : Nat)
    (h : (m,z) ∈ l1_281Nodes r) : ¬ 256 ∣ z := by
  simp only [l1_281Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_281_small (r m z : Nat)
    (h : (m,z) ∈ l1_281Nodes r) : m≤10 := by
  simp only [l1_281Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_281_closed (r m z t v zp : Nat)
    (hmem : (m,z) ∈ l1_281Nodes r)
    (hdiv : z=2^t*v)
    (hnext : 2*zp+1=16*(281+1024*r)+9+m+t+v) :
    (m+t+1,zp) ∈ l1_281Nodes r := by
  have hzpos : 0<z := l1_281_positive r m z hmem
  have hnodiv : ¬256 ∣ z := l1_281_no256 r m z hmem
  have hvpos : 0<v := by
    by_cases h0 : v=0
    · simp [h0] at hdiv
      omega
    · omega
  have ht : t<8 := by
    by_cases hh : t<8
    · exact hh
    have h8 : 8≤t := by omega
    have hd : (2:Nat)^8 ∣ 2^t := Nat.pow_dvd_pow 2 h8
    have hd' : 256 ∣ 2^t := by simpa using hd
    have hzz : 256 ∣ z := by
      rcases hd' with ⟨a,ha⟩
      refine ⟨a*v, ?_⟩
      simp [hdiv, ha, Nat.mul_assoc, Nat.mul_comm]
    exact False.elim (hnodiv hzz)
  have hcases : t=0∨t=1∨t=2∨t=3∨t=4∨t=5∨t=6∨t=7 := by omega
  simp only [l1_281Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hm,hz⟩
  all_goals simp only [hm,hz] at hdiv hnext ⊢
  all_goals rcases hcases with h|h|h|h|h|h|h|h <;> subst t <;>
    simp_all [l1_281Nodes] <;> omega


#print axioms l0_281_closed
#print axioms l1_281_closed
end BB6.Agent8Cylinder
