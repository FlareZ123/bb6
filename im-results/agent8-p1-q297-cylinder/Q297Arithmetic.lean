import Lean
namespace BB6.Agent8Q297

def l0Nodes (r : Nat) : List (Nat × Nat) :=
  [(0,3568+12288*r),(2,3272+11264*r),(4,2604+8960*r),(4,3199+11008*r),(5,2493+8576*r),(5,3981+13696*r),(6,3033+10432*r),(7,2708+9312*r),(7,3899+13408*r),(8,3737+12848*r),(9,4252+14616*r),(10,4510+15500*r)]

theorem l0_positive (r m z : Nat)
    (h : (m,z) ∈ l0Nodes r) : 0<z := by
  simp only [l0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_no256 (r m z : Nat)
    (h : (m,z) ∈ l0Nodes r) : ¬ 256 ∣ z := by
  simp only [l0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_small (r m z : Nat)
    (h : (m,z) ∈ l0Nodes r) : m≤10 := by
  simp only [l0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_closed (r m z t v zp : Nat)
    (hmem : (m,z) ∈ l0Nodes r)
    (hdiv : z=2^t*v)
    (hnext : 2*zp+1=16*(297+1024*r)+8+m+t+v) :
    (m+t+1,zp) ∈ l0Nodes r := by
  have hzpos : 0<z := l0_positive r m z hmem
  have hnodiv : ¬256 ∣ z := l0_no256 r m z hmem
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
  simp only [l0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hm,hz⟩
  all_goals simp only [hm,hz] at hdiv hnext ⊢
  all_goals rcases hcases with h|h|h|h|h|h|h|h <;> subst t <;>
    simp_all [l0Nodes] <;> omega

def l1Nodes (r : Nat) : List (Nat × Nat) :=
  [(0,2974+10240*r),(1,3867+13312*r),(2,3124+10752*r),(2,4314+14848*r),(3,3943+13568*r),(3,4538+15616*r),(4,3460+11904*r),(4,4353+14976*r),(5,4112+14144*r),(7,3411+11728*r),(8,4089+14056*r),(9,2641+9076*r),(10,2513+8634*r),(10,3705+12730*r)]

theorem l1_positive (r m z : Nat)
    (h : (m,z) ∈ l1Nodes r) : 0<z := by
  simp only [l1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_no256 (r m z : Nat)
    (h : (m,z) ∈ l1Nodes r) : ¬ 256 ∣ z := by
  simp only [l1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_small (r m z : Nat)
    (h : (m,z) ∈ l1Nodes r) : m≤10 := by
  simp only [l1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_closed (r m z t v zp : Nat)
    (hmem : (m,z) ∈ l1Nodes r)
    (hdiv : z=2^t*v)
    (hnext : 2*zp+1=16*(297+1024*r)+9+m+t+v) :
    (m+t+1,zp) ∈ l1Nodes r := by
  have hzpos : 0<z := l1_positive r m z hmem
  have hnodiv : ¬256 ∣ z := l1_no256 r m z hmem
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
  simp only [l1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hm,hz⟩
  all_goals simp only [hm,hz] at hdiv hnext ⊢
  all_goals rcases hcases with h|h|h|h|h|h|h|h <;> subst t <;>
    simp_all [l1Nodes] <;> omega

#print axioms l0_closed
#print axioms l1_closed
end BB6.Agent8Q297
