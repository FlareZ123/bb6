import Lean
namespace BB6.Agent8Cylinder

def l0_57Nodes (r : Nat) : List (Nat × Nat) :=
  [(0,688+12288*r),(2,632+11264*r),(4,504+8960*r),(4,619+11008*r),(5,483+8576*r),(5,771+13696*r),(6,588+10432*r),(8,610+10800*r),(9,537+9496*r)]

theorem l0_57_positive (r m z : Nat)
    (h : (m,z) ∈ l0_57Nodes r) : 0<z := by
  simp only [l0_57Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_57_no256 (r m z : Nat)
    (h : (m,z) ∈ l0_57Nodes r) : ¬ 256 ∣ z := by
  simp only [l0_57Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_57_small (r m z : Nat)
    (h : (m,z) ∈ l0_57Nodes r) : m≤10 := by
  simp only [l0_57Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_57_closed (r m z t v zp : Nat)
    (hmem : (m,z) ∈ l0_57Nodes r)
    (hdiv : z=2^t*v)
    (hnext : 2*zp+1=16*(57+1024*r)+8+m+t+v) :
    (m+t+1,zp) ∈ l0_57Nodes r := by
  have hzpos : 0<z := l0_57_positive r m z hmem
  have hnodiv : ¬256 ∣ z := l0_57_no256 r m z hmem
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
  simp only [l0_57Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hm,hz⟩
  all_goals simp only [hm,hz] at hdiv hnext ⊢
  all_goals rcases hcases with h|h|h|h|h|h|h|h <;> subst t <;>
    simp_all [l0_57Nodes] <;> omega


def l1_57Nodes (r : Nat) : List (Nat × Nat) :=
  [(0,574+10240*r),(1,747+13312*r),(2,604+10752*r),(2,834+14848*r),(3,763+13568*r),(3,878+15616*r),(4,670+11904*r),(4,843+14976*r),(5,797+14144*r),(6,630+11168*r),(6,861+15264*r),(7,778+13776*r),(8,621+10984*r)]

theorem l1_57_positive (r m z : Nat)
    (h : (m,z) ∈ l1_57Nodes r) : 0<z := by
  simp only [l1_57Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_57_no256 (r m z : Nat)
    (h : (m,z) ∈ l1_57Nodes r) : ¬ 256 ∣ z := by
  simp only [l1_57Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_57_small (r m z : Nat)
    (h : (m,z) ∈ l1_57Nodes r) : m≤10 := by
  simp only [l1_57Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_57_closed (r m z t v zp : Nat)
    (hmem : (m,z) ∈ l1_57Nodes r)
    (hdiv : z=2^t*v)
    (hnext : 2*zp+1=16*(57+1024*r)+9+m+t+v) :
    (m+t+1,zp) ∈ l1_57Nodes r := by
  have hzpos : 0<z := l1_57_positive r m z hmem
  have hnodiv : ¬256 ∣ z := l1_57_no256 r m z hmem
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
  simp only [l1_57Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hm,hz⟩
  all_goals simp only [hm,hz] at hdiv hnext ⊢
  all_goals rcases hcases with h|h|h|h|h|h|h|h <;> subst t <;>
    simp_all [l1_57Nodes] <;> omega


#print axioms l0_57_closed
#print axioms l1_57_closed
end BB6.Agent8Cylinder
