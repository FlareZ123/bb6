import Lean
namespace BB6.Agent8Cost11Q570
def l0Nodes (r : Nat) : List (Nat × Nat) :=
  [(0,6844+12288*r),(2,6275+11264*r),(3,5420+9728*r),(3,7702+13824*r),(4,7275+13056*r),(4,8416+15104*r),(5,6491+11648*r),(5,8203+14720*r),(6,6670+11968*r),(8,5093+9136*r),(9,7114+12760*r),(10,8125+14572*r),(11,6347+11382*r),(11,8631+15478*r)]

theorem l0_positive (r m z : Nat) (h:(m,z)∈l0Nodes r) : 0<z := by
  simp only [l0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_no256 (r m z : Nat) (h:(m,z)∈l0Nodes r) : ¬256∣z := by
  simp only [l0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_small (r m z : Nat) (h:(m,z)∈l0Nodes r) : m≤11 := by
  simp only [l0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_closed (r m z t v zp : Nat)
    (hmem : (m,z)∈l0Nodes r)
    (hdiv : z=2^t*v)
    (hnext : 2*zp+1=16*(570+1024*r)+8+m+t+v) :
    (m+t+1,zp) ∈ l0Nodes r := by
  have hzpos : 0<z := l0_positive r m z hmem
  have hnodiv : ¬256∣z := l0_no256 r m z hmem
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
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hm,hz⟩
  all_goals simp only [hm,hz] at hdiv hnext ⊢
  all_goals rcases hcases with h|h|h|h|h|h|h|h <;> subst t <;>
    simp_all [l0Nodes] <;> omega

def l1Nodes (r : Nat) : List (Nat × Nat) :=
  [(0,5704+10240*r),(1,7416+13312*r),(3,5278+9472*r),(3,6419+11520*r),(4,4922+8832*r),(4,7775+13952*r),(5,7027+12608*r),(6,5797+10400*r),(6,8080+14496*r),(7,8607+15440*r),(8,8871+15912*r),(9,5578+10004*r)]

theorem l1_positive (r m z : Nat) (h:(m,z)∈l1Nodes r) : 0<z := by
  simp only [l1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_no256 (r m z : Nat) (h:(m,z)∈l1Nodes r) : ¬256∣z := by
  simp only [l1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_small (r m z : Nat) (h:(m,z)∈l1Nodes r) : m≤11 := by
  simp only [l1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_closed (r m z t v zp : Nat)
    (hmem : (m,z)∈l1Nodes r)
    (hdiv : z=2^t*v)
    (hnext : 2*zp+1=16*(570+1024*r)+9+m+t+v) :
    (m+t+1,zp) ∈ l1Nodes r := by
  have hzpos : 0<z := l1_positive r m z hmem
  have hnodiv : ¬256∣z := l1_no256 r m z hmem
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
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hm,hz⟩
  all_goals simp only [hm,hz] at hdiv hnext ⊢
  all_goals rcases hcases with h|h|h|h|h|h|h|h <;> subst t <;>
    simp_all [l1Nodes] <;> omega

#print axioms l0_closed
#print axioms l1_closed
end BB6.Agent8Cost11Q570
