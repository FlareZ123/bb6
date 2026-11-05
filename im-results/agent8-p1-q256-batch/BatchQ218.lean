import Lean
namespace BB6.Agent8BatchQ218
def l0Nodes (r : Nat) : List (Nat × Nat) :=
  [(0,2620+3072*r),(2,2403+2816*r),(3,2076+2432*r),(3,2950+3456*r),(4,2787+3264*r),(4,3224+3776*r),(5,2487+2912*r),(5,3143+3680*r),(6,2556+2992*r),(8,2390+2796*r),(9,2071+2422*r)]

theorem l0_positive (r m z : Nat) (h:(m,z)∈l0Nodes r) : 0<z := by
  simp only [l0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_no256 (r m z : Nat) (h:(m,z)∈l0Nodes r) : ¬256∣z := by
  simp only [l0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_small (r m z : Nat) (h:(m,z)∈l0Nodes r) : m≤10 := by
  simp only [l0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l0_closed (r m z t v zp : Nat)
    (hmem : (m,z)∈l0Nodes r)
    (hdiv : z=2^t*v)
    (hnext : 2*zp+1=16*(218+256*r)+8+m+t+v) :
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
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hm,hz⟩
  all_goals simp only [hm,hz] at hdiv hnext ⊢
  all_goals rcases hcases with h|h|h|h|h|h|h|h <;> subst t <;>
    simp_all [l0Nodes] <;> omega

def l1Nodes (r : Nat) : List (Nat × Nat) :=
  [(0,2184+2560*r),(1,2840+3328*r),(3,2022+2368*r),(3,2459+2880*r),(4,1886+2208*r),(4,2979+3488*r),(5,2693+3152*r),(6,2222+2600*r),(6,3097+3624*r),(7,2862+3348*r),(8,2307+2698*r)]

theorem l1_positive (r m z : Nat) (h:(m,z)∈l1Nodes r) : 0<z := by
  simp only [l1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_no256 (r m z : Nat) (h:(m,z)∈l1Nodes r) : ¬256∣z := by
  simp only [l1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_small (r m z : Nat) (h:(m,z)∈l1Nodes r) : m≤10 := by
  simp only [l1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem l1_closed (r m z t v zp : Nat)
    (hmem : (m,z)∈l1Nodes r)
    (hdiv : z=2^t*v)
    (hnext : 2*zp+1=16*(218+256*r)+9+m+t+v) :
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
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hm,hz⟩
  all_goals simp only [hm,hz] at hdiv hnext ⊢
  all_goals rcases hcases with h|h|h|h|h|h|h|h <;> subst t <;>
    simp_all [l1Nodes] <;> omega

#print axioms l0_closed
#print axioms l1_closed
end BB6.Agent8BatchQ218
