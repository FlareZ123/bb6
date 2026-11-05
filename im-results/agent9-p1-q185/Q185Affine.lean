import Lean
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
namespace BB6.Agent9Q185

def q185L0Nodes (r : Nat) : List (Nat × Nat) :=
  [(0,2224+12288*r), (2,2040+11264*r), (4,1624+8960*r), (4,1995+11008*r), (5,1555+8576*r), (5,2483+13696*r), (6,1892+10432*r), (8,1960+10800*r), (9,1724+9496*r), (10,1978+10892*r), (10,2350+12940*r)]

theorem q185L0_positive (r m z : Nat) (h : (m,z) ∈ q185L0Nodes r) : 0<z := by
  simp only [q185L0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem q185L0_small (r m z : Nat) (h : (m,z) ∈ q185L0Nodes r) : m≤10 := by
  simp only [q185L0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem q185L0_no256 (r m z : Nat) (h : (m,z) ∈ q185L0Nodes r) : ¬256 ∣ z := by
  simp only [q185L0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem q185L0_closed (r m z t v zp : Nat)
    (hmem : (m,z) ∈ q185L0Nodes r)
    (hdiv : z=2^t*v)
    (hnext : 2*zp+1=16*(185+1024*r)+8+m+t+v) :
    (m+t+1,zp) ∈ q185L0Nodes r := by
  have hzpos : 0<z := q185L0_positive r m z hmem
  have hnodiv : ¬256 ∣ z := q185L0_no256 r m z hmem
  have hvpos : 0<v := by
    by_cases h0 : v=0
    · simp [h0] at hdiv
      omega
    · omega
  have ht : t<8 := by
    by_cases hh : t<8
    · exact hh
    have hd : (2:Nat)^8 ∣ 2^t := Nat.pow_dvd_pow 2 (by omega)
    have hd' : 256 ∣ 2^t := by simpa using hd
    have hzz : 256 ∣ z := by
      rcases hd' with ⟨a,ha⟩
      refine ⟨a*v, ?_⟩
      simp [hdiv, ha, Nat.mul_assoc, Nat.mul_comm]
    exact False.elim (hnodiv hzz)
  have hcases : t=0∨t=1∨t=2∨t=3∨t=4∨t=5∨t=6∨t=7 := by omega
  simp only [q185L0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hm,hz⟩
  all_goals simp only [hm,hz] at hdiv hnext ⊢
  all_goals rcases hcases with h | h | h | h | h | h | h | h <;> subst t <;>
    simp_all [q185L0Nodes] <;> omega

#print axioms q185L0_closed

def q185L1Nodes (r : Nat) : List (Nat × Nat) :=
  [(0,1854+10240*r), (1,2411+13312*r), (2,1948+10752*r), (2,2690+14848*r), (3,2459+13568*r), (3,2830+15616*r), (4,2158+11904*r), (4,2715+14976*r), (5,2565+14144*r), (6,2026+11168*r), (6,2769+15264*r), (7,2500+13776*r), (8,1994+10984*r), (9,2113+11636*r), (9,2485+13684*r), (10,1801+9914*r), (10,1987+10938*r), (10,2545+14010*r), (10,2731+15034*r)]

theorem q185L1_positive (r m z : Nat) (h : (m,z) ∈ q185L1Nodes r) : 0<z := by
  simp only [q185L1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem q185L1_small (r m z : Nat) (h : (m,z) ∈ q185L1Nodes r) : m≤10 := by
  simp only [q185L1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem q185L1_no256 (r m z : Nat) (h : (m,z) ∈ q185L1Nodes r) : ¬256 ∣ z := by
  simp only [q185L1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

theorem q185L1_closed (r m z t v zp : Nat)
    (hmem : (m,z) ∈ q185L1Nodes r)
    (hdiv : z=2^t*v)
    (hnext : 2*zp+1=16*(185+1024*r)+9+m+t+v) :
    (m+t+1,zp) ∈ q185L1Nodes r := by
  have hzpos : 0<z := q185L1_positive r m z hmem
  have hnodiv : ¬256 ∣ z := q185L1_no256 r m z hmem
  have hvpos : 0<v := by
    by_cases h0 : v=0
    · simp [h0] at hdiv
      omega
    · omega
  have ht : t<8 := by
    by_cases hh : t<8
    · exact hh
    have hd : (2:Nat)^8 ∣ 2^t := Nat.pow_dvd_pow 2 (by omega)
    have hd' : 256 ∣ 2^t := by simpa using hd
    have hzz : 256 ∣ z := by
      rcases hd' with ⟨a,ha⟩
      refine ⟨a*v, ?_⟩
      simp [hdiv, ha, Nat.mul_assoc, Nat.mul_comm]
    exact False.elim (hnodiv hzz)
  have hcases : t=0∨t=1∨t=2∨t=3∨t=4∨t=5∨t=6∨t=7 := by omega
  simp only [q185L1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hm,hz⟩
  all_goals simp only [hm,hz] at hdiv hnext ⊢
  all_goals rcases hcases with h | h | h | h | h | h | h | h <;> subst t <;>
    simp_all [q185L1Nodes] <;> omega

#print axioms q185L1_closed
end BB6.Agent9Q185
