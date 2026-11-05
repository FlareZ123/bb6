import Q297Width
import Q297NoEven
import Q297Exception
import ConeKernel

namespace BB6.Agent8Q297
open BB6.P1Reduction BB6.Agent4Cone BB6.Agent47P1
open BB6.Agent1Quarter BB6.Agent1ShortCone BB6.Agent45TwoRoot

/-- A well-founded, source-connected proof tree for all authentic L0
odd inverse cone hubs in the q=297+1024r family. The decreasing fuel is
11-m. The theorem closes every original GAncestor input and the c=1 gate. -/
theorem l0_blocked_fuel
    (r u : Nat)
    (hu : u+4*(297+1024*r)+3=7*2^(16*(297+1024*r)))
    (hu1 : 1≤u) (hu2 : u=u2 (297+1024*r))
    (fuel : Nat) :
    ∀ b d m, fuel+m=11 →
      OddCone (4*u-4) (4*u+9) b d m → b%4=0 → d%2=1 →
      Blocked b d := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro b d m hsum hcone hb4 hdodd
    have hm : m≤10 := l0_all_r_authentic_cost r u b d m hu hu1 hcone hb4
    have hb : 8≤b := by
      have hlarge := l0_hub_large r u b d m hu hu1 hcone hb4
      omega
    have hno : ∀ k, ¬GAncestor b d k 1 := by
      intro k hanc
      obtain ⟨t,hi,_⟩ := inverseAt_complete b d k 1 hanc
      exact l0_all_r_no_exceptional r u b d m t k hu hu1 hcone hb4 hi
    refine Blocked.feeder b d hb hb4 (by omega) hno ?_
    intro k v hanc hv
    obtain ⟨t,hi,_⟩ := inverseAt_complete b d k v hanc
    have hklower := inverseAt_four_lower b d t k v hi
    have hk : 4≤k := by
      have hlarge := l0_hub_large r u b d m hu hu1 hcone hb4
      omega
    have hchild_even : (2*k-4)%2=0 := by omega
    have hchild_pos : 0<v+4 := by omega
    by_cases hveven : v%2=0
    · refine Blocked.powerLeaf (2*k-4) (v+4)
        hchild_even hchild_pos (by omega) ?_
      intro j
      have hgap := l0_all_r_no_even_power r u b d m t k v j
        hu hu1 hu2 hcone hb hb4 hdodd hi hveven
      have heq : (2*k-4)+12=2*k+8 := by omega
      simpa only [heq] using hgap
    · have hvodd : v%2=1 := by omega
      have hchildmod : (2*k-4)%4=0 ∨ (2*k-4)%4=2 := by omega
      rcases hchildmod with h0 | h2
      · have hchild := OddCone.parent b d m t k v hcone
          hb hb4 hdodd hi (by omega) hvodd
        have hmchild := l0_all_r_authentic_cost r u (2*k-4) (v+4)
          (m+t+1) hu hu1 hchild h0
        let nextFuel := 11-(m+t+1)
        have hlt : nextFuel < fuel := by dsimp [nextFuel]; omega
        have hsumChild : nextFuel+(m+t+1)=11 := by dsimp [nextFuel]; omega
        exact ih nextFuel hlt (2*k-4) (v+4) (m+t+1)
          hsumChild hchild h0 (by omega)
      · exact Blocked.modLeaf (2*k-4) (v+4)
          hchild_even hchild_pos (by omega) h2

/-- A well-founded, source-connected proof tree for all authentic L1
odd inverse cone hubs in the q=297+1024r family. The decreasing fuel is
11-m. The theorem closes every original GAncestor input and the c=1 gate. -/
theorem l1_blocked_fuel
    (r u : Nat)
    (hu : u+4*(297+1024*r)+3=7*2^(16*(297+1024*r)))
    (hu1 : 1≤u) (hu2 : u=u2 (297+1024*r))
    (fuel : Nat) :
    ∀ b d m, fuel+m=11 →
      OddCone (6*u-2) (2*u+5) b d m → b%4=0 → d%2=1 →
      Blocked b d := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro b d m hsum hcone hb4 hdodd
    have hm : m≤10 := l1_all_r_authentic_cost r u b d m hu hu1 hcone hb4
    have hb : 8≤b := by
      have hlarge := l1_hub_large r u b d m hu hu1 hcone hb4
      omega
    have hno : ∀ k, ¬GAncestor b d k 1 := by
      intro k hanc
      obtain ⟨t,hi,_⟩ := inverseAt_complete b d k 1 hanc
      exact l1_all_r_no_exceptional r u b d m t k hu hu1 hcone hb4 hi
    refine Blocked.feeder b d hb hb4 (by omega) hno ?_
    intro k v hanc hv
    obtain ⟨t,hi,_⟩ := inverseAt_complete b d k v hanc
    have hklower := inverseAt_four_lower b d t k v hi
    have hk : 4≤k := by
      have hlarge := l1_hub_large r u b d m hu hu1 hcone hb4
      omega
    have hchild_even : (2*k-4)%2=0 := by omega
    have hchild_pos : 0<v+4 := by omega
    by_cases hveven : v%2=0
    · refine Blocked.powerLeaf (2*k-4) (v+4)
        hchild_even hchild_pos (by omega) ?_
      intro j
      have hgap := l1_all_r_no_even_power r u b d m t k v j
        hu hu1 hu2 hcone hb hb4 hdodd hi hveven
      have heq : (2*k-4)+12=2*k+8 := by omega
      simpa only [heq] using hgap
    · have hvodd : v%2=1 := by omega
      have hchildmod : (2*k-4)%4=0 ∨ (2*k-4)%4=2 := by omega
      rcases hchildmod with h0 | h2
      · have hchild := OddCone.parent b d m t k v hcone
          hb hb4 hdodd hi (by omega) hvodd
        have hmchild := l1_all_r_authentic_cost r u (2*k-4) (v+4)
          (m+t+1) hu hu1 hchild h0
        let nextFuel := 11-(m+t+1)
        have hlt : nextFuel < fuel := by dsimp [nextFuel]; omega
        have hsumChild : nextFuel+(m+t+1)=11 := by dsimp [nextFuel]; omega
        exact ih nextFuel hlt (2*k-4) (v+4) (m+t+1)
          hsumChild hchild h0 (by omega)
      · exact Blocked.modLeaf (2*k-4) (v+4)
          hchild_even hchild_pos (by omega) h2

#print axioms l0_blocked_fuel
#print axioms l1_blocked_fuel
end BB6.Agent8Q297
