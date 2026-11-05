import ConeKernel
import OddConeMass
import P1FiniteInverse
import ShortConeBridge

namespace BB6.Agent8Generic11
open BB6.P1Reduction BB6.Agent4Cone BB6.Agent47P1
open BB6.Agent1Quarter BB6.Agent1ShortCone

/-- Abstract source-sound finite-cone induction: four genuine terminal
    obligations suffice to exclude the root at every blank time. -/
theorem blocked_of_uniform_cone_exit11
    (b0 d0 : Nat)
    (hcost : ∀ b d m, OddCone b0 d0 b d m → b%4=0 → m≤11)
    (hwidth : ∀ b d m, OddCone b0 d0 b d m → b%4=0 → 24≤b)
    (hno : ∀ b d m t k, OddCone b0 d0 b d m → b%4=0 →
      inverseAt b d t=some (k,1) → False)
    (heven : ∀ b d m t k c j, OddCone b0 d0 b d m →
      8≤b → b%4=0 → d%2=1 →
      inverseAt b d t=some (k,c) → c%2=0 →
      2*k+8≠14*2^j)
    (hroot4 : b0%4=0) (hrootodd : d0%2=1) :
    Blocked b0 d0 := by
  have haux (fuel : Nat) :
      ∀ b d m, fuel+m=12 →
      OddCone b0 d0 b d m → b%4=0 → d%2=1 → Blocked b d := by
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro b d m hsum hcone hb4 hdodd
      have hm : m≤11 := hcost b d m hcone hb4
      have hb : 8≤b := by have hlarge := hwidth b d m hcone hb4; omega
      have hnone : ∀ k, ¬GAncestor b d k 1 := by
        intro k hanc
        obtain ⟨t,hi,_⟩ := inverseAt_complete b d k 1 hanc
        exact hno b d m t k hcone hb4 hi
      refine Blocked.feeder b d hb hb4 (by omega) hnone ?_
      intro k v hanc hv
      obtain ⟨t,hi,_⟩ := inverseAt_complete b d k v hanc
      have hklower := inverseAt_four_lower b d t k v hi
      have hk : 4≤k := by have hlarge := hwidth b d m hcone hb4; omega
      have hchild_even : (2*k-4)%2=0 := by omega
      have hchild_pos : 0<v+4 := by omega
      by_cases hveven : v%2=0
      · refine Blocked.powerLeaf (2*k-4) (v+4)
          hchild_even hchild_pos (by omega) ?_
        intro j
        have hgap := heven b d m t k v j hcone hb hb4 hdodd hi hveven
        have heq : (2*k-4)+12=2*k+8 := by omega
        simpa only [heq] using hgap
      · have hvodd : v%2=1 := by omega
        have hchildmod : (2*k-4)%4=0 ∨ (2*k-4)%4=2 := by omega
        rcases hchildmod with h0 | h2
        · have hchild := OddCone.parent b d m t k v hcone
            hb hb4 hdodd hi (by omega) hvodd
          have hmchild := hcost (2*k-4) (v+4) (m+t+1) hchild h0
          let nextFuel := 12-(m+t+1)
          have hlt : nextFuel < fuel := by dsimp [nextFuel]; omega
          have hsumChild : nextFuel+(m+t+1)=12 := by dsimp [nextFuel]; omega
          exact ih nextFuel hlt (2*k-4) (v+4) (m+t+1)
            hsumChild hchild h0 (by omega)
        · exact Blocked.modLeaf (2*k-4) (v+4)
            hchild_even hchild_pos (by omega) h2
  exact haux 12 b0 d0 0 (by omega) OddCone.root hroot4 hrootodd

#print axioms blocked_of_uniform_cone_exit11
end BB6.Agent8Generic
