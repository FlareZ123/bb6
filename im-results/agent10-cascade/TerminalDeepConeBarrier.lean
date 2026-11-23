import RootConeComposition

set_option maxHeartbeats 0

namespace CascadeTerminalDeepCone
open CascadeResetInverse CascadeRootConeComposition CascadeSweep

/-- A symbolic 17-node, two-fork source-reset cone: fourteen
    consecutive even-ray states and three off-spine vertices.
    Nothing here treats missing odd valuations as impossible:
    universal source ResetParent coverage is an explicit hypothesis. -/
def deepCone (J : Nat) (ray : Nat → Nat)
    (oddTwo oddEight evenEight x : Nat) : Prop :=
  (∃ k : Nat, k≤13 ∧ x=ray (J-k)) ∨
    x=oddTwo ∨ x=oddEight ∨ x=evenEight

/-- Complete two-fork structural root barrier. Once the authentic
    source parent relation at the fourteen ray vertices and the
    three off-spine vertices has been classified exactly, the
    true blank root is excluded without any finite simulation,
    source-orbit truncation, or induction on an arbitrary time bound. -/
theorem deep_thirteen_step_two_fork_root_dead
    (J : Nat) (ray : Nat → Nat)
    (oddTwo oddEight evenEight : Nat)
    (hJ : 13≤J)
    (hmainRoot : ∀ k, k≤13 → ray (J-k) ≠ 2)
    (hoddTwoRoot : oddTwo≠2)
    (hoddEightRoot : oddEight≠2)
    (hevenEightRoot : evenEight≠2)
    (hterminal : ∀ r, ¬ ResetParent r (ray J))
    (hnormal : ∀ k, 1≤k → k≤13 → k≠2 → k≠8 →
      ∀ r, ResetParent r (ray (J-k)) →
        r=ray (J-(k-1)))
    (hforkTwo : ∀ r, ResetParent r (ray (J-2)) →
      r=ray (J-1) ∨ r=oddTwo)
    (hforkEight : ∀ r, ResetParent r (ray (J-8)) →
      r=ray (J-7) ∨ r=oddEight)
    (hoddTwoLeaf : ∀ r, ¬ ResetParent r oddTwo)
    (hoddEightParent : ∀ r, ResetParent r oddEight → r=evenEight)
    (hevenEightLeaf : ∀ r, ¬ ResetParent r evenEight) :
    ¬ ReachC (2,0) (ray (J-13),0) := by
  let P : Nat → Prop := deepCone J ray oddTwo oddEight evenEight
  have hnoroot : ¬ P 2 := by
    intro hx
    change (∃ k : Nat, k≤13 ∧ 2=ray (J-k)) ∨
      2=oddTwo ∨ 2=oddEight ∨ 2=evenEight at hx
    rcases hx with ⟨k,hk,heq⟩ | heq | heq | heq
    · exact (hmainRoot k hk) heq.symm
    · exact hoddTwoRoot heq.symm
    · exact hoddEightRoot heq.symm
    · exact hevenEightRoot heq.symm
  have hback : ∀ u r, P u → ResetParent r u → P r := by
    intro u r hu hr
    change (∃ k : Nat, k≤13 ∧ u=ray (J-k)) ∨
      u=oddTwo ∨ u=oddEight ∨ u=evenEight at hu
    change (∃ k : Nat, k≤13 ∧ r=ray (J-k)) ∨
      r=oddTwo ∨ r=oddEight ∨ r=evenEight
    rcases hu with ⟨k,hk,heq⟩ | heq | heq | heq
    · subst u
      by_cases hk0 : k=0
      · subst k
        exact False.elim ((hterminal r) (by simpa using hr))
      · by_cases hk2 : k=2
        · subst k
          rcases hforkTwo r hr with hw | ho
          · exact Or.inl ⟨1,by omega,hw⟩
          · exact Or.inr (Or.inl ho)
        · by_cases hk8 : k=8
          · subst k
            rcases hforkEight r hr with hw | ho
            · exact Or.inl ⟨7,by omega,hw⟩
            · exact Or.inr (Or.inr (Or.inl ho))
          · have heq : r=ray (J-(k-1)) :=
              hnormal k (by omega) hk hk2 hk8 r hr
            exact Or.inl ⟨k-1,by omega,heq⟩
    · subst u
      exact False.elim ((hoddTwoLeaf r) hr)
    · subst u
      exact Or.inr (Or.inr (Or.inr (hoddEightParent r hr)))
    · subst u
      exact False.elim ((hevenEightLeaf r) hr)
  exact backward_closed_root_barrier P hnoroot hback
    (ray (J-13)) (by
      change (∃ k : Nat, k≤13 ∧ ray (J-13)=ray (J-k)) ∨
        ray (J-13)=oddTwo ∨ ray (J-13)=oddEight ∨
          ray (J-13)=evenEight
      exact Or.inl ⟨13,by omega,rfl⟩)

#print axioms deep_thirteen_step_two_fork_root_dead
end CascadeTerminalDeepCone
