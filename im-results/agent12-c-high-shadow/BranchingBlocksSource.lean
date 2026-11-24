import BranchingBlocks
import DirectBlocksSource

namespace BB6.Agent12BranchingBlocks
open BB6.Agent42DirectBlocks BB6.Agent42ModularCone

theorem source_branchingBlockExcluded (x y : Nat)
    (h : branchingBlockExcluded x y=true) : ¬BB6.Agent3.CReach x y :=
  branchingBlockExcluded_sound BB6.Agent3.CReach source_direct
    BB6.Agent42ModularCone.source_parent BB6.Agent42DirectBlocks.source_forbidden x y h

theorem source_high_branching_family (m q j k : Nat)
    (hm : 5≤m) (hm4 : m%4=1) (hq : 1≤q)
    (hq32 : q%32=(11*m+4)%32)
    (hj : j+3*m+3=q*2^(2*m+2))
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) : ¬BB6.Agent3.CReach (2*j+3) k :=
  high_branching_family BB6.Agent3.CReach source_direct
    BB6.Agent42ModularCone.source_parent BB6.Agent42DirectBlocks.source_forbidden m q j k hm hm4 hq hq32 hj hstop

def highAllowedBranching (j m : Nat) : Prop :=
  highAllowedDirect j m ∧ branchingBlockExcluded (2*j+3) (highTarget j m)=false

theorem blank_halts_iff_branching_blocks : BB6.CReachBridge.RunHalts ↔
    (∃ m, lowAllowedFullModular m ∧ BB6.Agent3ValSix.valSixMixedRootDecision 1
      (2^(2*m+3)-(3*m+4))=true) ∨
    (∃ j m, highAllowedBranching j m ∧ BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
      (highTarget j m)=true) := by
  rw [blank_halts_iff_direct_blocks]
  constructor
  · rintro (h | ⟨j,m,hallow,hroot⟩)
    · exact Or.inl h
    · have hr := (BB6.Agent3ValSix.valSixMixedRootDecision_iff _ _).mp hroot
      have hnew : branchingBlockExcluded (2*j+3) (highTarget j m)=false := by
        cases hc : branchingBlockExcluded (2*j+3) (highTarget j m) with
        | false => rfl
        | true => exact False.elim ((source_branchingBlockExcluded _ _ hc) hr)
      exact Or.inr ⟨j,m,⟨hallow,hnew⟩,hroot⟩
  · rintro (h | ⟨j,m,hallow,hroot⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j,m,hallow.1,hroot⟩

#print axioms source_branchingBlockExcluded
#print axioms source_high_branching_family
#print axioms blank_halts_iff_branching_blocks
end BB6.Agent12BranchingBlocks
