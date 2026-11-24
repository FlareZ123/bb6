import DirectBlocks
import HeightConeCriterion
import EvenRightSixOrbit

namespace BB6.Agent42DirectBlocks

theorem source_direct : DirectLaw BB6.Agent3.CReach :=
  BB6.Agent46.six_even_right_blank_reach_iff

theorem source_forbidden : ForbiddenLaw BB6.Agent3.CReach :=
  BB6.Agent13TwoParent.odd_forbidden_image

theorem source_direct_block_iff (r x y u : Nat) (hu : 4≤u) (hue : u%2=0)
    (hy : y+2=2^r*u) (hx : x%4=0 ∨ x%4=3) :
    BB6.Agent3.CReach x y ↔ BB6.Agent3.CReach (x+2*y-2*(u-2)-4*r) (u-2) :=
  direct_block_iff BB6.Agent3.CReach source_direct r x y u hu hue hy hx

theorem source_high_long_direct_excluded (J m k r u : Nat)
    (hstop : k+J+3*m+4=2^(2*m+2)*(J+2))
    (hval : k+2=2^(r+1)*u) (hu : 7≤u) (hu4 : u%4=3)
    (hm : m%4=(2*(r+1)+1)%4) : ¬BB6.Agent3.CReach (2*J+1) k :=
  high_long_direct_excluded BB6.Agent3.CReach source_direct source_forbidden J m k r u hstop hval hu hu4 hm

theorem source_m1_family_excluded (s t : Nat) :
    ¬BB6.Agent3.CReach (2*m1J s t+1) (15*m1J s t+25) :=
  m1_family_excluded BB6.Agent3.CReach source_direct source_forbidden s t

theorem source_directBlockExcluded (x y : Nat) (hc : directBlockExcluded x y=true) :
    ¬BB6.Agent3.CReach x y :=
  directBlockExcluded_sound BB6.Agent3.CReach source_direct source_forbidden x y hc

open BB6.Agent42ModularCone

def highAllowedDirect (j m : Nat) : Prop :=
  highAllowedHeight j m ∧ directBlockExcluded (2*j+3) (highTarget j m)=false

theorem blank_halts_iff_direct_blocks :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedFullModular m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedDirect j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3) (highTarget j m)=true) := by
  rw [blank_halts_iff_height]
  constructor
  · rintro (h | ⟨j,m,hallow,hroot⟩)
    · exact Or.inl h
    · have hreach : BB6.Agent3.CReach (2*j+3) (highTarget j m) :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff _ _).mp hroot
      have hnew : directBlockExcluded (2*j+3) (highTarget j m)=false := by
        cases hc : directBlockExcluded (2*j+3) (highTarget j m) with
        | false => rfl
        | true => exact False.elim ((source_directBlockExcluded _ _ hc) hreach)
      exact Or.inr ⟨j,m,⟨hallow,hnew⟩,hroot⟩
  · rintro (h | ⟨j,m,hallow,hroot⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j,m,hallow.1,hroot⟩

theorem height_strict_witness :
    highAllowedFullModular 11 0 ∧ ¬highAllowedHeight 11 0 := by
  have hfast : BB6.Agent27FastBool.fastHighAllowedFullBool 11 0=true := by decide
  have hfull := (BB6.Agent27FullBool.highAllowedFullBool_iff 11 0).mpr
    ((BB6.Agent27FastBool.fastHighAllowedFullBool_iff 11 0).mp hfast)
  have ha : highAllowedFullModular 11 0 := ⟨hfull,by decide,by decide⟩
  refine ⟨ha,?_⟩
  intro h
  have hc : highHeightExcluded 11 0=true := by decide
  have hf := h.2
  rw [hc] at hf
  exact Bool.noConfusion hf

#print axioms source_direct_block_iff
#print axioms source_high_long_direct_excluded
#print axioms source_m1_family_excluded
#print axioms source_directBlockExcluded
#print axioms blank_halts_iff_direct_blocks
#print axioms height_strict_witness
end BB6.Agent42DirectBlocks
