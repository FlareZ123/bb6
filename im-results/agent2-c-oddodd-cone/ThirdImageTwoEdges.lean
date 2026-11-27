import ThirdImageConeSource
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent2CThirdImageProper

open BB6.Agent46

/-- Every point in the proposed third-image hole has a genuine
    two-edge preimage chain in the unchanged original Machine C map. -/
theorem two_predecessor_edges (x y : Nat)
    (hs : (x+y)%256=36) (hy : y%128=49) :
    ∃ a k b l, secNext (b,l)=some (a,k) ∧
      secNext (a,k)=some (x,y) := by
  let a := (x+y-4)/2
  let k := (x+3*y-10)/4
  let b := (a+k-5)/2
  let l := (a+3*k-9)/4
  have hw : a%128=16 ∧ k%64=31 ∧ 5≤l ∧ b%2=1 ∧
      2≤b ∧ b<2*l ∧ x+y=2*a+4 ∧ x+3*y=4*k+10 ∧
      a+k+1=2*(b-1)+8 ∧
      (2*l-b+3)+(2*(b-1)+8)=a+2*k+2 := by
    dsimp [a,k,b,l]
    omega
  rcases hw with ⟨ha,hk,hl5,hbodd,hb2,hbl,hsum,hcost,hpow,hdyn⟩
  have hxo : x%2=1 := by omega
  have hyo : y%2=1 := by omega
  have hy5 : 5≤y := by omega
  have hs8 : (x+y)%8=4 := by omega
  have hout : secNext (a,k)=some (x,y) :=
    (BB6.Agent3.oddodd_parent_iff a k x y hxo hyo hy5 hs8).mpr
      ⟨hsum,hcost⟩
  have hb0 : b≠0 := by omega
  have hb1 : b≠1 := by omega
  have hl0 : l≠0 := by omega
  have hreg : ¬ 2*l≤b := by omega
  have hbe : ¬ b%2=0 := by omega
  have hpre : BB6.Agent46.sectionPreimageCriterion b l a k := by
    unfold BB6.Agent46.sectionPreimageCriterion
    simp only [if_neg hb0,if_neg hb1,if_neg hl0,
      if_neg hreg,if_neg hbe]
    refine ⟨0,?_,?_⟩ <;> simp <;> omega
  have hin : secNext (b,l)=some (a,k) :=
    (BB6.Agent46.complete_section_inverse b l a k (by omega)).mpr hpre
  exact ⟨a,k,b,l,hin,hout⟩

/-- No point in this cylinder has three section predecessors from
    any starting configuration: the second predecessor contradicts the
    source-universal odd-image congruence theorem. -/
theorem no_three_predecessor_edges (x y : Nat)
    (hs : (x+y)%256=36) (hy : y%128=49) :
    ¬ ∃ c d b l a k,
      secNext (c,d)=some (b,l) ∧
      secNext (b,l)=some (a,k) ∧
      secNext (a,k)=some (x,y) := by
  rintro ⟨c,d,b,l,a,k,hfirst,hsecond,hlast⟩
  obtain ⟨ha,hk⟩ :=
    BB6.Agent2CThirdImage.first_parent_cone a k x y hs hy hlast
  have hcrit : BB6.Agent46.sectionPreimageCriterion b l a k :=
    (BB6.Agent46.complete_section_inverse b l a k (by omega)).mp hsecond
  obtain ⟨hl5,hlodd,hbad⟩ :=
    BB6.Agent2CThirdImage.all_parent_forbidden b l a k ha hk hcrit
  have himage := BB6.Agent3.section_odd_image c d b l hfirst hl5 hlodd
  omega

/-- New strict section-image cone I_2 minus I_3 with natural
    positive density 1/32768 in full coordinate-space. -/
theorem strict_second_vs_third_image (x y : Nat)
    (hs : (x+y)%256=36) (hy : y%128=49) :
    (∃ a k b l, secNext (b,l)=some (a,k) ∧
        secNext (a,k)=some (x,y)) ∧
    ¬ (∃ c d b l a k, secNext (c,d)=some (b,l) ∧
        secNext (b,l)=some (a,k) ∧
        secNext (a,k)=some (x,y)) :=
  ⟨two_predecessor_edges x y hs hy,
   no_three_predecessor_edges x y hs hy⟩

#print axioms two_predecessor_edges
#print axioms no_three_predecessor_edges
#print axioms strict_second_vs_third_image

end BB6.Agent2CThirdImageProper
