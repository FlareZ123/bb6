import MixedMod16SevenInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- A genuine depth-one bounce edge for every high odd/even section
    output satisfying (x+y+1)%16=8. Its existence is proved from the
    source-complete inverse iff, with explicit original-source witnesses. -/
theorem mod16_eight_bounce_construct (x y : Nat)
    (hx : x%2=1) (he : y%2=0) (hmod : (x+y+1)%16=8)
    (hy : 64≤y) :
    secNext ((x+y+1)/4-3, (x+2*y-((x+y+1)/4-3)-10)/2) =
      some (x,y) := by
  let a := (x+y+1)/4-3
  let k := (x+2*y-a-10)/2
  have ha2 : 2≤a := by dsimp [a]; omega
  have haodd : a%2=1 := by dsimp [a]; omega
  have hk1 : 1≤k := by dsimp [a,k]; omega
  have hregion : a<2*k := by dsimp [a,k]; omega
  have hpow : x+y+1=2*(2*(a-1)+8) := by dsimp [a]; omega
  have hcost : (2*k-a+3)+(2*(a-1)+8)+3*1=x+2*y+2 := by
    dsimp [a,k]
    omega
  have hcrit : sectionPreimageCriterion a k x y := by
    unfold sectionPreimageCriterion
    have hn0:a≠0 := by omega
    have hn1:a≠1 := by omega
    have hkn:k≠0 := by omega
    have hnot : ¬ 2*k≤a := by omega
    have heven : ¬a%2=0 := by omega
    simp only [if_neg hn0,if_neg hn1,if_neg hkn,if_neg hnot,if_neg heven]
    exact ⟨1,hpow,hcost⟩
  exact (complete_section_inverse a k x y (by omega)).mpr hcrit

#print axioms mod16_eight_bounce_construct
end BB6.Agent3
