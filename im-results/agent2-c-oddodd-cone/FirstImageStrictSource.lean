import OddOddConeSource
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent2CFirstImageStrict

open BB6.Agent46

/-- Every point in the new 48/64 missing-blank cone actually has
    a genuine incoming original-source section edge. It is therefore
    an image theorem, rather than just an arithmetic nonreachability
    criterion. The explicit parent is the depth-zero even-bounce case. -/
theorem one_predecessor_edge (x y : Nat)
    (hx : x%8=5) (hy : y%8=3)
    (hy8 : 8≤y) (hs : (x+y)%64=48) :
    ∃ a k, secNext (a,k)=some (x,y) := by
  let a := (x+y-4)/2
  let k := (x+3*y-10)/4
  have hw : 2≤a ∧ 1≤k ∧ a%2=0 ∧ a<2*k ∧
      x+y=2*(a-1)+6 ∧
      (2*k-a+3)+(2*(a-1)+6)=x+2*y := by
    dsimp [a,k]
    omega
  rcases hw with ⟨ha2,hk1,haeven,haHigh,hpower,hcost⟩
  have ha0 : a≠0 := by omega
  have ha1 : a≠1 := by omega
  have hk0 : k≠0 := by omega
  have hreg : ¬ 2*k≤a := by omega
  have hpre : sectionPreimageCriterion a k x y := by
    unfold sectionPreimageCriterion
    simp only [if_neg ha0,if_neg ha1,if_neg hk0,
      if_neg hreg,if_pos haeven]
    refine ⟨0,?_,?_⟩ <;> simp <;> omega
  exact ⟨a,k,(complete_section_inverse a k x y (by omega)).mpr hpre⟩

/-- No state in the same cone admits two genuine original-section
    predecessor edges from ANY source. Every possible immediate parent
    violates the universal one-step odd-image congruence invariant. -/
theorem no_two_predecessor_edges (x y : Nat)
    (hx : x%8=5) (hy : y%8=3)
    (hy8 : 8≤y) (hs : (x+y)%64=48) :
    ¬ ∃ b l a k,
      secNext (b,l)=some (a,k) ∧ secNext (a,k)=some (x,y) := by
  rintro ⟨b,l,a,k,hfirst,hlast⟩
  have hcrit : sectionPreimageCriterion a k x y :=
    (complete_section_inverse a k x y (by omega)).mp hlast
  obtain ⟨hk5,hkodd,hbad⟩ :=
    BB6.Agent2COddOddCone.all_parent_forbidden a k x y hx hy hs hcrit
  have hi := BB6.Agent3.section_odd_image b l a k hfirst hk5 hkodd
  omega

/-- A complete constructive source theorem for a positive-density
    strict first-versus-second section-image cylinder: I1 minus I2.
    The ambient density of this 48/64 cylinder is 1/512. -/
theorem strict_first_vs_second_image (x y : Nat)
    (hx : x%8=5) (hy : y%8=3)
    (hy8 : 8≤y) (hs : (x+y)%64=48) :
    (∃ a k, secNext (a,k)=some (x,y)) ∧
    ¬ (∃ b l a k,
      secNext (b,l)=some (a,k) ∧ secNext (a,k)=some (x,y)) :=
  ⟨one_predecessor_edge x y hx hy hy8 hs,
   no_two_predecessor_edges x y hx hy hy8 hs⟩

#print axioms one_predecessor_edge
#print axioms no_two_predecessor_edges
#print axioms strict_first_vs_second_image

end BB6.Agent2CFirstImageStrict
