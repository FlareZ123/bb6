import RootMod128Source
import RootMod128FourArithmetic
import OddOddLowVal
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29New
open BB6.Agent46

/-- New four-forced-link original-blank Machine C exclusion, all
natural x and y, without runtime cutoff. -/
theorem blank_no_four_link (x y : Nat)
    (hx : x%128=117) (hs : (x+y+1)%128=96) (hy : 106≤y) :
    ¬ BB6.Agent3.CReach x y := by
  intro h
  let a := x+y-2
  let k := (y-2)/2
  let b := a+k-2
  let l := (k-2)/2
  let c := (b+l-4)/2
  let d := (b+3*l-10)/4
  let e := c+d-2
  let f := (d-2)/2
  have hprops := four_link_properties x y hx hs hy
  obtain ⟨hk4,hkeven,hsum,hbodd,hlodd,hl5,hmod4,hmod16,hsize,
    hd6,hdeven,hnot0,hnot7,hf5,hfodd,hbad⟩ := hprops
  have hx8 : x%8=5 := by omega
  have h1 : BB6.Agent3.CReach a k :=
    (sum96_forced_root_iff x y hx8 (by omega) (by omega) hs (by omega)).mp h
  have h2 : BB6.Agent3.CReach b l :=
    (BB6.Agent15.blank_reach_iff_affine a k hk4 hkeven hsum).mp h1
  have h3 : BB6.Agent3.CReach c d :=
    (BB6.Agent3.oddodd_lowval_blank_reach_iff b l
      hbodd hlodd hl5 hmod4 hmod16 hsize).mp h2
  have h4 : BB6.Agent3.CReach e f :=
    (six_even_right_blank_reach_iff c d hd6 hdeven hnot0 hnot7).mp h3
  rcases h4 with ⟨time,hr⟩
  cases time with
  | zero =>
    simp [BB6.Agent8Section.run] at hr
    omega
  | succ t =>
    have hi := BB6.Agent3.blank_section_odd_image t e f hr hf5 hfodd
    omega

#print axioms blank_no_four_link
end BB6.Agent29New
