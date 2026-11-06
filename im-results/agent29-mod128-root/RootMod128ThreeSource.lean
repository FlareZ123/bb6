import RootMod128Source
import RootMod128ThreeArithmetic
import OddOddLowVal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29New
open BB6.Agent46

/-- New unbounded three-forced-link authentic Machine C blank-root
exclusion in the complementary x=5 mod16 sector of the valuation-five
sum96 gate. The final predecessor has odd right and forbidden sum 1 mod4. -/
theorem blank_no_three_link (x y : Nat)
    (hx : x%64=37) (hs : (x+y+1)%128=96) (hy : 58≤y) :
    ¬ BB6.Agent3.CReach x y := by
  intro h
  let a := x+y-2
  let k := (y-2)/2
  let b := a+k-2
  let l := (k-2)/2
  let c := (b+l-4)/2
  let d := (b+3*l-10)/4
  have hprops := three_link_properties x y hx hs hy
  obtain ⟨hk4,hkeven,hsum,hbodd,hlodd,hl5,hmod4,hmod16,hsize,hd5,hdodd,hbad⟩ :=
    hprops
  have hx8 : x%8=5 := by omega
  have h1 : BB6.Agent3.CReach a k :=
    (sum96_forced_root_iff x y hx8 (by omega) (by omega) hs (by omega)).mp h
  have h2 : BB6.Agent3.CReach b l :=
    (BB6.Agent15.blank_reach_iff_affine a k hk4 hkeven hsum).mp h1
  have h3 : BB6.Agent3.CReach c d :=
    (BB6.Agent3.oddodd_lowval_blank_reach_iff b l
      hbodd hlodd hl5 hmod4 hmod16 hsize).mp h2
  rcases h3 with ⟨time,hr⟩
  cases time with
  | zero =>
    simp [BB6.Agent8Section.run] at hr
    omega
  | succ t =>
    have hi := BB6.Agent3.blank_section_odd_image t c d hr hd5 hdodd
    omega

#print axioms blank_no_three_link
end BB6.Agent29New
