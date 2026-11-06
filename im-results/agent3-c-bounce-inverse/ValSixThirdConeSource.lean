import ValSixSecondSource
import ValSixThirdConeArithmetic
import OddOddLowVal
import ReachAffine
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ValSix
open BB6.Agent46

/-- A larger valuation-six cylinder is absent from the authentic
blank-origin Machine C orbit, uniformly at all section times. -/
theorem third_cone_blank_unreachable (x y : Nat)
    (hy:y%64=58) (hmod:(x+y+1)%256=192) :
    ¬ BB6.Agent3.CReach x y := by
  intro h
  let a := x+y-2
  let k := (y-2)/2
  let b := a+k-2
  let l := (k-2)/2
  let c := (b+l-4)/2
  let d := (b+3*l-10)/4
  obtain ⟨hx16,hy16,hk4,hkeven,hsum,
    hbodd,hlodd,hl5,hs4,hs16,hbig,hdodd,hd5,hsRbad⟩ :=
    third_cone_arithmetic x y hy hmod
  have hA : BB6.Agent3.CReach a k :=
    (second_val_six_root_iff x y hx16 hy16 hmod).mp h
  have hB : BB6.Agent3.CReach b l :=
    (BB6.Agent15.blank_reach_iff_affine a k hk4 hkeven hsum).mp hA
  have hC : BB6.Agent3.CReach c d := by
    simpa only [BB6.Agent3.CReach] using
      (BB6.Agent3.oddodd_lowval_blank_reach_iff
        b l hbodd hlodd hl5 hs4 hs16 hbig).mp hB
  rcases hC with ⟨t,ht⟩
  cases t with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n c d ht hd5 hdodd
      omega

#print axioms third_cone_blank_unreachable
end BB6.Agent3ValSix
