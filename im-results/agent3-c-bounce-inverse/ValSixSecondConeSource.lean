import ValSixSecondSource
import ValSixSecondConeArithmetic
import OddOddLowVal
import OddSevenOrbit
import ReachAffine
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ValSix
open BB6.Agent46

/-- Full source-certified four-link backward obstruction, uniform over
all genuine blank times and all two-dimensional cylinder parameters. -/
theorem second_cone_blank_unreachable (x y : Nat)
    (hx:x%256=165) (hy:y%256=26) :
    ¬ BB6.Agent3.CReach x y := by
  intro h
  let a := x+y-2
  let k := (y-2)/2
  let b := a+k-2
  let l := (k-2)/2
  let c := (b+l-4)/2
  let d := (b+3*l-10)/4
  let e := (c+d-5)/2
  let f := (c+3*d-9)/4
  obtain ⟨hx16,hy16,hmod,hk4,hkeven,hsum,
    hbodd,hlodd,hl5,hs4,hs16,hbig,
    hceven,hdodd,hd5,hseven,hcsize,hfodd,hf5,hf2⟩ :=
    second_cone_arithmetic x y hx hy
  have hA : BB6.Agent3.CReach a k :=
    (second_val_six_root_iff x y hx16 hy16 hmod).mp h
  have hB : BB6.Agent3.CReach b l :=
    (BB6.Agent15.blank_reach_iff_affine a k hk4 hkeven hsum).mp hA
  have hC : BB6.Agent3.CReach c d := by
    simpa only [BB6.Agent3.CReach] using
      (BB6.Agent3.oddodd_lowval_blank_reach_iff
        b l hbodd hlodd hl5 hs4 hs16 hbig).mp hB
  have hE : BB6.Agent3.CReach e f := by
    simpa only [BB6.Agent3.CReach] using
      (BB6.Agent3.odd_seven_blank_reach_iff
        c d hceven hdodd hd5 hseven hcsize).mp hC
  rcases hE with ⟨t,ht⟩
  cases t with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n e f ht hf5 hfodd
      omega

#print axioms second_cone_blank_unreachable
end BB6.Agent3ValSix
