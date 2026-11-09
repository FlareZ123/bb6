import M0OddRay
import OddSevenOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0Deep
open BB6.Agent46

/-- A second, disjoint m=0 source-authentic infinite ray.
    Inverse sequence: even-right, odd/odd valuation 3,
    even-right, even-right, even/odd seven, odd/odd valuation 3.
    The last ancestor has odd right >=5 and sum=1 modulo 4. -/
theorem blank_no_deep_ray (q : Nat) :
    ¬BB6.Agent3.CReach (2321+4096*q) (3484+6144*q) := by
  intro hr
  have hp1 := (six_even_right_blank_reach_iff
    (2321+4096*q) (3484+6144*q)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have h1 : BB6.Agent3.CReach (5803+10240*q) (1741+3072*q) := by
    have hx : (2321+4096*q)+(3484+6144*q)-2=5803+10240*q := by omega
    have hy : ((3484+6144*q)-2)/2=1741+3072*q := by omega
    simpa only [hx,hy] using hp1

  have hp2 := (BB6.Agent3.oddodd_val3_blank_reach_iff
    (5803+10240*q) (1741+3072*q)
    (by omega) (by omega) (by omega) (by omega) (by omega)).mp h1
  have h2 : BB6.Agent3.CReach (3770+6656*q) (2754+4864*q) := by
    have hx : ((5803+10240*q)+(1741+3072*q)-4)/2=3770+6656*q := by omega
    have hy : ((5803+10240*q)+3*(1741+3072*q)-10)/4=2754+4864*q := by omega
    simpa only [hx,hy] using hp2

  have hp3 := (six_even_right_blank_reach_iff
    (3770+6656*q) (2754+4864*q)
    (by omega) (by omega) (by omega) (by omega)).mp h2
  have h3 : BB6.Agent3.CReach (6522+11520*q) (1376+2432*q) := by
    have hx : (3770+6656*q)+(2754+4864*q)-2=6522+11520*q := by omega
    have hy : ((2754+4864*q)-2)/2=1376+2432*q := by omega
    simpa only [hx,hy] using hp3

  have hp4 := (six_even_right_blank_reach_iff
    (6522+11520*q) (1376+2432*q)
    (by omega) (by omega) (by omega) (by omega)).mp h3
  have h4 : BB6.Agent3.CReach (7896+13952*q) (687+1216*q) := by
    have hx : (6522+11520*q)+(1376+2432*q)-2=7896+13952*q := by omega
    have hy : ((1376+2432*q)-2)/2=687+1216*q := by omega
    simpa only [hx,hy] using hp4

  have hp5 := (BB6.Agent3.odd_seven_blank_reach_iff
    (7896+13952*q) (687+1216*q)
    (by omega) (by omega) (by omega) (by omega) (by omega)).mp h4
  have h5 : BB6.Agent3.CReach (4289+7584*q) (2487+4400*q) := by
    have hx : ((7896+13952*q)+(687+1216*q)-5)/2=4289+7584*q := by omega
    have hy : ((7896+13952*q)+3*(687+1216*q)-9)/4=2487+4400*q := by omega
    simpa only [hx,hy] using hp5

  have hp6 := (BB6.Agent3.oddodd_val3_blank_reach_iff
    (4289+7584*q) (2487+4400*q)
    (by omega) (by omega) (by omega) (by omega) (by omega)).mp h5
  have h6 : BB6.Agent3.CReach (3386+5992*q) (2935+5196*q) := by
    have hx : ((4289+7584*q)+(2487+4400*q)-4)/2=3386+5992*q := by omega
    have hy : ((4289+7584*q)+3*(2487+4400*q)-10)/4=2935+5196*q := by omega
    simpa only [hx,hy] using hp6

  rcases h6 with ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
  | succ n =>
      have hh := BB6.Agent3.blank_section_odd_image n
        (3386+5992*q) (2935+5196*q) ht (by omega) (by omega)
      omega

/-- Translate the ray to high stopping parameters m=0, j=1159 mod2048. -/
theorem high_stop_mzero_1159 (j k : Nat)
    (hj : j%2048=1159)
    (hstop : k+j+3*0+5=(2:Nat)^(2*0+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let q := (j-1159)/2048
  have hjform : j=1159+2048*q := by dsimp [q]; omega
  have hp : (2:Nat)^(2*0+2)=4 := by decide
  rw [hp] at hstop
  have hkform : k=3484+6144*q := by omega
  have hxform : 2*j+3=2321+4096*q := by omega
  rw [hxform,hkform]
  exact blank_no_deep_ray q

#print axioms blank_no_deep_ray
#print axioms high_stop_mzero_1159

end BB6.Agent11M0Deep
