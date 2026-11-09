import M0FourRoot
import EvenOddFourExact
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0ValTwo
open BB6.Agent46

/-- A source-authentic six-inverse-edge obstruction for an entire
    independent high-stopping m=0 ray. Four forced reductions are supplied
    by the uniform modulo-four theorem; the fifth is the exact even/odd
    valuation-two inverse; the sixth is even-right source uniqueness.
    The final odd-right state has mass 2 mod4, impossible for the true
    blank-origin Machine C section. -/
theorem blank_no_valtwo_ray (q : Nat) :
    ¬BB6.Agent3.CReach (2065+4096*q) (3100+6144*q) := by
  intro hr
  have h4 : BB6.Agent3.CReach (7024+13952*q) (611+1216*q) := by
    have hstart : BB6.Agent3.CReach
      (17+64*(32+64*q)) (28+96*(32+64*q)) := by
      have hx : 17+64*(32+64*q)=2065+4096*q := by omega
      have hy : 28+96*(32+64*q)=3100+6144*q := by omega
      simpa only [hx,hy] using hr
    have hh := BB6.Agent11M0Four.mzero_four_reach
      (32+64*q) (by omega) hstart
    have hx : 48+218*(32+64*q)=7024+13952*q := by omega
    have hy : 3+19*(32+64*q)=611+1216*q := by omega
    simpa only [hx,hy] using hh

  have hp5 := (BB6.Agent3.evenodd_four_blank_reach_iff
    (7024+13952*q) (611+1216*q)
    (by omega) (by omega) (by omega) (by omega)).mp h4
  have h5 : BB6.Agent3.CReach (3815+7584*q) (2212+4400*q) := by
    have hx : ((7024+13952*q)+(611+1216*q)-5)/2=3815+7584*q := by omega
    have hy : ((7024+13952*q)+3*(611+1216*q)-9)/4=2212+4400*q := by omega
    change (∃ n, BB6.Agent8Section.run secNext n (some (5,1)) =
      some (3815+7584*q,2212+4400*q))
    simpa only [hx,hy] using hp5

  have hp6 := (six_even_right_blank_reach_iff
    (3815+7584*q) (2212+4400*q)
    (by omega) (by omega) (by omega) (by omega)).mp h5
  have h6 : BB6.Agent3.CReach (6025+11984*q) (1105+2200*q) := by
    have hx : (3815+7584*q)+(2212+4400*q)-2=6025+11984*q := by omega
    have hy : ((2212+4400*q)-2)/2=1105+2200*q := by omega
    simpa only [hx,hy] using hp6

  rcases h6 with ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      have hh := BB6.Agent3.blank_section_odd_image n
        (6025+11984*q) (1105+2200*q) ht (by omega) (by omega)
      omega

/-- High stopping m=0, j=1031 modulo2048 is unreachable from blank. -/
theorem high_stop_mzero_1031 (j k : Nat)
    (hj : j%2048=1031)
    (hstop : k+j+3*0+5=(2:Nat)^(2*0+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let q := (j-1031)/2048
  have hjform : j=1031+2048*q := by dsimp [q]; omega
  have hp : (2:Nat)^(2*0+2)=4 := by decide
  rw [hp] at hstop
  have hkform : k=3100+6144*q := by omega
  have hxform : 2*j+3=2065+4096*q := by omega
  rw [hxform,hkform]
  exact blank_no_valtwo_ray q

#print axioms blank_no_valtwo_ray
#print axioms high_stop_mzero_1031

end BB6.Agent11M0ValTwo
