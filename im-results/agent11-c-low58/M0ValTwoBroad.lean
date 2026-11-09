import M0FourRoot
import EvenOddFourExact
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0ValTwoBroad
open BB6.Agent46

/-- The entire m=0 subray t=32+32q (not merely t=32+64q)
    is eliminated by six exact original-source predecessor steps.
    Source parents 5 and 6 use the previously unintegrated
    even/odd valuation-two and complete even-right inverse rules.
    The normalized output is in the genuine blank forbidden parity
    wedge for EVERY q, with no inverse-fuel or time bound. -/
theorem blank_no_valtwo_broad (q : Nat) :
    ¬BB6.Agent3.CReach (2065+2048*q) (3100+3072*q) := by
  intro hr
  have h4 : BB6.Agent3.CReach (7024+6976*q) (611+608*q) := by
    have hstart : BB6.Agent3.CReach
      (17+64*(32+32*q)) (28+96*(32+32*q)) := by
      have hx : 17+64*(32+32*q)=2065+2048*q := by omega
      have hy : 28+96*(32+32*q)=3100+3072*q := by omega
      simpa only [hx,hy] using hr
    have hh := BB6.Agent11M0Four.mzero_four_reach
      (32+32*q) (by omega) hstart
    have hx : 48+218*(32+32*q)=7024+6976*q := by omega
    have hy : 3+19*(32+32*q)=611+608*q := by omega
    simpa only [hx,hy] using hh

  have hp5 := (BB6.Agent3.evenodd_four_blank_reach_iff
    (7024+6976*q) (611+608*q)
    (by omega) (by omega) (by omega) (by omega)).mp h4
  have h5 : BB6.Agent3.CReach (3815+3792*q) (2212+2200*q) := by
    have hx : ((7024+6976*q)+(611+608*q)-5)/2=3815+3792*q := by omega
    have hy : ((7024+6976*q)+3*(611+608*q)-9)/4=2212+2200*q := by omega
    change (∃ n, BB6.Agent8Section.run secNext n (some (5,1)) =
      some (3815+3792*q,2212+2200*q))
    simpa only [hx,hy] using hp5

  have hp6 := (six_even_right_blank_reach_iff
    (3815+3792*q) (2212+2200*q)
    (by omega) (by omega) (by omega) (by omega)).mp h5
  have h6 : BB6.Agent3.CReach (6025+5992*q) (1105+1100*q) := by
    have hx : (3815+3792*q)+(2212+2200*q)-2=6025+5992*q := by omega
    have hy : ((2212+2200*q)-2)/2=1105+1100*q := by omega
    simpa only [hx,hy] using hp6

  rcases h6 with ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      have hh := BB6.Agent3.blank_section_odd_image n
        (6025+5992*q) (1105+1100*q) ht (by omega) (by omega)
      omega

/-- Broad high stopping exclusion: every m=0 j>=1031 with j=7
    mod1024, including both parities of the t/32 quotient. -/
theorem high_stop_mzero_7mod1024 (j k : Nat)
    (hj : j%1024=7) (hjmin : 1031≤j)
    (hstop : k+j+3*0+5=(2:Nat)^(2*0+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let q := (j-1031)/1024
  have hjform : j=1031+1024*q := by dsimp [q]; omega
  have hp : (2:Nat)^(2*0+2)=4 := by decide
  rw [hp] at hstop
  have hkform : k=3100+3072*q := by omega
  have hxform : 2*j+3=2065+2048*q := by omega
  rw [hxform,hkform]
  exact blank_no_valtwo_broad q

#print axioms blank_no_valtwo_broad
#print axioms high_stop_mzero_7mod1024

end BB6.Agent11M0ValTwoBroad
