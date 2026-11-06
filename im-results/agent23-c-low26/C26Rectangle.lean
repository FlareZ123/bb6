import OddOddLowVal
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent23C26
open BB6.Agent3 BB6.Agent46

/-- Two-dimensional all-time blank-root exclusion; the inverse chain is E,E,O,E,E. -/
theorem blank_no_rectangle (u v : Nat) (hv : 1 ≤ v) :
    ¬ BB6.Agent3.CReach (64*u+1) (256*v+26) := by
  intro h
  have h1 : BB6.Agent3.CReach (64*u+256*v+25) (128*v+12) := by
    have hh := (six_even_right_blank_reach_iff (64*u+1) (256*v+26)
      (by omega) (by omega) (by omega) (by omega)).mp h
    have hx : (64*u+1)+(256*v+26)-2=64*u+256*v+25 := by omega
    have hy : ((256*v+26)-2)/2=128*v+12 := by omega
    simpa only [hx,hy] using hh
  have h2 : BB6.Agent3.CReach (64*u+384*v+35) (64*v+5) := by
    have hh := (six_even_right_blank_reach_iff (64*u+256*v+25) (128*v+12)
      (by omega) (by omega) (by omega) (by omega)).mp h1
    have hx : (64*u+256*v+25)+(128*v+12)-2=64*u+384*v+35 := by omega
    have hy : ((128*v+12)-2)/2=64*v+5 := by omega
    simpa only [hx,hy] using hh
  have h3 : BB6.Agent3.CReach (32*u+224*v+18) (16*u+144*v+10) := by
    have hh := (oddodd_lowval_blank_reach_iff (64*u+384*v+35) (64*v+5)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp h2
    have hx : ((64*u+384*v+35)+(64*v+5)-4)/2=32*u+224*v+18 := by omega
    have hy : ((64*u+384*v+35)+3*(64*v+5)-10)/4=16*u+144*v+10 := by omega
    simpa only [hx,hy,BB6.Agent3.CReach] using hh
  have h4 : BB6.Agent3.CReach (48*u+368*v+26) (8*u+72*v+4) := by
    have hh := (six_even_right_blank_reach_iff (32*u+224*v+18) (16*u+144*v+10)
      (by omega) (by omega) (by omega) (by omega)).mp h3
    have hx : (32*u+224*v+18)+(16*u+144*v+10)-2=48*u+368*v+26 := by omega
    have hy : ((16*u+144*v+10)-2)/2=8*u+72*v+4 := by omega
    simpa only [hx,hy] using hh
  have h5 : BB6.Agent3.CReach (56*u+440*v+28) (4*u+36*v+1) := by
    have hh := (six_even_right_blank_reach_iff (48*u+368*v+26) (8*u+72*v+4)
      (by omega) (by omega) (by omega) (by omega)).mp h4
    have hx : (48*u+368*v+26)+(8*u+72*v+4)-2=56*u+440*v+28 := by omega
    have hy : ((8*u+72*v+4)-2)/2=4*u+36*v+1 := by omega
    simpa only [hx,hy] using hh
  rcases h5 with ⟨n,hn⟩
  cases n with
  | zero =>
      simp [BB6.Agent8Section.run] at hn
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n
        (56*u+440*v+28) (4*u+36*v+1) hn (by omega) (by omega)
      omega

#print axioms blank_no_rectangle
end BB6.Agent23C26
