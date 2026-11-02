import CMod128Eighteen
import Lean.Elab.Tactic.Omega

namespace BB6.CMod128SeventyTwo
open BB6.CBack BB6.CRange BB6.CHubSplit BB6.CMod128Eighteen

private theorem eq3 {a b c d e f : Nat}
    (h1:a=d) (h2:b=e) (h3:c=f) :
    ((a,b,c):Nat×Nat×Nat)=(d,e,f) := by
  cases h1; cases h2; cases h3; rfl

/-- The first odd-section high-zero option is ruled out by another
zero-left portal and an even-c high-one impossibility. -/
theorem no_first_high (t:Nat) :
    ¬ BB6CLine.Reach (416*t+233,0,608*t+342) := by
  intro h
  have hi : BB6CLine.Reach ((416*t+226)+7,0,(608*t+338)+4) := by simpa using h
  rcases reached_high_kzero_prev (416*t+226) (608*t+338) hi with ⟨k,hodd,hA,hr⟩
  have hZ : BB6CLine.Reach (0,208*t+115,608*t+342) := by
    have he : (0,k,(608*t+338)+4)=(0,208*t+115,608*t+342) := by
      apply eq3 <;> omega
    exact he ▸ hr
  have hHub : BB6CLine.Reach (208*t+113,2,816*t+455) := by
    have hh := zero_high_hub (208*t+115) (608*t+342) (by omega) (by omega) hZ
    have he : (208*t+115-2,2,(608*t+342)+(208*t+115)-2) =
        (208*t+113,2,816*t+455) := by apply eq3 <;> omega
    exact he ▸ hh
  have hP : BB6CLine.Reach (208*t+114,1,816*t+456) := by
    have hi : BB6CLine.Reach (208*t+113,2,(816*t+451)+4) := by simpa using hHub
    have hp := reached_hub_prev (208*t+113) (816*t+451) hi (by omega)
    have he : (208*t+113+1,1,816*t+451+5)=(208*t+114,1,816*t+456) := by
      apply eq3 <;> omega
    exact he ▸ hp
  have hi2 : BB6CLine.Reach (208*t+114,1,(816*t+452)+4) := by simpa using hP
  exact even_one_exclusion (208*t+114) (816*t+452)
     (by omega) (by omega) (by omega) (by omega) hi2

/-- A second odd-section high-zero option is forced into a forbidden
zero-left-return class. -/
theorem no_second_high (t:Nat) :
    ¬ BB6CLine.Reach (720*t+401,0,304*t+170) := by
  intro h
  have hi : BB6CLine.Reach ((720*t+394)+7,0,(304*t+166)+4) := by simpa using h
  rcases reached_high_kzero_prev (720*t+394) (304*t+166) hi with ⟨k,hodd,hA,hr⟩
  have hZ : BB6CLine.Reach (0,360*t+199,304*t+170) := by
    have he : (0,k,(304*t+166)+4)=(0,360*t+199,304*t+170) := by
      apply eq3 <;> omega
    exact he ▸ hr
  have hHub : BB6CLine.Reach (360*t+197,2,664*t+367) := by
    have hh := zero_high_hub (360*t+199) (304*t+170) (by omega) (by omega) hZ
    have he : (360*t+199-2,2,(304*t+170)+(360*t+199)-2) =
        (360*t+197,2,664*t+367) := by apply eq3 <;> omega
    exact he ▸ hh
  have hP : BB6CLine.Reach (360*t+198,1,664*t+368) := by
    have hi : BB6CLine.Reach (360*t+197,2,(664*t+363)+4) := by simpa using hHub
    have hp := reached_hub_prev (360*t+197) (664*t+363) hi (by omega)
    have he : (360*t+197+1,1,664*t+363+5)=(360*t+198,1,664*t+368) := by
      apply eq3 <;> omega
    exact he ▸ hp
  have hi2 : BB6CLine.Reach (360*t+198,1,(664*t+364)+4) := by simpa using hP
  exact even_one_exclusion (360*t+198) (664*t+364)
      (by omega) (by omega) (by omega) (by omega) hi2

/-- First odd-sector origin forces a new even reset by eliminating
its only alternative high-zero ancestor. -/
theorem first_odd_to_even (t:Nat)
    (h:BB6CLine.Reach (640*t+363,192*t+109,0)) :
    BB6CLine.Reach (416*t+234,304*t+170,0) := by
  have hHub1 : BB6CLine.Reach (832*t+467,2,192*t+107) := by
    have hi : BB6CLine.Reach (640*t+363,(192*t+102)+7,0) := by simpa using h
    have hp := reached_zero_hub (640*t+363) (192*t+102) hi
    have he : (640*t+363+(192*t+102)+2,2,192*t+102+5)=(832*t+467,2,192*t+107) := by
      apply eq3 <;> omega
    exact he ▸ hp
  have hP1 : BB6CLine.Reach (832*t+468,1,192*t+108) := by
    have hi : BB6CLine.Reach (832*t+467,2,(192*t+103)+4) := by simpa using hHub1
    have hp := reached_hub_prev (832*t+467) (192*t+103) hi (by omega)
    have he : (832*t+467+1,1,192*t+103+5)=(832*t+468,1,192*t+108) := by
      apply eq3 <;> omega
    exact he ▸ hp
  have hH0 : BB6CLine.Reach (832*t+469,0,192*t+109) := by
    have hi : BB6CLine.Reach (832*t+468,1,(192*t+104)+4) := by simpa using hP1
    rcases reached_one_high_or_reset (832*t+468) (192*t+104) hi with hp | ⟨k,hk,hr⟩
    · have he : (832*t+468+1,0,192*t+104+5)=(832*t+469,0,192*t+109) := by
        apply eq3 <;> omega
      exact he ▸ hp
    · omega
  have hZ : BB6CLine.Reach (0,416*t+233,192*t+109) := by
    have hi : BB6CLine.Reach ((832*t+462)+7,0,(192*t+105)+4) := by simpa using hH0
    rcases reached_high_kzero_prev (832*t+462) (192*t+105) hi with ⟨k,hodd,hA,hr⟩
    have he : (0,k,(192*t+105)+4)=(0,416*t+233,192*t+109) := by
      apply eq3 <;> omega
    exact he ▸ hr
  have hHub2 : BB6CLine.Reach (416*t+231,2,608*t+340) := by
    have hh := zero_high_hub (416*t+233) (192*t+109) (by omega) (by omega) hZ
    have he : (416*t+233-2,2,(192*t+109)+(416*t+233)-2)=
        (416*t+231,2,608*t+340) := by apply eq3 <;> omega
    exact he ▸ hh
  have hP2 : BB6CLine.Reach (416*t+232,1,608*t+341) := by
    have hi : BB6CLine.Reach (416*t+231,2,(608*t+336)+4) := by simpa using hHub2
    have hp := reached_hub_prev (416*t+231) (608*t+336) hi (by omega)
    have he : (416*t+231+1,1,608*t+336+5)=(416*t+232,1,608*t+341) := by
      apply eq3 <;> omega
    exact he ▸ hp
  have hi : BB6CLine.Reach (416*t+232,1,(608*t+337)+4) := by simpa using hP2
  rcases reached_one_high_or_reset (416*t+232) (608*t+337) hi with hp | ⟨k,hk,hr⟩
  · have hHigh : BB6CLine.Reach (416*t+233,0,608*t+342) := by
      have he : (416*t+232+1,0,608*t+337+5)=(416*t+233,0,608*t+342) := by
        apply eq3 <;> omega
      exact he ▸ hp
    exact False.elim (no_first_high t hHigh)
  · have he : (416*t+232+2,k,0)=(416*t+234,304*t+170,0) := by
      apply eq3 <;> omega
    exact he ▸ hr

/-- Repeating an odd-sector inversion forces another even reset. -/
theorem second_even_to_even (t:Nat)
    (h:BB6CLine.Reach (416*t+234,304*t+170,0)) :
    BB6CLine.Reach (720*t+402,152*t+84,0) := by
  have hHub : BB6CLine.Reach (720*t+399,2,304*t+168) := by
    have hi : BB6CLine.Reach (416*t+234,(304*t+163)+7,0) := by simpa using h
    have hp := reached_zero_hub (416*t+234) (304*t+163) hi
    have he : (416*t+234+(304*t+163)+2,2,304*t+163+5)=(720*t+399,2,304*t+168) := by
      apply eq3 <;> omega
    exact he ▸ hp
  have hP : BB6CLine.Reach (720*t+400,1,304*t+169) := by
    have hi : BB6CLine.Reach (720*t+399,2,(304*t+164)+4) := by simpa using hHub
    have hp := reached_hub_prev (720*t+399) (304*t+164) hi (by omega)
    have he : (720*t+399+1,1,304*t+164+5)=(720*t+400,1,304*t+169) := by
      apply eq3 <;> omega
    exact he ▸ hp
  have hi : BB6CLine.Reach (720*t+400,1,(304*t+165)+4) := by simpa using hP
  rcases reached_one_high_or_reset (720*t+400) (304*t+165) hi with hp | ⟨k,hk,hr⟩
  · have hHigh : BB6CLine.Reach (720*t+401,0,304*t+170) := by
      have he : (720*t+400+1,0,304*t+165+5)=(720*t+401,0,304*t+170) := by
        apply eq3 <;> omega
      exact he ▸ hp
    exact False.elim (no_second_high t hHigh)
  · have he : (720*t+400+2,k,0)=(720*t+402,152*t+84,0) := by
      apply eq3 <;> omega
    exact he ▸ hr

/-- The final forced reset has a globally prohibited odd-zero sum residue. -/
theorem no_final_even (t:Nat) :
    ¬BB6CLine.Reach (720*t+402,152*t+84,0) := by
  intro h
  have hHub : BB6CLine.Reach (872*t+481,2,152*t+82) := by
    have hi : BB6CLine.Reach (720*t+402,(152*t+77)+7,0) := by simpa using h
    have hp := reached_zero_hub (720*t+402) (152*t+77) hi
    have he : (720*t+402+(152*t+77)+2,2,152*t+77+5)=(872*t+481,2,152*t+82) := by
      apply eq3 <;> omega
    exact he ▸ hp
  have hP : BB6CLine.Reach (872*t+482,1,152*t+83) := by
    have hi : BB6CLine.Reach (872*t+481,2,(152*t+78)+4) := by simpa using hHub
    have hp := reached_hub_prev (872*t+481) (152*t+78) hi (by omega)
    have he : (872*t+481+1,1,152*t+78+5)=(872*t+482,1,152*t+83) := by
      apply eq3 <;> omega
    exact he ▸ hp
  have hi : BB6CLine.Reach (872*t+482,1,(152*t+79)+4) := by simpa using hP
  rcases reached_one_high_or_reset (872*t+482) (152*t+79) hi with hp | ⟨k,hk,hr⟩
  · have hHigh : BB6CLine.Reach (872*t+483,0,152*t+84) := by
      have he : (872*t+482+1,0,152*t+79+5)=(872*t+483,0,152*t+84) := by
        apply eq3 <;> omega
      exact he ▸ hp
    have hmod := high_zero_mod4 (872*t+483) (152*t+84) (by omega) (by omega) hHigh
    omega
  · have hReset : BB6CLine.Reach (872*t+484,76*t+41,0) := by
      have he : (872*t+482+2,k,0)=(872*t+484,76*t+41,0) := by
        apply eq3 <;> omega
      exact he ▸ hr
    have hbad := reached_odd_zero_mod4_hole (872*t+484) (76*t+41) hReset
      (by omega) (by omega)
    omega

/-- New all-time reset exclusion at index j congruent to 72 modulo 128. -/
theorem reset_mod128_seventytwo_unreachable (t:Nat) :
    ¬BB6CLine.Reach (256*t+145,384*t+220,0) := by
  intro h
  have h1 : BB6CLine.Reach (640*t+363,192*t+109,0) := by
    have hub : BB6CLine.Reach (256*t+145+(384*t+220)-5,2,(384*t+220)-2) →
        BB6CLine.Reach (256*t+145+(384*t+220)-4,1,(384*t+220)-1) := by
      intro hp
      have he : (256*t+145+(384*t+220)-5,2,(384*t+220)-2) =
           (640*t+360,2,(384*t+214)+4) := by apply eq3 <;> omega
      have hh := reached_hub_prev (640*t+360) (384*t+214) (he ▸ hp) (by omega)
      have he2 : (640*t+360+1,1,384*t+214+5) =
            (256*t+145+(384*t+220)-4,1,(384*t+220)-1) := by apply eq3 <;> omega
      exact he2 ▸ hh
    have hp := BB6.CMod128Six.even_backward (256*t+145) (384*t+220)
      (by omega) (by omega) h hub
    have he : (256*t+145+(384*t+220)-2,(384*t+220)/2-1,0) =
         (640*t+363,192*t+109,0) := by apply eq3 <;> omega
    exact he ▸ hp
  have h2 := first_odd_to_even t h1
  have h3 := second_even_to_even t h2
  exact no_final_even t h3

#print axioms reset_mod128_seventytwo_unreachable
end BB6.CMod128SeventyTwo
