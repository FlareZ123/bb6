import CHubSplit
import CMod128Six
import Lean.Elab.Tactic.Omega

namespace BB6.CMod128Eighteen
open BB6.CBack BB6.CRange BB6.CHubSplit

private theorem eq3 {a b c d e f : Nat}
    (h1:a=d) (h2:b=e) (h3:c=f) :
    ((a,b,c):Nat×Nat×Nat)=(d,e,f) := by
  cases h1; cases h2; cases h3; rfl

/-- A generic contradiction: with even right counter, a high k=1 state
must descend to a high k=0 predecessor, which has left counter 1 mod4. -/
theorem even_one_exclusion (A C:Nat) (hA:7≤A+1) (hC:4≤C+5)
    (hmod:(A+1)%4 ≠ 1) (hc:(C+4)%2=0)
    (h:BB6CLine.Reach (A,1,C+4)) : False := by
  rcases reached_one_high_or_reset A C h with hp | ⟨k,hk,hr⟩
  · have hs := high_zero_mod4 (A+1) (C+5) hA hC hp
    omega
  · omega

/-- The second portal in the j=18 class has no positive-high precursor. -/
theorem no_middle_positive (t:Nat) :
    ¬BB6CLine.Reach (160*t+19,1,864*t+123) := by
  intro h
  have hi : BB6CLine.Reach (160*t+19,1,(864*t+119)+4) := by simpa using h
  rcases reached_one_high_or_reset (160*t+19) (864*t+119) hi with hp | ⟨k,hk,hr⟩
  · have hodd := reached_kzero_odd (160*t+20) (864*t+124) (by
      have he : (160*t+19+1,0,864*t+119+5)=(160*t+20,0,864*t+124) := by
        apply eq3 <;> omega
      exact he ▸ hp)
    omega
  · have hK : k=432*t+61 := by omega
    have hs : BB6CLine.Reach (160*t+21,432*t+61,0) := by
      have he : (160*t+19+2,k,0)=(160*t+21,432*t+61,0) := by
        apply eq3 <;> omega
      exact he ▸ hr
    have hbad := reached_odd_zero_mod4_hole (160*t+21) (432*t+61) hs (by omega) (by omega)
    omega

/-- The third portal has no positive-high precursor. -/
theorem no_third_positive (t:Nat) :
    ¬BB6CLine.Reach (80*t+7,1,944*t+132) := by
  intro h
  have he : (80*t+7,1,944*t+132)=(80*t+7,1,(944*t+128)+4) := by
    apply eq3 <;> omega
  exact even_one_exclusion (80*t+7) (944*t+128) (by omega) (by omega)
    (by omega) (by omega) (he ▸ h)

/-- No reached configuration can be the fourth possible portal predecessor. -/
theorem no_last_portal (t:Nat) :
    ¬BB6CLine.Reach (0,40*t+2,944*t+134) := by
  intro h
  have hhub : BB6CLine.Reach (40*t,2,984*t+134) := by
    cases t with
    | zero => simpa using h
    | succ s =>
      have h1 := zero_high_hub (40*(s+1)+2) (944*(s+1)+134)
        (by omega) (by omega) h
      have he : (40*(s+1)+2-2,2,(944*(s+1)+134)+(40*(s+1)+2)-2) =
            (40*(s+1),2,984*(s+1)+134) := by apply eq3 <;> omega
      exact he ▸ h1
  have h1 : BB6CLine.Reach (40*t+1,1,984*t+135) := by
    have hi : BB6CLine.Reach (40*t,2,(984*t+130)+4) := by simpa using hhub
    have hp := reached_hub_prev (40*t) (984*t+130) hi (by omega)
    have he : (40*t+1,1,984*t+130+5)=(40*t+1,1,984*t+135) := by
      apply eq3 <;> omega
    exact he ▸ hp
  have hi : BB6CLine.Reach (40*t+1,1,(984*t+131)+4) := by simpa using h1
  rcases reached_one_high_or_reset (40*t+1) (984*t+131) hi with hp | ⟨k,hk,hr⟩
  · have hh : BB6CLine.Reach (40*t+2,0,984*t+136) := by
      have he : (40*t+1+1,0,984*t+131+5)=(40*t+2,0,984*t+136) := by
        apply eq3 <;> omega
      exact he ▸ hp
    have hbad := reached_kzero_odd (40*t+2) (984*t+136) hh
    omega
  · have hs : BB6CLine.Reach (40*t+3,492*t+67,0) := by
      have he : (40*t+1+2,k,0)=(40*t+3,492*t+67,0) := by
        apply eq3 <;> omega
      exact he ▸ hr
    have hbad := reached_odd_zero_mod4_hole (40*t+3) (492*t+67) hs (by omega) (by omega)
    omega

/-- The entire cascade from the first zero-left portal is excluded. -/
theorem no_first_portal (t:Nat) :
    ¬BB6CLine.Reach (0,320*t+44,384*t+59) := by
  intro h
  have hhub1 : BB6CLine.Reach (320*t+42,2,704*t+101) := by
    have hh := zero_high_hub (320*t+44) (384*t+59) (by omega) (by omega) h
    have he : (320*t+44-2,2,(384*t+59)+(320*t+44)-2)=
        (320*t+42,2,704*t+101) := by apply eq3 <;> omega
    exact he ▸ hh
  have hZ1 : BB6CLine.Reach (0,160*t+20,704*t+104) := by
    have hi : BB6CLine.Reach (320*t+42,2,(704*t+97)+4) := by simpa using hhub1
    rcases reached_two_split (320*t+42) (704*t+97) (by omega) hi with hp | ⟨k,hk,ha,hr⟩
    · have hi1 : BB6CLine.Reach (320*t+43,1,(704*t+98)+4) := by
        have he : (320*t+42+1,1,704*t+97+5) =
              (320*t+43,1,(704*t+98)+4) := by apply eq3 <;> omega
        exact he ▸ hp
      exact False.elim (even_one_exclusion (320*t+43) (704*t+98)
        (by omega) (by omega) (by omega) (by omega) hi1)
    · have he : (0,k,(704*t+97)+7)=(0,160*t+20,704*t+104) := by
        apply eq3 <;> omega
      exact he ▸ hr
  have hhub2 : BB6CLine.Reach (160*t+18,2,864*t+122) := by
    have hh := zero_high_hub (160*t+20) (704*t+104) (by omega) (by omega) hZ1
    have he : (160*t+20-2,2,(704*t+104)+(160*t+20)-2)=
        (160*t+18,2,864*t+122) := by apply eq3 <;> omega
    exact he ▸ hh
  have hZ2 : BB6CLine.Reach (0,80*t+8,864*t+125) := by
    have hi : BB6CLine.Reach (160*t+18,2,(864*t+118)+4) := by simpa using hhub2
    rcases reached_two_split (160*t+18) (864*t+118) (by omega) hi with hp | ⟨k,hk,ha,hr⟩
    · have hh : BB6CLine.Reach (160*t+19,1,864*t+123) := by
        have he : (160*t+18+1,1,864*t+118+5)=(160*t+19,1,864*t+123) := by
          apply eq3 <;> omega
        exact he ▸ hp
      exact False.elim (no_middle_positive t hh)
    · have he : (0,k,(864*t+118)+7)=(0,80*t+8,864*t+125) := by
        apply eq3 <;> omega
      exact he ▸ hr
  have hhub3 : BB6CLine.Reach (80*t+6,2,944*t+131) := by
    have hh := zero_high_hub (80*t+8) (864*t+125) (by omega) (by omega) hZ2
    have he : (80*t+8-2,2,(864*t+125)+(80*t+8)-2)=
        (80*t+6,2,944*t+131) := by apply eq3 <;> omega
    exact he ▸ hh
  have hZ3 : BB6CLine.Reach (0,40*t+2,944*t+134) := by
    have hi : BB6CLine.Reach (80*t+6,2,(944*t+127)+4) := by simpa using hhub3
    rcases reached_two_split (80*t+6) (944*t+127) (by omega) hi with hp | ⟨k,hk,ha,hr⟩
    · have hh : BB6CLine.Reach (80*t+7,1,944*t+132) := by
        have he : (80*t+6+1,1,944*t+127+5)=(80*t+7,1,944*t+132) := by
          apply eq3 <;> omega
        exact he ▸ hp
      exact False.elim (no_third_positive t hh)
    · have he : (0,k,(944*t+127)+7)=(0,40*t+2,944*t+134) := by
        apply eq3 <;> omega
      exact he ▸ hr
  exact no_last_portal t hZ3

/-- The only candidate final high-k=1 state of the positive branch has
no predecessor compatible with the universal high-zero and odd-zero invariants. -/
theorem no_positive_final (t:Nat) :
    ¬BB6CLine.Reach (464*t+62,1,560*t+75) := by
  intro h
  have hi : BB6CLine.Reach (464*t+62,1,(560*t+71)+4) := by simpa using h
  rcases reached_one_high_or_reset (464*t+62) (560*t+71) hi with hp | ⟨k,hk,hr⟩
  · have h0 : BB6CLine.Reach (464*t+63,0,560*t+76) := by
      have he : (464*t+62+1,0,560*t+71+5)=(464*t+63,0,560*t+76) := by
        apply eq3 <;> omega
      exact he ▸ hp
    have hz := high_zero_mod4 (464*t+63) (560*t+76) (by omega) (by omega) h0
    omega
  · have h0 : BB6CLine.Reach (464*t+64,280*t+37,0) := by
      have he : (464*t+62+2,k,0)=(464*t+64,280*t+37,0) := by
        apply eq3 <;> omega
      exact he ▸ hr
    have hbad := reached_odd_zero_mod4_hole (464*t+64) (280*t+37) h0
      (by omega) (by omega)
    omega

/-- Following the positive branch from the first high hub eventually
contradicts a nonreset modular restriction. -/
theorem no_first_positive (t:Nat) :
    ¬BB6CLine.Reach (640*t+91,1,384*t+57) := by
  intro h
  have hReset : BB6CLine.Reach (640*t+93,192*t+28,0) := by
    have hi : BB6CLine.Reach (640*t+91,1,(384*t+53)+4) := by simpa using h
    rcases reached_one_high_or_reset (640*t+91) (384*t+53) hi with hp | ⟨k,hk,hr⟩
    · have hs : BB6CLine.Reach (640*t+92,0,384*t+58) := by
        have he : (640*t+91+1,0,384*t+53+5)=(640*t+92,0,384*t+58) := by
          apply eq3 <;> omega
        exact he ▸ hp
      have hb := reached_kzero_odd (640*t+92) (384*t+58) hs
      omega
    · have he : (640*t+91+2,k,0)=(640*t+93,192*t+28,0) := by
        apply eq3 <;> omega
      exact he ▸ hr
  have hReset2 : BB6CLine.Reach (832*t+119,96*t+13,0) := by
    have hub : BB6CLine.Reach (640*t+93+(192*t+28)-5,2,(192*t+28)-2) →
        BB6CLine.Reach (640*t+93+(192*t+28)-4,1,(192*t+28)-1) := by
      intro hp
      have he : (640*t+93+(192*t+28)-5,2,(192*t+28)-2) =
            (832*t+116,2,(192*t+22)+4) := by apply eq3 <;> omega
      have hh := reached_hub_prev (832*t+116) (192*t+22) (he ▸ hp) (by omega)
      have he2 : (832*t+116+1,1,192*t+22+5) =
           (640*t+93+(192*t+28)-4,1,(192*t+28)-1) := by apply eq3 <;> omega
      exact he2 ▸ hh
    have hh := BB6.CMod128Six.even_backward (640*t+93) (192*t+28)
      (by omega) (by omega) hReset hub
    have he : (640*t+93+(192*t+28)-2,(192*t+28)/2-1,0) =
          (832*t+119,96*t+13,0) := by apply eq3 <;> omega
    exact he ▸ hh
  have hHub : BB6CLine.Reach (928*t+127,2,96*t+11) := by
    have hi : BB6CLine.Reach (832*t+119,(96*t+6)+7,0) := by simpa using hReset2
    have hp := reached_zero_hub (832*t+119) (96*t+6) hi
    have he : (832*t+119+(96*t+6)+2,2,(96*t+6)+5) =
         (928*t+127,2,96*t+11) := by apply eq3 <;> omega
    exact he ▸ hp
  have h1 : BB6CLine.Reach (928*t+128,1,96*t+12) := by
    have hi : BB6CLine.Reach (928*t+127,2,(96*t+7)+4) := by simpa using hHub
    have hp := reached_hub_prev (928*t+127) (96*t+7) hi (by omega)
    have he : (928*t+127+1,1,96*t+7+5)=(928*t+128,1,96*t+12) := by
      apply eq3 <;> omega
    exact he ▸ hp
  have h2 : BB6CLine.Reach (928*t+129,0,96*t+13) := by
    have hi : BB6CLine.Reach (928*t+128,1,(96*t+8)+4) := by simpa using h1
    rcases reached_one_high_or_reset (928*t+128) (96*t+8) hi with hp | ⟨k,hk,hr⟩
    · have he : (928*t+128+1,0,96*t+8+5)=(928*t+129,0,96*t+13) := by
        apply eq3 <;> omega
      exact he ▸ hp
    · omega
  have hZ : BB6CLine.Reach (0,464*t+63,96*t+13) := by
    have hi : BB6CLine.Reach ((928*t+122)+7,0,(96*t+9)+4) := by simpa using h2
    rcases reached_high_kzero_prev (928*t+122) (96*t+9) hi with ⟨k,hodd,hA,hr⟩
    have he : (0,k,(96*t+9)+4)=(0,464*t+63,96*t+13) := by
      apply eq3 <;> omega
    exact he ▸ hr
  have hHub2 : BB6CLine.Reach (464*t+61,2,560*t+74) := by
    have hh := zero_high_hub (464*t+63) (96*t+13) (by omega) (by omega) hZ
    have he : (464*t+63-2,2,(96*t+13)+(464*t+63)-2)=
        (464*t+61,2,560*t+74) := by apply eq3 <;> omega
    exact he ▸ hh
  have hP : BB6CLine.Reach (464*t+62,1,560*t+75) := by
    have hi : BB6CLine.Reach (464*t+61,2,(560*t+70)+4) := by simpa using hHub2
    have hp := reached_hub_prev (464*t+61) (560*t+70) hi (by omega)
    have he : (464*t+61+1,1,560*t+70+5) = (464*t+62,1,560*t+75) := by
      apply eq3 <;> omega
    exact he ▸ hp
  exact no_positive_final t hP

/-- A complete symbolic nonreachability result for the remaining first hub,
where both the positive and zero-left predecessors lead to contradictions. -/
theorem reset_mod128_eighteen_unreachable (t:Nat) :
    ¬BB6CLine.Reach (256*t+37,384*t+58,0) := by
  intro h
  have hHub : BB6CLine.Reach (640*t+90,2,384*t+56) := by
    have hi : BB6CLine.Reach (256*t+37,(384*t+51)+7,0) := by simpa using h
    have hh := reached_zero_hub (256*t+37) (384*t+51) hi
    have he : (256*t+37+(384*t+51)+2,2,(384*t+51)+5) =
        (640*t+90,2,384*t+56) := by apply eq3 <;> omega
    exact he ▸ hh
  have hi : BB6CLine.Reach (640*t+90,2,(384*t+52)+4) := by simpa using hHub
  rcases reached_two_split (640*t+90) (384*t+52) (by omega) hi with hp | ⟨k,hk,ha,hr⟩
  · have hh : BB6CLine.Reach (640*t+91,1,384*t+57) := by
      have he : (640*t+90+1,1,384*t+52+5)=(640*t+91,1,384*t+57) := by
        apply eq3 <;> omega
      exact he ▸ hp
    exact no_first_positive t hh
  · have hh : BB6CLine.Reach (0,320*t+44,384*t+59) := by
      have he : (0,k,(384*t+52)+7)=(0,320*t+44,384*t+59) := by
        apply eq3 <;> omega
      exact he ▸ hr
    exact no_first_portal t hh

#print axioms reset_mod128_eighteen_unreachable

#print axioms no_first_portal
end BB6.CMod128Eighteen
