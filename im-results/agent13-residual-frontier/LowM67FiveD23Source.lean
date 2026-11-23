import LowM67D4ThirdSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13FiveD23
open BB6.Agent46 BB6.Agent3

/-- Source-level complete depth-0/depth-2 parent contradiction for
    (180*u+28,166*u+25), uniform for u=33 (mod 512).
    The depth-two branch follows the exact OE source-normalizer path. -/
theorem rectangle_u33_mod512_unreachable
    (u : Nat) (hu : u%512=33) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/512
  have hU : u=512*t+33 := by
    have hh := Nat.mod_add_div u 512
    dsimp [t]
    omega
  have hx : 5<180*u+28 := by omega
  have hxe : (180*u+28)%2=0 := by omega
  have hyo : (166*u+25)%2=1 := by omega
  have hy5 : 5≤166*u+25 := by omega
  have hbig : 64≤(180*u+28)+(166*u+25)+1 := by omega
  have hmod : ((180*u+28)+(166*u+25)+1)%64≠0 := by
    rw [hU]
    omega
  intro hr
  obtain ⟨a,k,hpre,hedge⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (180*u+28) (166*u+25) hx hr
  obtain ⟨n,hn,hlow,hpow,hcost⟩ :=
    BB6.Agent13SmallFan.even_odd_small_valuation_parent
      a k (180*u+28) (166*u+25)
      hxe hyo hy5 hbig hmod hedge
  rw [hU] at hpow hcost
  rcases hn with hn0|hn2
  · subst n
    have ha : a=(88576*t+5733) := by
      simp at hpow
      omega
    have hk : k=(86784*t+5617) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) hpre
  · subst n
    have ha : a=(22144*t+1431) := by
      simp at hpow
      omega
    have hk : k=(120000*t+7765) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    have hg1 := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (22144*t+1431) (120000*t+7765)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp hpre
    have h1 : BB6.Agent3.CReach (71072*t+4596) (95536*t+6179) := by
      simpa only [BB6.Agent3.CReach,
        show ((22144*t+1431)+(120000*t+7765)-4)/2=(71072*t+4596) by omega,
        show ((22144*t+1431)+3*(120000*t+7765)-10)/4=(95536*t+6179) by omega] using hg1
    have hg2 := (BB6.Agent3.odd_seven_blank_reach_iff
      (71072*t+4596) (95536*t+6179)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp h1
    have h2 : BB6.Agent3.CReach (83304*t+5385) (89420*t+5781) := by
      simpa only [BB6.Agent3.CReach,
        show ((71072*t+4596)+(95536*t+6179)-5)/2=(83304*t+5385) by omega,
        show ((71072*t+4596)+3*(95536*t+6179)-9)/4=(89420*t+5781) by omega] using hg2
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) h2

/-- All-time source-authentic low stopping target nonreachability for
    m=512*z+67, z=165 modulo 256. -/
theorem low_stop_m67_z165_mod256_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%256=165)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 131072 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^17 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^17=131072 by decide] using h
  have hpmod : (2^(2*m+3))%131072=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hkmod : k%131072=8499 := by
    have hs : (k+3*m+4)%131072=0 := by
      rw [hstop]
      exact hpmod
    rw [hm] at hs
    omega
  let u := 512*(k/131072)+33
  have hu : u%512=33 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 131072
    rw [hkmod] at hh
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (rectangle_u33_mod512_unreachable u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)


/-- Source-level complete depth-0/depth-2 parent contradiction for
    (180*u+28,166*u+25), uniform for u=393 (mod 1024).
    The depth-two branch follows the exact AOBB source-normalizer path. -/
theorem rectangle_u393_mod1024_unreachable
    (u : Nat) (hu : u%1024=393) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/1024
  have hU : u=1024*t+393 := by
    have hh := Nat.mod_add_div u 1024
    dsimp [t]
    omega
  have hx : 5<180*u+28 := by omega
  have hxe : (180*u+28)%2=0 := by omega
  have hyo : (166*u+25)%2=1 := by omega
  have hy5 : 5≤166*u+25 := by omega
  have hbig : 64≤(180*u+28)+(166*u+25)+1 := by omega
  have hmod : ((180*u+28)+(166*u+25)+1)%64≠0 := by
    rw [hU]
    omega
  intro hr
  obtain ⟨a,k,hpre,hedge⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (180*u+28) (166*u+25) hx hr
  obtain ⟨n,hn,hlow,hpow,hcost⟩ :=
    BB6.Agent13SmallFan.even_odd_small_valuation_parent
      a k (180*u+28) (166*u+25)
      hxe hyo hy5 hbig hmod hedge
  rw [hU] at hpow hcost
  rcases hn with hn0|hn2
  · subst n
    have ha : a=(177152*t+68013) := by
      simp at hpow
      omega
    have hk : k=(173568*t+66637) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) hpre
  · subst n
    have ha : a=(44288*t+17001) := by
      simp at hpow
      omega
    have hk : k=(240000*t+92140) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    have hg1 := (BB6.Agent15.blank_reach_iff_affine
      (44288*t+17001) (240000*t+92140)
      (by omega) (by omega) (by omega)).mp hpre
    have h1 : BB6.Agent3.CReach (284288*t+109139) (120000*t+46069) := by
      simpa only [BB6.Agent3.CReach,
        show (44288*t+17001)+(240000*t+92140)-2=(284288*t+109139) by omega,
        show ((240000*t+92140)-2)/2=(120000*t+46069) by omega] using hg1
    have hg2 := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (284288*t+109139) (120000*t+46069)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp h1
    have h2 : BB6.Agent3.CReach (202144*t+77602) (161072*t+61834) := by
      simpa only [BB6.Agent3.CReach,
        show ((284288*t+109139)+(120000*t+46069)-4)/2=(202144*t+77602) by omega,
        show ((284288*t+109139)+3*(120000*t+46069)-10)/4=(161072*t+61834) by omega] using hg2
    have hg3 := (BB6.Agent46.six_even_right_blank_reach_iff
      (202144*t+77602) (161072*t+61834)
      (by omega) (by omega) (by omega) (by omega)).mp h2
    have h3 : BB6.Agent3.CReach (363216*t+139434) (80536*t+30916) := by
      simpa only [BB6.Agent3.CReach,
        show (202144*t+77602)+(161072*t+61834)-2=(363216*t+139434) by omega,
        show ((161072*t+61834)-2)/2=(80536*t+30916) by omega] using hg3
    have hg4 := (BB6.Agent46.six_even_right_blank_reach_iff
      (363216*t+139434) (80536*t+30916)
      (by omega) (by omega) (by omega) (by omega)).mp h3
    have h4 : BB6.Agent3.CReach (443752*t+170348) (40268*t+15457) := by
      simpa only [BB6.Agent3.CReach,
        show (363216*t+139434)+(80536*t+30916)-2=(443752*t+170348) by omega,
        show ((80536*t+30916)-2)/2=(40268*t+15457) by omega] using hg4
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inl (by omega))) h4

/-- All-time source-authentic low stopping target nonreachability for
    m=512*z+67, z=105 modulo 512. -/
theorem low_stop_m67_z105_mod512_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%512=105)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 262144 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^18 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^18=262144 by decide] using h
  have hpmod : (2^(2*m+3))%262144=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hkmod : k%262144=100659 := by
    have hs : (k+3*m+4)%262144=0 := by
      rw [hstop]
      exact hpmod
    rw [hm] at hs
    omega
  let u := 1024*(k/262144)+393
  have hu : u%1024=393 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 262144
    rw [hkmod] at hh
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (rectangle_u393_mod1024_unreachable u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)


/-- Source-level complete depth-0/depth-2 parent contradiction for
    (180*u+28,166*u+25), uniform for u=1281 (mod 2048).
    The depth-two branch follows the exact OBFB source-normalizer path. -/
theorem rectangle_u1281_mod2048_unreachable
    (u : Nat) (hu : u%2048=1281) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/2048
  have hU : u=2048*t+1281 := by
    have hh := Nat.mod_add_div u 2048
    dsimp [t]
    omega
  have hx : 5<180*u+28 := by omega
  have hxe : (180*u+28)%2=0 := by omega
  have hyo : (166*u+25)%2=1 := by omega
  have hy5 : 5≤166*u+25 := by omega
  have hbig : 64≤(180*u+28)+(166*u+25)+1 := by omega
  have hmod : ((180*u+28)+(166*u+25)+1)%64≠0 := by
    rw [hU]
    omega
  intro hr
  obtain ⟨a,k,hpre,hedge⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (180*u+28) (166*u+25) hx hr
  obtain ⟨n,hn,hlow,hpow,hcost⟩ :=
    BB6.Agent13SmallFan.even_odd_small_valuation_parent
      a k (180*u+28) (166*u+25)
      hxe hyo hy5 hbig hmod hedge
  rw [hU] at hpow hcost
  rcases hn with hn0|hn2
  · subst n
    have ha : a=(354304*t+221637) := by
      simp at hpow
      omega
    have hk : k=(347136*t+217153) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) hpre
  · subst n
    have ha : a=(88576*t+55407) := by
      simp at hpow
      omega
    have hk : k=(480000*t+300265) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    have hg1 := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (88576*t+55407) (480000*t+300265)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp hpre
    have h1 : BB6.Agent3.CReach (284288*t+177834) (382144*t+239048) := by
      simpa only [BB6.Agent3.CReach,
        show ((88576*t+55407)+(480000*t+300265)-4)/2=(284288*t+177834) by omega,
        show ((88576*t+55407)+3*(480000*t+300265)-10)/4=(382144*t+239048) by omega] using hg1
    have hg2 := (BB6.Agent46.six_even_right_blank_reach_iff
      (284288*t+177834) (382144*t+239048)
      (by omega) (by omega) (by omega) (by omega)).mp h1
    have h2 : BB6.Agent3.CReach (666432*t+416880) (191072*t+119523) := by
      simpa only [BB6.Agent3.CReach,
        show (284288*t+177834)+(382144*t+239048)-2=(666432*t+416880) by omega,
        show ((382144*t+239048)-2)/2=(191072*t+119523) by omega] using hg2
    have hg3 := (BB6.Agent3.evenodd_four_blank_reach_iff
      (666432*t+416880) (191072*t+119523)
      (by omega) (by omega) (by omega) (by omega)).mp h2
    have h3 : BB6.Agent3.CReach (428752*t+268199) (309912*t+193860) := by
      simpa only [BB6.Agent3.CReach,
        show ((666432*t+416880)+(191072*t+119523)-5)/2=(428752*t+268199) by omega,
        show ((666432*t+416880)+3*(191072*t+119523)-9)/4=(309912*t+193860) by omega] using hg3
    have hg4 := (BB6.Agent46.six_even_right_blank_reach_iff
      (428752*t+268199) (309912*t+193860)
      (by omega) (by omega) (by omega) (by omega)).mp h3
    have h4 : BB6.Agent3.CReach (738664*t+462057) (154956*t+96929) := by
      simpa only [BB6.Agent3.CReach,
        show (428752*t+268199)+(309912*t+193860)-2=(738664*t+462057) by omega,
        show ((309912*t+193860)-2)/2=(154956*t+96929) by omega] using hg4
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) h4

/-- All-time source-authentic low stopping target nonreachability for
    m=512*z+67, z=469 modulo 1024. -/
theorem low_stop_m67_z469_mod1024_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%1024=469)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 524288 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^19 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^19=524288 by decide] using h
  have hpmod : (2^(2*m+3))%524288=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hkmod : k%524288=327987 := by
    have hs : (k+3*m+4)%524288=0 := by
      rw [hstop]
      exact hpmod
    rw [hm] at hs
    omega
  let u := 2048*(k/524288)+1281
  have hu : u%2048=1281 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 524288
    rw [hkmod] at hh
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (rectangle_u1281_mod2048_unreachable u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)


/-- Source-level complete depth-0/depth-2 parent contradiction for
    (180*u+28,166*u+25), uniform for u=929 (mod 2048).
    The depth-two branch follows the exact OFAB source-normalizer path. -/
theorem rectangle_u929_mod2048_unreachable
    (u : Nat) (hu : u%2048=929) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/2048
  have hU : u=2048*t+929 := by
    have hh := Nat.mod_add_div u 2048
    dsimp [t]
    omega
  have hx : 5<180*u+28 := by omega
  have hxe : (180*u+28)%2=0 := by omega
  have hyo : (166*u+25)%2=1 := by omega
  have hy5 : 5≤166*u+25 := by omega
  have hbig : 64≤(180*u+28)+(166*u+25)+1 := by omega
  have hmod : ((180*u+28)+(166*u+25)+1)%64≠0 := by
    rw [hU]
    omega
  intro hr
  obtain ⟨a,k,hpre,hedge⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (180*u+28) (166*u+25) hx hr
  obtain ⟨n,hn,hlow,hpow,hcost⟩ :=
    BB6.Agent13SmallFan.even_odd_small_valuation_parent
      a k (180*u+28) (166*u+25)
      hxe hyo hy5 hbig hmod hedge
  rw [hU] at hpow hcost
  rcases hn with hn0|hn2
  · subst n
    have ha : a=(354304*t+160741) := by
      simp at hpow
      omega
    have hk : k=(347136*t+157489) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) hpre
  · subst n
    have ha : a=(88576*t+40183) := by
      simp at hpow
      omega
    have hk : k=(480000*t+217765) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    have hg1 := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (88576*t+40183) (480000*t+217765)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp hpre
    have h1 : BB6.Agent3.CReach (284288*t+128972) (382144*t+173367) := by
      simpa only [BB6.Agent3.CReach,
        show ((88576*t+40183)+(480000*t+217765)-4)/2=(284288*t+128972) by omega,
        show ((88576*t+40183)+3*(480000*t+217765)-10)/4=(382144*t+173367) by omega] using hg1
    have hg2 := (BB6.Agent3.evenodd_four_blank_reach_iff
      (284288*t+128972) (382144*t+173367)
      (by omega) (by omega) (by omega) (by omega)).mp h1
    have h2 : BB6.Agent3.CReach (333216*t+151167) (357680*t+162266) := by
      simpa only [BB6.Agent3.CReach,
        show ((284288*t+128972)+(382144*t+173367)-5)/2=(333216*t+151167) by omega,
        show ((284288*t+128972)+3*(382144*t+173367)-9)/4=(357680*t+162266) by omega] using hg2
    have hg3 := (BB6.Agent15.blank_reach_iff_affine
      (333216*t+151167) (357680*t+162266)
      (by omega) (by omega) (by omega)).mp h2
    have h3 : BB6.Agent3.CReach (690896*t+313431) (178840*t+81132) := by
      simpa only [BB6.Agent3.CReach,
        show (333216*t+151167)+(357680*t+162266)-2=(690896*t+313431) by omega,
        show ((357680*t+162266)-2)/2=(178840*t+81132) by omega] using hg3
    have hg4 := (BB6.Agent46.six_even_right_blank_reach_iff
      (690896*t+313431) (178840*t+81132)
      (by omega) (by omega) (by omega) (by omega)).mp h3
    have h4 : BB6.Agent3.CReach (869736*t+394561) (89420*t+40565) := by
      simpa only [BB6.Agent3.CReach,
        show (690896*t+313431)+(178840*t+81132)-2=(869736*t+394561) by omega,
        show ((178840*t+81132)-2)/2=(89420*t+40565) by omega] using hg4
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) h4

/-- All-time source-authentic low stopping target nonreachability for
    m=512*z+67, z=869 modulo 1024. -/
theorem low_stop_m67_z869_mod1024_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%1024=869)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 524288 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^19 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^19=524288 by decide] using h
  have hpmod : (2^(2*m+3))%524288=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hkmod : k%524288=237875 := by
    have hs : (k+3*m+4)%524288=0 := by
      rw [hstop]
      exact hpmod
    rw [hm] at hs
    omega
  let u := 2048*(k/524288)+929
  have hu : u%2048=929 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 524288
    rw [hkmod] at hh
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (rectangle_u929_mod2048_unreachable u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)


/-- Source-level complete depth-0/depth-2 parent contradiction for
    (180*u+28,166*u+25), uniform for u=585 (mod 2048).
    The depth-two branch follows the exact AOFB source-normalizer path. -/
theorem rectangle_u585_mod2048_unreachable
    (u : Nat) (hu : u%2048=585) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/2048
  have hU : u=2048*t+585 := by
    have hh := Nat.mod_add_div u 2048
    dsimp [t]
    omega
  have hx : 5<180*u+28 := by omega
  have hxe : (180*u+28)%2=0 := by omega
  have hyo : (166*u+25)%2=1 := by omega
  have hy5 : 5≤166*u+25 := by omega
  have hbig : 64≤(180*u+28)+(166*u+25)+1 := by omega
  have hmod : ((180*u+28)+(166*u+25)+1)%64≠0 := by
    rw [hU]
    omega
  intro hr
  obtain ⟨a,k,hpre,hedge⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (180*u+28) (166*u+25) hx hr
  obtain ⟨n,hn,hlow,hpow,hcost⟩ :=
    BB6.Agent13SmallFan.even_odd_small_valuation_parent
      a k (180*u+28) (166*u+25)
      hxe hyo hy5 hbig hmod hedge
  rw [hU] at hpow hcost
  rcases hn with hn0|hn2
  · subst n
    have ha : a=(354304*t+101229) := by
      simp at hpow
      omega
    have hk : k=(347136*t+99181) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) hpre
  · subst n
    have ha : a=(88576*t+25305) := by
      simp at hpow
      omega
    have hk : k=(480000*t+137140) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    have hg1 := (BB6.Agent15.blank_reach_iff_affine
      (88576*t+25305) (480000*t+137140)
      (by omega) (by omega) (by omega)).mp hpre
    have h1 : BB6.Agent3.CReach (568576*t+162443) (240000*t+68569) := by
      simpa only [BB6.Agent3.CReach,
        show (88576*t+25305)+(480000*t+137140)-2=(568576*t+162443) by omega,
        show ((480000*t+137140)-2)/2=(240000*t+68569) by omega] using hg1
    have hg2 := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (568576*t+162443) (240000*t+68569)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp h1
    have h2 : BB6.Agent3.CReach (404288*t+115504) (322144*t+92035) := by
      simpa only [BB6.Agent3.CReach,
        show ((568576*t+162443)+(240000*t+68569)-4)/2=(404288*t+115504) by omega,
        show ((568576*t+162443)+3*(240000*t+68569)-10)/4=(322144*t+92035) by omega] using hg2
    have hg3 := (BB6.Agent3.evenodd_four_blank_reach_iff
      (404288*t+115504) (322144*t+92035)
      (by omega) (by omega) (by omega) (by omega)).mp h2
    have h3 : BB6.Agent3.CReach (363216*t+103767) (342680*t+97900) := by
      simpa only [BB6.Agent3.CReach,
        show ((404288*t+115504)+(322144*t+92035)-5)/2=(363216*t+103767) by omega,
        show ((404288*t+115504)+3*(322144*t+92035)-9)/4=(342680*t+97900) by omega] using hg3
    have hg4 := (BB6.Agent46.six_even_right_blank_reach_iff
      (363216*t+103767) (342680*t+97900)
      (by omega) (by omega) (by omega) (by omega)).mp h3
    have h4 : BB6.Agent3.CReach (705896*t+201665) (171340*t+48949) := by
      simpa only [BB6.Agent3.CReach,
        show (363216*t+103767)+(342680*t+97900)-2=(705896*t+201665) by omega,
        show ((342680*t+97900)-2)/2=(171340*t+48949) by omega] using hg4
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) h4

/-- All-time source-authentic low stopping target nonreachability for
    m=512*z+67, z=585 modulo 1024. -/
theorem low_stop_m67_z585_mod1024_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%1024=585)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 524288 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^19 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^19=524288 by decide] using h
  have hpmod : (2^(2*m+3))%524288=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hkmod : k%524288=149811 := by
    have hs : (k+3*m+4)%524288=0 := by
      rw [hstop]
      exact hpmod
    rw [hm] at hs
    omega
  let u := 2048*(k/524288)+585
  have hu : u%2048=585 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 524288
    rw [hkmod] at hh
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (rectangle_u585_mod2048_unreachable u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)


#print axioms low_stop_m67_z165_mod256_unreachable
#print axioms low_stop_m67_z105_mod512_unreachable
#print axioms low_stop_m67_z469_mod1024_unreachable
#print axioms low_stop_m67_z869_mod1024_unreachable
#print axioms low_stop_m67_z585_mod1024_unreachable
end BB6.Agent13FiveD23
