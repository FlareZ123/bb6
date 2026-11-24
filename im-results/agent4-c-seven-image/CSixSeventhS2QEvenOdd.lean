import CSixSeventhS2QEven

/-!
Odd-coset extension of the q-even h5 source exclusion.

The existing h5 progression uses u = 2 + 8192*d.  This file proves an
additional odd-coset subfamily u = 4098 + 8192*r, v = 48 + 8192*b under
(5*r+b) % 8 = 2.  All reachability claims are reduced through the original
Machine C source-parent theorems imported by CSixSeventhS2QEven.
-/

namespace BB6.Agent4SevenS2QEven

private def qEvenH5OddU (r : Nat) : Nat := 4098+8192*r
private def qEvenH5OddV (b : Nat) : Nat := 48+8192*b
private def qEvenH5OddT (r b : Nat) : Nat := 1036+2048*(r+b)
private def qEvenH5OddZ (r b : Nat) : Nat := 355+704*r+448*b

/-- The odd-coset residual pair is absent from the genuine blank-origin
    Machine C section orbit whenever 5*r+b = 2 (mod 8). -/
private theorem q_even_h5_residual_unreachable_odd (r b : Nat)
    (hmod : (5*r+b)%8=2) :
    ¬ BB6.Agent3.CReach
      (3661268+7148544*r+14296064*b)
      (317564+620032*r+1240576*b) := by
  let x := 3661268+7148544*r+14296064*b
  let y := 317564+620032*r+1240576*b
  let S := 497354+971072*r+1942080*b
  let Dpx := 3978830+7768576*r+15536640*b
  let Dpy := 158781+310016*r+620288*b
  let D1x := 2068803+4039296*r+8078464*b
  let D1y := 1113791+2174656*r+4349376*b
  let Ex := 994706+1942144*r+3884160*b
  let Ey := 1650840+3223232*r+6446528*b
  let Erx := 2645544+5165376*r+10330688*b
  let Ery := 825419+1611616*r+3223264*b
  let Eax := 1735479+3388496*r+6776976*b
  let Eay := 1280448+2500056*r+5000120*b
  let Ebx := 3015925+5888552*r+11777096*b
  let Eby := 640223+1250028*r+2500060*b
  have hxy : x+y=8*S := by dsimp [x,y,S]; omega
  have hS4 : S%4=2 := by dsimp [S]; omega
  have hSgt : 2<S := by dsimp [S]; omega
  have hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
    intro h
    have hDx : x+y-2=Dpx := by dsimp [x,y,Dpx]; omega
    have hDy : (y-2)/2=Dpy := by dsimp [y,Dpy]; omega
    have hDreach : BB6.Agent3.CReach Dpx Dpy := by
      simpa only [hDx,hDy] using h
    have hgate := (BB6.Agent3.evenodd_four_blank_reach_iff Dpx Dpy
      (by dsimp [Dpx]; omega) (by dsimp [Dpy]; omega)
      (by dsimp [Dpy]; omega) (by dsimp [Dpx,Dpy]; omega)).mp hDreach
    have hD1x : (Dpx+Dpy-5)/2=D1x := by
      dsimp [Dpx,Dpy,D1x]; omega
    have hD1y : (Dpx+3*Dpy-9)/4=D1y := by
      dsimp [Dpx,Dpy,D1y]; omega
    have hD1reach : BB6.Agent3.CReach D1x D1y := by
      rcases hgate with ⟨time,htime⟩
      exact ⟨time,by simpa only [hD1x,hD1y] using htime⟩
    exact BB6.Agent11High.blank_no_odd_sum_two D1x D1y
      (by dsimp [D1y]; omega) (by dsimp [D1y]; omega)
      (by dsimp [D1x,D1y]; omega) hD1reach
  have hE : ¬ BB6.Agent3.CReach (2*S-2) ((x+2*y-2*S-8)/2) := by
    intro h
    have hEx : 2*S-2=Ex := by dsimp [S,Ex]; omega
    have hEy : (x+2*y-2*S-8)/2=Ey := by dsimp [x,y,S,Ey]; omega
    have hEreach : BB6.Agent3.CReach Ex Ey := by
      simpa only [hEx,hEy] using h
    have hgate0 := (six_even_right_blank_reach_iff Ex Ey
      (by dsimp [Ex]; omega) (by dsimp [Ey]; omega)
      (by dsimp [Ey]; omega) (by dsimp [Ex,Ey]; omega)).mp hEreach
    have hErx : Ex+Ey-2=Erx := by dsimp [Ex,Ey,Erx]; omega
    have hEry : (Ey-2)/2=Ery := by dsimp [Ey,Ery]; omega
    have hErreach : BB6.Agent3.CReach Erx Ery := by
      rcases hgate0 with ⟨time,htime⟩
      exact ⟨time,by simpa only [hErx,hEry] using htime⟩
    have hgate1 := (BB6.Agent3.evenodd_four_blank_reach_iff Erx Ery
      (by dsimp [Erx]; omega) (by dsimp [Ery]; omega)
      (by dsimp [Ery]; omega) (by dsimp [Erx,Ery]; omega)).mp hErreach
    have hEax : (Erx+Ery-5)/2=Eax := by
      dsimp [Erx,Ery,Eax]; omega
    have hEay : (Erx+3*Ery-9)/4=Eay := by
      dsimp [Erx,Ery,Eay]; omega
    have hEareach : BB6.Agent3.CReach Eax Eay := by
      rcases hgate1 with ⟨time,htime⟩
      exact ⟨time,by simpa only [hEax,hEay] using htime⟩
    have hgate2 := (six_even_right_blank_reach_iff Eax Eay
      (by dsimp [Eax]; omega) (by dsimp [Eay]; omega)
      (by dsimp [Eay]; omega) (by dsimp [Eax,Eay]; omega)).mp hEareach
    have hEbx : Eax+Eay-2=Ebx := by dsimp [Eax,Eay,Ebx]; omega
    have hEby : (Eay-2)/2=Eby := by dsimp [Eay,Eby]; omega
    have hEbreach : BB6.Agent3.CReach Ebx Eby := by
      rcases hgate2 with ⟨time,htime⟩
      exact ⟨time,by simpa only [hEbx,hEby] using htime⟩
    have hlow := (BB6.Agent3.oddodd_lowval_blank_reach_iff Ebx Eby
      (by dsimp [Eby]; omega) (by dsimp [Eby]; omega)
      (by dsimp [Ebx,Eby]; omega) (by dsimp [Ebx,Eby]; omega)
      (by dsimp [Ebx,Eby]; omega) (by dsimp [Ebx,Eby]; omega)).mp hEbreach
    let P0x := 1828072+3569290*r+7138578*b
    let P0y := 1234146+2409659*r+4819319*b
    have hP0x : (Ebx+Eby-4)/2=P0x := by
      dsimp [Ebx,Eby,P0x]; omega
    have hP0y : (Ebx+3*Eby-10)/4=P0y := by
      dsimp [Ebx,Eby,P0y]; omega
    have hP0reach : BB6.Agent3.CReach P0x P0y := by
      rcases hlow with ⟨time,htime⟩
      exact ⟨time,by simpa only [hP0x,hP0y] using htime⟩
    have hgateP := (six_even_right_blank_reach_iff P0x P0y
      (by dsimp [P0y]; omega) (by dsimp [P0y]; omega)
      (by dsimp [P0x,P0y]; omega) (by dsimp [P0x,P0y]; omega)).mp hP0reach
    let D0x := P0x+P0y-2
    let D0y := (P0y-2)/2
    have hD0reach : BB6.Agent3.CReach D0x D0y := by
      rcases hgateP with ⟨time,htime⟩
      exact ⟨time,by simp [D0x,D0y] at htime ⊢; exact htime⟩
    exact BB6.Agent11High.blank_no_odd_sum_one D0x D0y
      (by dsimp [D0y,P0y]; omega) (by dsimp [D0y,P0y]; omega)
      (by dsimp [D0x,D0y,P0x,P0y]; omega) hD0reach
  exact BB6.Agent11M0SumZeroVerified.blank_no_v2one_target x y S
    (by dsimp [x]; omega) (by dsimp [x]; omega)
    (by dsimp [y]; omega) (by dsimp [y]; omega)
    hxy hS4 hSgt hD hE

/-- The odd h5 direct parent is absent under the residue condition. -/
private theorem q_even_p_blank_unreachable_h5_odd (r b : Nat)
    (hmod : (5*r+b)%8=2) :
    ¬ BB6.Agent3.CReach
      (1113+650*qEvenH5OddU r+1298*qEvenH5OddV b)
      (321+187*qEvenH5OddU r+375*qEvenH5OddV b) := by
  let u := qEvenH5OddU r
  let v := qEvenH5OddV b
  let t := qEvenH5OddT r b
  let z := qEvenH5OddZ r b
  let px := 1113+650*u+1298*v
  let py := 321+187*u+375*v
  let A := 6568+6272*t-13376*z
  let B := 4758+4544*t-9696*z
  let W := 595+568*t-1212*z
  let F1x := A+8*W-4
  let F1y := 4*W-2
  let F2x := A+12*W-8
  let F2y := 2*W-2
  have hlo : 7*t+10≤32*z := by dsimp [t,z,qEvenH5OddT,qEvenH5OddZ]; omega
  have hhi : 32*z≤12+11*t := by dsimp [t,z,qEvenH5OddT,qEvenH5OddZ]; omega
  have hsum : u+v=2+4*t := by dsimp [u,v,t,qEvenH5OddU,qEvenH5OddV,qEvenH5OddT]; omega
  have hAeq : (px+py-4)/2=A := by
    dsimp [px,py,A,u,v,t,z,qEvenH5OddU,qEvenH5OddV,qEvenH5OddT,qEvenH5OddZ]
    omega
  have hBeq : (px+3*py-10)/4=B := by
    dsimp [px,py,B,u,v,t,z,qEvenH5OddU,qEvenH5OddV,qEvenH5OddT,qEvenH5OddZ]
    omega
  have hW : B+2=8*W := by dsimp [B,W,t,z,qEvenH5OddT,qEvenH5OddZ]; omega
  have hAmin : 5<A := by dsimp [A]; omega
  have hBmin : 6≤B := by dsimp [B]; omega
  have hWmin : 5≤W := by dsimp [W]; omega
  have hWmod : W%4=3 := by dsimp [W,t,z,qEvenH5OddT,qEvenH5OddZ]; omega
  have hBmod : B%8=6 := by omega
  have hsum0 : (A+B)%8=6 := by dsimp [A,B,t,z,qEvenH5OddT,qEvenH5OddZ]; omega
  have hF1x : A+B-2=F1x := by dsimp [F1x]; omega
  have hF1y : (B-2)/2=F1y := by dsimp [F1y]; omega
  have hF1sum : (F1x+F1y)%8=6 := by dsimp [F1x,F1y]; omega
  have hF1min : 6≤F1y := by dsimp [F1y]; omega
  have hF2x : F1x+F1y-2=F2x := by dsimp [F1x,F1y,F2x]; omega
  have hF2y : (F1y-2)/2=F2y := by dsimp [F1y,F2y]; omega
  have hF2min : 6≤F2y := by dsimp [F2y]; omega
  have hF2sum : (F2x+F2y)%8=0 := by dsimp [F2x,F2y]; omega
  have hAreach : ¬ BB6.Agent3.CReach A B := by
    intro hp
    have hgate0 := (six_even_right_blank_reach_iff A B
      (by omega) (by omega) (by omega) (by omega)).mp hp
    have hF1reach : BB6.Agent3.CReach F1x F1y := by
      rcases hgate0 with ⟨time,htime⟩
      exact ⟨time,by simpa only [hF1x,hF1y] using htime⟩
    have hgate1 := (six_even_right_blank_reach_iff F1x F1y
      (by omega) (by omega) (by omega) (by omega)).mp hF1reach
    have hF2reach : BB6.Agent3.CReach F2x F2y := by
      rcases hgate1 with ⟨time,htime⟩
      exact ⟨time,by simpa only [hF2x,hF2y] using htime⟩
    have hF2xeq : F2x=3661268+7148544*r+14296064*b := by
      dsimp [F2x,A,W,t,z,qEvenH5OddT,qEvenH5OddZ]; omega
    have hF2yeq : F2y=317564+620032*r+1240576*b := by
      dsimp [F2y,W,t,z,qEvenH5OddT,qEvenH5OddZ]; omega
    have hF2reach' : BB6.Agent3.CReach
        (3661268+7148544*r+14296064*b)
        (317564+620032*r+1240576*b) := by
      rcases hF2reach with ⟨time,htime⟩
      exact ⟨time,by simpa only [hF2xeq,hF2yeq] using htime⟩
    exact q_even_h5_residual_unreachable_odd r b hmod hF2reach'
  intro hp
  have hiff := (BB6.Agent3.oddodd_lowval_blank_reach_iff
    px py (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).mp hp
  rcases hiff with ⟨time,htime⟩
  exact hAreach ⟨time,by simpa only [hAeq,hBeq] using htime⟩

/-- The odd h5 R-image is absent under the residue condition. -/
private theorem q_even_r_blank_unreachable_h5_odd (r b : Nat)
    (hmod : (5*r+b)%8=2) :
    ¬ BB6.Agent3.CReach
      (471+276*qEvenH5OddU r+548*qEvenH5OddV b)
      (644+374*qEvenH5OddU r+750*qEvenH5OddV b) := by
  let u := qEvenH5OddU r
  let v := qEvenH5OddV b
  let t := qEvenH5OddT r b
  let z := qEvenH5OddZ r b
  have hlo : 7*t+10≤32*z := by dsimp [t,z,qEvenH5OddT,qEvenH5OddZ]; omega
  have hhi : 32*z≤12+11*t := by dsimp [t,z,qEvenH5OddT,qEvenH5OddZ]; omega
  have hsum : u+v=2+4*t := by dsimp [u,v,t,qEvenH5OddU,qEvenH5OddV,qEvenH5OddT]; omega
  have hv : v%32=(12+11*t)%32 := by dsimp [v,t,qEvenH5OddV,qEvenH5OddT]; omega
  have hvdef : v=12+11*t-32*z := by dsimp [v,t,z,qEvenH5OddV,qEvenH5OddT,qEvenH5OddZ]; omega
  intro hr
  rcases hr with ⟨time,hrun⟩
  cases time with
  | zero => exact q_even_zero_not_initial_target _ _ (by omega) hrun
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at hrun
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some
              (471+276*u+548*v,644+374*u+750*v) := by
            simpa [BB6.Agent8Section.run,hp] using hrun
          have hpre : sectionPreimageAll a k
              (471+276*u+548*v) (644+374*u+750*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          rcases q_even_R_parents u v t a k hsum hv hpre with hP|hQ
          · have hPreach : BB6.Agent3.CReach
                (1113+650*u+1298*v) (321+187*u+375*v) := by
              refine ⟨n,?_⟩
              simpa [hP.1,hP.2] using hp
            exact q_even_p_blank_unreachable_h5_odd r b hmod hPreach
          · have hQreach : BB6.Agent3.CReach
                (601+650*t+162*v) (1598+1723*t+431*v) := by
              refine ⟨n,?_⟩
              simpa [hQ.1,hQ.2] using hp
            exact q_even_q_blank_unreachable t z hlo hhi
              (by simpa only [hvdef] using hQreach)

/-- The odd h5 P2 parent is absent, by reduction to the odd R-image theorem. -/
private theorem q_even_p2_blank_unreachable_h5_odd (r b : Nat)
    (hmod : (5*r+b)%8=2) :
    ¬ BB6.Agent3.CReach
      (128+80*qEvenH5OddU r+144*qEvenH5OddV b)
      (819+472*qEvenH5OddU r+952*qEvenH5OddV b) := by
  let u := qEvenH5OddU r
  let v := qEvenH5OddV b
  intro hr
  rcases hr with ⟨time,htime⟩
  cases time with
  | zero => exact q_even_zero_not_initial_target _ _ (by omega) htime
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at htime
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some
              (128+80*u+144*v,819+472*u+952*v) := by
            simpa [BB6.Agent8Section.run,hp] using htime
          have hpre : sectionPreimageAll a k
              (128+80*u+144*v) (819+472*u+952*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          obtain ⟨ha,hk⟩ := high_two_unique a k u v hpre
          have hR : BB6.Agent3.CReach
              (471+276*u+548*v) (644+374*u+750*v) := by
            refine ⟨n,?_⟩
            simpa [ha,hk] using hp
          exact q_even_r_blank_unreachable_h5_odd r b hmod hR

/-- The odd h5 H1 parent is absent, using the generic P0 exclusion and the
    odd-coset P2-to-R reduction. -/
private theorem q_even_h1_blank_unreachable_h5_odd (r b : Nat)
    (hmod : (5*r+b)%8=2) :
    ¬ BB6.Agent3.CReach
      (301+256*qEvenH5OddU r+256*qEvenH5OddV b)
      (739+384*qEvenH5OddU r+896*qEvenH5OddV b) := by
  let u := qEvenH5OddU r
  let v := qEvenH5OddV b
  intro hr
  rcases hr with ⟨time,htime⟩
  cases time with
  | zero => exact q_even_zero_not_initial_target _ _ (by omega) htime
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at htime
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some
              (301+256*u+256*v,739+384*u+896*v) := by
            simpa [BB6.Agent8Section.run,hp] using htime
          have hpre : sectionPreimageAll a k
              (301+256*u+256*v) (739+384*u+896*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          rcases high_one_two_parents a k u v hpre with hP0|hP2
          · have hP0reach : BB6.Agent3.CReach
                (518+320*u+576*v) (627+352*u+736*v) := by
              refine ⟨n,?_⟩
              simpa [hP0.1,hP0.2] using hp
            exact q_even_p0_blank_unreachable u v hP0reach
          · have hP2reach : BB6.Agent3.CReach
                (128+80*u+144*v) (819+472*u+952*v) := by
              refine ⟨n,?_⟩
              simpa [hP2.1,hP2.2] using hp
            exact q_even_p2_blank_unreachable_h5_odd r b hmod hP2reach

/-- Exact original-source exclusion for the odd h5 q-even image subfamily. -/
theorem blank_ne_s2q_even_image_h5_odd_subfamily
    (r b time : Nat) (hmod : (5*r+b)%8=2) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (641+1024*(4098+8192*r),574+1024*(48+8192*b)) := by
  let u := qEvenH5OddU r
  let v := qEvenH5OddV b
  intro hr
  cases time with
  | zero => exact q_even_zero_not_initial_target _ _ (by omega) hr
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at hr
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some (641+1024*u,574+1024*v) := by
            simpa [u,v,qEvenH5OddU,qEvenH5OddV,BB6.Agent8Section.run,hp] using hr
          have hpre : sectionPreimageAll a k (641+1024*u) (574+1024*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          rcases target_three_parents a k u v hpre with hD|hH1|hH3
          · have hDreach : BB6.Agent3.CReach
                (1213+1024*u+1024*v) (286+512*v) := by
              refine ⟨n,?_⟩
              simpa [hD.1,hD.2] using hp
            exact q_even_d_blank_unreachable u v hDreach
          · have hH1reach : BB6.Agent3.CReach
                (301+256*u+256*v) (739+384*u+896*v) := by
              refine ⟨n,?_⟩
              simpa [hH1.1,hH1.2] using hp
            exact q_even_h1_blank_unreachable_h5_odd r b hmod hH1reach
          · have hH3reach : BB6.Agent3.CReach
                (73+64*u+64*v) (850+480*u+992*v) := by
              refine ⟨n,?_⟩
              simpa [hH3.1,hH3.2] using hp
            exact q_even_h3_blank_unreachable u v hH3reach

end BB6.Agent4SevenS2QEven
