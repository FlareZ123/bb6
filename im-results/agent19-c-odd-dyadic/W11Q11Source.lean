import U5B2Root32
import EvenOddFourExact
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 16384
set_option maxHeartbeats 200000

namespace BB6.Agent19W11Q11
open BB6.Agent46

/-
  W11, q = 128*s+11. This file deliberately keeps the new cylinder
  separate from U5B2Root32's accepted base theorem. It composes only
  original-section reachability equivalences and the accepted B2 -> P4
  implication.
-/

def pX (s : Nat) : Nat := 61014457967 + 665924474880*s
def pY (s : Nat) : Nat := 52132129384 + 568980894720*s

def qX (s : Nat) : Nat := 113146587349 + 1234905369600*s
def qY (s : Nat) : Nat := 26066064691 + 284490447360*s

def aX (s : Nat) : Nat := 28286646835 + 308726342400*s
def aY (s : Nat) : Nat := 68496034945 + 747579960960*s

def dqX (s : Nat) : Nat := 69606326018 + 759697908480*s
def dqY (s : Nat) : Nat := 47836195353 + 522094177920*s
def rqX (s : Nat) : Nat := 58721260683 + 640896043200*s
def rqY (s : Nat) : Nat := 53278728017 + 581495110560*s
def tqX (s : Nat) : Nat := 55999994348 + 611195576880*s
def tqY (s : Nat) : Nat := 54639361181 + 596345343720*s

def daX (s : Nat) : Nat := 48391340888 + 528153151680*s
def daY (s : Nat) : Nat := 58443687915 + 637866556320*s
def raX (s : Nat) : Nat := 53417514399 + 583009854000*s
def raY (s : Nat) : Nat := 55930601156 + 610438205160*s
def taX (s : Nat) : Nat := 109348115553 + 1193448059160*s
def taY (s : Nat) : Nat := 27965300577 + 305219102580*s

/-- The complete original-source parent fan of P(128*s+11).
    Every case comes from the exact all-branch source preimage grammar. -/
theorem p_parent_fan (s a k : Nat)
    (hedge : secNext (a,k) = some (pX s,pY s)) :
    (a=qX s ∧ k=qY s) ∨ (a=aX s ∧ k=aY s) := by
  have hp := (section_preimage_all_iff a k (pX s) (pY s)).mp hedge
  by_cases ha0 : a=0
  · subst a
    by_cases hk0 : k=0
    · simp [sectionPreimageAll,hk0] at hp <;> omega
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,hk0,hk1] at hp <;> omega
      · have hcase :
            4≤pY s ∧ ∃ n : Nat,
              pX s+pY s=2^n*8 ∧ (2*k+1)+8+3*n=pX s+2*pY s := by
          simpa [sectionPreimageAll,hk0,hk1] using hp
        rcases hcase with ⟨_,n,hpow,_⟩
        have hodd : (pX s+pY s)%2=1 := by
          dsimp [pX,pY]
          omega
        have heven : (2^n*8)%2=0 := by simp [Nat.mul_mod]
        rw [hpow] at hodd
        omega
  · by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,hk0] at hp <;> omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,hk0,hk1] at hp <;> omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,hk0,hk1,hk2] at hp <;> omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,hk0,hk1,hk2,hk3] at hp <;> omega
            · have hcase :
                  (pY s=3 ∧ ∃ n : Nat,
                    pX s+6=2^n*16 ∧
                    (2*k-3)+16+3*n=pX s+10) ∨
                  (5≤pY s ∧ ∃ n : Nat,
                    pX s+pY s+1=2^n*16 ∧
                    (2*k-3)+16+3*n=pX s+2*pY s+2) := by
                simpa [sectionPreimageAll,hk0,hk1,hk2,hk3] using hp
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · dsimp [pY] at hy3
                omega
              · have hmod : (pX s+pY s+1)%16=8 := by
                  dsimp [pX,pY]
                  omega
                have hdiv : 16∣2^n*16 := ⟨2^n,by ring⟩
                have hzero : (pX s+pY s+1)%16=0 := by
                  rw [hpow]
                  exact Nat.mod_eq_zero_of_dvd hdiv
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hlow : 2*k≤a
        · have hcase : pX s=a-2*k ∧ pY s=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          rcases hcase with ⟨hx,hy⟩
          left
          constructor
          · dsimp [qX,pX,pY]
            omega
          · dsimp [qY,pY]
            omega
        · by_cases haeven : a%2=0
          · have hcase :
                4≤pY s ∧ ∃ n : Nat,
                  pX s+pY s=2^n*(2*(a-1)+6) ∧
                  (2*k-a+3)+(2*(a-1)+6)+3*n=pX s+2*pY s := by
                simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨_,n,hpow,_⟩
            have hodd : (pX s+pY s)%2=1 := by
              dsimp [pX,pY]
              omega
            have heven : (2^n*(2*(a-1)+6))%2=0 := by
              simp [Nat.mul_mod]
            rw [hpow] at hodd
            omega
          · have haodd : a%2=1 := by omega
            have hcase :
                  (pY s=3 ∧ ∃ n : Nat,
                    pX s+6=2^n*(2*(a-1)+8) ∧
                    (2*k-a+3)+(2*(a-1)+8)+3*n=pX s+10) ∨
                  (5≤pY s ∧ ∃ n : Nat,
                    pX s+pY s+1=2^n*(2*(a-1)+8) ∧
                    (2*k-a+3)+(2*(a-1)+8)+3*n=pX s+2*pY s+2) := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,hcost⟩
            · dsimp [pY] at hy3
              omega
            · have hmod16 : (pX s+pY s+1)%16=8 := by
                dsimp [pX,pY]
                omega
              have hnlt2 : n<2 := by
                by_contra hn
                have hn2 : 2≤n := by omega
                have hpow4 : 4∣2^n := by
                  have h := Nat.pow_dvd_pow 2 hn2
                  simpa only [show (2:Nat)^2=4 by decide] using h
                have hsub : (a-1)%2=0 := by omega
                have hfac4 : 4∣2*(a-1)+8 := by
                  obtain ⟨b,hb⟩ := Nat.dvd_of_mod_eq_zero hsub
                  refine ⟨b+2,?_⟩
                  rw [hb]
                  ring
                obtain ⟨u,hu⟩ := hpow4
                obtain ⟨v,hv⟩ := hfac4
                have hdiv16 : 16∣2^n*(2*(a-1)+8) := by
                  refine ⟨u*v,?_⟩
                  rw [hu,hv]
                  ring
                have hzero :
                    (2^n*(2*(a-1)+8))%16=0 :=
                  Nat.mod_eq_zero_of_dvd hdiv16
                rw [←hpow] at hzero
                omega
              have hcost' :
                  2*k+a+7+3*n=pX s+2*pY s := by omega
              have hnodd : n%2=1 := by
                have hxodd : pX s%2=1 := by dsimp [pX]; omega
                have hyeven : pY s%2=0 := by dsimp [pY]; omega
                omega
              have hn : n=1 := by omega
              have hpow1 :
                  pX s+pY s+1=2*(2*(a-1)+8) := by
                simpa [hn] using hpow
              have hcost1 :
                  2*k+a+10=pX s+2*pY s := by
                rw [hn] at hcost'
                omega
              right
              constructor
              · dsimp [aX,pX,pY]
                omega
              · dsimp [aY,pX,pY]
                omega

/-- The direct Q parent has three forced original-source inverse edges
    ending in the forbidden odd-right sum-one image cylinder. -/
theorem q_unreachable (s : Nat) :
    ¬ BB6.Agent3.CReach (qX s) (qY s) := by
  intro hq
  have hqRun :
      ∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (qX s,qY s) := by
    simpa [BB6.Agent3.CReach] using hq
  have hDQRun :=
    (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (qX s) (qY s)
      (by dsimp [qX]; omega) (by dsimp [qY]; omega)
      (by dsimp [qY]; omega)
      (by dsimp [qX,qY]; omega)
      (by dsimp [qX,qY]; omega)
      (by dsimp [qX,qY]; omega)).mp hqRun
  have hDQx : (qX s+qY s-4)/2=dqX s := by
    dsimp [qX,qY,dqX]
    omega
  have hDQy : (qX s+3*qY s-10)/4=dqY s := by
    dsimp [qX,qY,dqY]
    omega
  have hDQ : BB6.Agent3.CReach (dqX s) (dqY s) := by
    change (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some (dqX s,dqY s))
    simpa only [hDQx,hDQy] using hDQRun
  have hDQRun' :
      ∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (dqX s,dqY s) := by
    simpa [BB6.Agent3.CReach] using hDQ
  have hRQRun :=
    (BB6.Agent3.evenodd_four_blank_reach_iff
      (dqX s) (dqY s)
      (by dsimp [dqX]; omega) (by dsimp [dqY]; omega)
      (by dsimp [dqY]; omega)
      (by dsimp [dqX,dqY]; omega)).mp hDQRun'
  have hRQx : (dqX s+dqY s-5)/2=rqX s := by
    dsimp [dqX,dqY,rqX]
    omega
  have hRQy : (dqX s+3*dqY s-9)/4=rqY s := by
    dsimp [dqX,dqY,rqY]
    omega
  have hRQ : BB6.Agent3.CReach (rqX s) (rqY s) := by
    change (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some (rqX s,rqY s))
    simpa only [hRQx,hRQy] using hRQRun
  have hRQRun' :
      ∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (rqX s,rqY s) := by
    simpa [BB6.Agent3.CReach] using hRQ
  have hTQRun :=
    (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (rqX s) (rqY s)
      (by dsimp [rqX]; omega) (by dsimp [rqY]; omega)
      (by dsimp [rqY]; omega)
      (by dsimp [rqX,rqY]; omega)
      (by dsimp [rqX,rqY]; omega)
      (by dsimp [rqX,rqY]; omega)).mp hRQRun'
  have hTQx : (rqX s+rqY s-4)/2=tqX s := by
    dsimp [rqX,rqY,tqX]
    omega
  have hTQy : (rqX s+3*rqY s-10)/4=tqY s := by
    dsimp [rqX,rqY,tqY]
    omega
  have hTQ : BB6.Agent3.CReach (tqX s) (tqY s) := by
    change (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some (tqX s,tqY s))
    simpa only [hTQx,hTQy] using hTQRun
  exact
    (BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (tqX s) (tqY s)
      (by dsimp [tqX]; omega)
      (by dsimp [tqY]; omega)
      (by dsimp [tqY]; omega)
      (by dsimp [tqX,tqY]; omega)) hTQ

/-- The alternate A parent has three exact original-source inverse edges
    ending in the forbidden odd-right sum-two image cylinder. -/
theorem a_unreachable (s : Nat) :
    ¬ BB6.Agent3.CReach (aX s) (aY s) := by
  intro hA
  have hARun :
      ∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (aX s,aY s) := by
    simpa [BB6.Agent3.CReach] using hA
  have hDARun :=
    (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (aX s) (aY s)
      (by dsimp [aX]; omega) (by dsimp [aY]; omega)
      (by dsimp [aY]; omega)
      (by dsimp [aX,aY]; omega)
      (by dsimp [aX,aY]; omega)
      (by dsimp [aX,aY]; omega)).mp hARun
  have hDAx : (aX s+aY s-4)/2=daX s := by
    dsimp [aX,aY,daX]
    omega
  have hDAy : (aX s+3*aY s-10)/4=daY s := by
    dsimp [aX,aY,daY]
    omega
  have hDA : BB6.Agent3.CReach (daX s) (daY s) := by
    change (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some (daX s,daY s))
    simpa only [hDAx,hDAy] using hDARun
  have hDARun' :
      ∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (daX s,daY s) := by
    simpa [BB6.Agent3.CReach] using hDA
  have hRARun :=
    (BB6.Agent3.evenodd_four_blank_reach_iff
      (daX s) (daY s)
      (by dsimp [daX]; omega) (by dsimp [daY]; omega)
      (by dsimp [daY]; omega)
      (by dsimp [daX,daY]; omega)).mp hDARun'
  have hRAx : (daX s+daY s-5)/2=raX s := by
    dsimp [daX,daY,raX]
    omega
  have hRAy : (daX s+3*daY s-9)/4=raY s := by
    dsimp [daX,daY,raY]
    omega
  have hRA : BB6.Agent3.CReach (raX s) (raY s) := by
    change (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some (raX s,raY s))
    simpa only [hRAx,hRAy] using hRARun
  have hRARun' :
      ∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (raX s,raY s) := by
    simpa [BB6.Agent3.CReach] using hRA
  have hTARun :=
    (BB6.Agent15.blank_reach_iff_even_right
      (raX s) (raY s)
      (by dsimp [raY]; omega)
      (by dsimp [raY]; omega)
      (by dsimp [raX,raY]; omega)
      (by dsimp [raX,raY]; omega)).mp hRARun'
  have hTAx : raX s+raY s-2=taX s := by
    dsimp [raX,raY,taX]
    omega
  have hTAy : (raY s-2)/2=taY s := by
    dsimp [raY,taY]
    omega
  have hTA : BB6.Agent3.CReach (taX s) (taY s) := by
    change (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some (taX s,taY s))
    simpa only [hTAx,hTAy] using hTARun
  exact
    (BB6.Agent11High.blank_no_odd_sum_two
      (taX s) (taY s)
      (by dsimp [taY]; omega)
      (by dsimp [taY]; omega)
      (by dsimp [taX,taY]; omega)) hTA

/-- The P family itself is blank-unreachable: its complete source fan
    has only Q and A, and both alternatives are excluded above. -/
theorem p_unreachable (s : Nat) :
    ¬ BB6.Agent3.CReach (pX s) (pY s) := by
  intro hP
  obtain ⟨a,k,hprev,hedge⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (pX s) (pY s) (by dsimp [pX]; omega) hP
  rcases p_parent_fan s a k hedge with hQ | hA
  · have hQreach : BB6.Agent3.CReach (qX s) (qY s) := by
      simpa only [hQ.1,hQ.2] using hprev
    exact q_unreachable s hQreach
  · have hAreach : BB6.Agent3.CReach (aX s) (aY s) := by
      simpa only [hA.1,hA.2] using hprev
    exact a_unreachable s hAreach

def p4X (s : Nat) : Nat := 149837743803 + 1635360276480*s
def p4Y (s : Nat) : Nat := 7720486473 + 84262993920*s
def dSx (s : Nat) : Nat := 78779115136 + 859811635200*s
def dSy (s : Nat) : Nat := 43249800803 + 472037314560*s

/-- The B2 residual is absent for u=157622+1720320*s. This is an
    unconditional infinite parameter family, independent of the root equation. -/
theorem blank_no_b2_w11_q11 (s : Nat) :
    ¬ BB6.Agent3.CReach
      (734+10944*(157622+1720320*s))
      (34881+518816*(157622+1720320*s)) := by
  let u := 157622+1720320*s
  have huEven : u%2=0 := by dsimp [u]; omega
  intro hB2
  have hP4 :=
    BB6.Agent3U5B2Root32.b2_even_reach_implies_p4_reach u huEven hB2
  have hP4x : 63895+950614*u=p4X s := by
    dsimp [u,p4X]
    omega
  have hP4y : 3291+48981*u=p4Y s := by
    dsimp [u,p4Y]
    omega
  have hP4s : BB6.Agent3.CReach (p4X s) (p4Y s) := by
    simpa only [hP4x,hP4y] using hP4
  have hDRun :=
    (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (p4X s) (p4Y s)
      (by dsimp [p4X]; omega) (by dsimp [p4Y]; omega)
      (by dsimp [p4Y]; omega)
      (by dsimp [p4X,p4Y]; omega)
      (by dsimp [p4X,p4Y]; omega)
      (by dsimp [p4X,p4Y]; omega)).mp
      (by simpa [BB6.Agent3.CReach] using hP4s)
  have hDx : (p4X s+p4Y s-4)/2=dSx s := by
    dsimp [p4X,p4Y,dSx]
    omega
  have hDy : (p4X s+3*p4Y s-10)/4=dSy s := by
    dsimp [p4X,p4Y,dSy]
    omega
  have hD : BB6.Agent3.CReach (dSx s) (dSy s) := by
    change (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some (dSx s,dSy s))
    simpa only [hDx,hDy] using hDRun
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (dSx s) (dSy s) (by dsimp [dSx]; omega) hD
  obtain ⟨n,haOdd,hnEven,hpow,hcost⟩ :=
    BB6.Agent3U5B2Root32.even_odd_three_divisible_parent
      a k (dSx s) (dSy s)
      (by dsimp [dSx]; omega)
      (by dsimp [dSy]; omega)
      (by dsimp [dSy]; omega)
      (by dsimp [dSx,dSy]; omega)
      hstep
  have hn0 : n=0 := by
    by_contra hn
    have hn2 : 2≤n := by omega
    have hpow4 : 4∣2^n := by
      have h := Nat.pow_dvd_pow 2 hn2
      simpa only [show (2:Nat)^2=4 by decide] using h
    have hsub : (a-1)%2=0 := by omega
    have hfac4 : 4∣2*a+6 := by
      obtain ⟨b,hb⟩ := Nat.dvd_of_mod_eq_zero hsub
      refine ⟨b+2,?_⟩
      rw [hb]
      ring
    obtain ⟨v,hv⟩ := hpow4
    obtain ⟨z,hz⟩ := hfac4
    have hdiv16 : 16∣2^n*(2*a+6) := by
      refine ⟨v*z,?_⟩
      rw [hv,hz]
      ring
    have hdiv8 : 8∣2^n*(2*a+6) :=
      Nat.dvd_trans (by decide : 8∣16) hdiv16
    have hzero :
        (2^n*(2*a+6))%8=0 := Nat.mod_eq_zero_of_dvd hdiv8
    have hmod : (dSx s+dSy s+1)%8=4 := by
      dsimp [dSx,dSy]
      omega
    rw [←hpow] at hzero
    omega
  have hpow0 : dSx s+dSy s+1=2*a+6 := by
    simpa [hn0] using hpow
  have hcost0 : 2*k+a+7=dSx s+2*dSy s := by
    simpa [hn0] using hcost
  have ha : a=pX s := by
    dsimp [dSx,dSy,pX]
    omega
  have hk : k=pY s := by
    dsimp [dSx,dSy,pX,pY]
    omega
  have hPreach : BB6.Agent3.CReach (pX s) (pY s) := by
    simpa only [ha,hk] using hprev
  exact p_unreachable s hPreach

/-- The exact root equation on r=11092 (mod 16384) forces
    u=157622+1720320*s, and hence the B2 residual is blank-unreachable. -/
theorem root_q11_parameter (r E u : Nat)
    (hr : r%16384=11092)
    (hE : E=201+3360*(6657+8192*r))
    (hRoot : 18018+211*u+22155*r=20*2^(E-13)) :
    ∃ s : Nat, u=157622+1720320*s := by
  let R := r/16
  have hrEq : r=16*R+4 := by
    dsimp [R]
    have h := Nat.mod_add_div r 16
    omega
  have hmod1680 :=
    BB6.Agent3U5B2Root32ParameterBridge.root_equation_mod1680
      r E u hE hRoot
  have huMod1680 : u%1680=1382 := by
    rw [hrEq] at hmod1680
    omega
  have huMod840 : u%840=542 := by omega
  let w := u/840
  have huEq : u=542+840*w := by
    dsimp [w]
    have h := Nat.mod_add_div u 840
    omega
  have hRmod : R%1024=693 := by
    dsimp [R]
    omega
  have hpowStep : 2^(E-13)=2*2^(E-14) := by
    have hE14 : 14≤E := by rw [hE]; omega
    rw [show E-13=(E-14)+1 by omega, Nat.pow_succ]
    omega
  have hscaled :
      8*(27625+44310*R+22155*w)=8*(5*2^(E-14)) := by
    rw [huEq,hrEq,hpowStep] at hRoot
    omega
  have hEq : 27625+44310*R+22155*w=5*2^(E-14) := by omega
  have hEpow : 11≤E-14 := by rw [hE]; omega
  have hpowDiv : 2048∣2^(E-14) := by
    have h := Nat.pow_dvd_pow 2 hEpow
    simpa only [show (2:Nat)^11=2048 by decide] using h
  have hdiv : 2048∣5*2^(E-14) := by
    obtain ⟨z,hz⟩ := hpowDiv
    refine ⟨5*z,?_⟩
    rw [hz]
    ring
  have hdivW : 2048∣27625+44310*R+22155*w := by
    rw [hEq]
    exact hdiv
  have hmodW :
      (27625+44310*R+22155*w)%2048=0 :=
    Nat.mod_eq_zero_of_dvd hdivW
  obtain ⟨t,hRt⟩ : ∃ t : Nat, R=693+1024*t := by
    refine ⟨R/1024,?_⟩
    have h := Nat.mod_add_div R 1024
    omega
  rw [hRt] at hmodW
  have hwmod : w%2048=187 := by omega
  let s := w/2048
  have hwEq : w=187+2048*s := by
    dsimp [s]
    have h := Nat.mod_add_div w 2048
    omega
  refine ⟨s,?_⟩
  rw [huEq,hwEq]
  dsimp [s]
  omega

/-- Exact root-index exclusion for the W11 cylinder. This is conditional
    on the exact residual root equation; the separate arithmetic
    nonvacuity argument remains documented in the dossier. -/
theorem blank_no_b2_root_r11092 (r E u : Nat)
    (hr : r%16384=11092)
    (hE : E=201+3360*(6657+8192*r))
    (hRoot : 18018+211*u+22155*r=20*2^(E-13)) :
    ¬ BB6.Agent3.CReach (734+10944*u) (34881+518816*u) := by
  obtain ⟨s,hu⟩ := root_q11_parameter r E u hr hE hRoot
  intro hB2
  have hB2s :
      BB6.Agent3.CReach
        (734+10944*(157622+1720320*s))
        (34881+518816*(157622+1720320*s)) := by
    simpa only [hu] using hB2
  exact blank_no_b2_w11_q11 s hB2s

#print axioms p_parent_fan
#print axioms q_unreachable
#print axioms a_unreachable
#print axioms p_unreachable
#print axioms blank_no_b2_w11_q11
#print axioms root_q11_parameter
#print axioms blank_no_b2_root_r11092

end BB6.Agent19W11Q11
