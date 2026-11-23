import Root32HighStopA4Core
import Root32HighStopR10592LCore
import Root32P7E1EGenericA4
import EvenRightSixOrbit
import OddEvenUnique
import OddOddLowVal
import MixedMod16SevenOrbit
import OddSevenForcedRoot
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

namespace BB6.Agent6A4T719Q0EvenS8

open BB6.Agent46

abbrev RunReach (x y : Nat) : Prop :=
  BB6.Agent3Root32HighStopA4Core.RunReach x y

def T0x (s : Nat) : Nat := 1773156457998 + 2524388401920*s
def T0y (s : Nat) : Nat := 1647558417041 + 2345578327680*s

def A4Q1x (s : Nat) : Nat := 443289114498 + 631097100480*s
def A4Q1y (s : Nat) : Nat := 2312492088788 + 3292223978400*s
def A4Q1Dx (s : Nat) : Nat := 2755781203284 + 3923321078880*s
def A4Q1Dy (s : Nat) : Nat := 1156246044393 + 1646111989200*s

def T0Q1x (s : Nat) : Nat := 427589359377 + 608745841200*s
def T0Q1y (s : Nat) : Nat := 2320341966345 + 3303398633040*s

def P0x (s : Nat) : Nat := 1710357437517 + 2434983364800*s
def P0y (s : Nat) : Nat := 1678957927278 + 2390280846240*s
def R0x (s : Nat) : Nat := 3389315364793 + 4825264211040*s
def R0y (s : Nat) : Nat := 839478963638 + 1195140423120*s

def R1x (m : Nat) : Nat := 4228794328429 + 48163237073280*m
def R1y (m : Nat) : Nat := 419739481818 + 4780561692480*m

def D1x (m : Nat) : Nat := 4648533810245 + 52943798765760*m
def D1y (m : Nat) : Nat := 209869740908 + 2390280846240*m
def E1x (m : Nat) : Nat := 4858403551151 + 55334079612000*m
def E1y (m : Nat) : Nat := 104934870453 + 1195140423120*m
def F1x (m : Nat) : Nat := 2481669210800 + 28264610017560*m
def F1y (m : Nat) : Nat := 1293302040625 + 14729875220340*m

def B1x (m : Nat) : Nat := 1162133452559 + 13235949691440*m
def B1y (m : Nat) : Nat := 1953069919748 + 22244205383400*m
def G1x (m : Nat) : Nat := 3115203372305 + 35480155074840*m
def G1y (m : Nat) : Nat := 976534959873 + 11122102691700*m

/-- An odd factor greater than one cannot turn a positive power of two
into another power of two. -/
private theorem no_pow2_mul_odd_gt_one (d w n : Nat)
    (hd : 0<d) (hodd : w%2=1) (hgt : 1<w)
    (heq : 2^d*w=2^n) : False := by
  have hdiv : 2^d ∣ 2^n := ⟨w,heq.symm⟩
  have hn : d≤n :=
    (Nat.pow_dvd_pow_iff_le_right (by decide : 1<2)).mp hdiv
  have hfactor : 2^n=2^d*2^(n-d) := by
    calc
      2^n = 2^(d+(n-d)) := by congr 1 <;> omega
      _ = 2^d*2^(n-d) := by rw [Nat.pow_add]
  have hmul : 2^d*w=2^d*2^(n-d) := by
    calc
      2^d*w = 2^n := heq
      _ = 2^d*2^(n-d) := hfactor
  have hw : w=2^(n-d) := by
    apply Nat.mul_left_cancel (by positivity : 0<2^d)
    exact hmul
  by_cases hz : n-d=0
  · rw [hz] at hw
    simp at hw
    omega
  · have hpos : 1≤n-d := by omega
    have hdiv2 : 2∣2^(n-d) := by
      have h := Nat.pow_dvd_pow 2 hpos
      simpa using h
    have heven : w%2=0 := by
      rw [hw]
      exact Nat.mod_eq_zero_of_dvd hdiv2
    omega

/-- The even/even sum-two source fan has only its direct parent. -/
theorem even_even_sum2_reach_forces_direct (x y : Nat)
    (hx : 5<x) (hxe : x%2=0)
    (hy : 6≤y) (hye : y%2=0)
    (hsum : (x+y)%4=2)
    (hr : RunReach x y) :
    RunReach (x+y-2) ((y-2)/2) := by
  obtain ⟨a,k,hprev,hedge⟩ :=
    BB6.Agent3Root32HighStopA4Core.run_parent_of_left_gt5 x y hx hr
  have hfan := BB6.Agent3ParentFan.even_even_parent_fan
    a k x y (by omega) hxe hy hye hedge
  rcases hfan with hdirect | hzero | hbounce
  · rcases hdirect with ⟨ha,hk⟩
    simpa [ha,hk] using hprev
  · rcases hzero with ⟨_,_,n,hxy,_⟩
    have hdiv : 4∣x+y := by
      refine ⟨2^n*2,?_⟩
      rw [hxy]
      omega
    have hmod := Nat.mod_eq_zero_of_dvd hdiv
    omega
  · rcases hbounce with ⟨_,_,_,_,n,hnodd,hxy,_⟩
    have hn : 2≤n+1 := by omega
    have hdivPow : 4∣2^(n+1) := by
      have h := Nat.pow_dvd_pow 2 hn
      simpa only [show (2:Nat)^2=4 by decide] using h
    have hdiv : 4∣x+y := by
      rcases hdivPow with ⟨q,hq⟩
      refine ⟨q*(a+2),?_⟩
      calc
        x+y = 2^(n+1)*(a+2) := hxy
        _ = (4*q)*(a+2) := by rw [hq]
        _ = 4*(q*(a+2)) := by ac_rfl
    have hmod := Nat.mod_eq_zero_of_dvd hdiv
    omega

/-- Exact all-depth parent classification for A4(719+1024*s).
The q=0 parent is T0(s); q=1 is the displayed even/even parent. -/
private theorem a4_source_parent_cases (s a k : Nat)
    (hstep : secNext (a,k) =
      some (BB6.Agent3Root32HighStopA4Core.a4X (719+1024*s),
            BB6.Agent3Root32HighStopA4Core.a4Y (719+1024*s))) :
    (a=T0x s ∧ k=T0y s) ∨
    (a=A4Q1x s ∧ k=A4Q1y s) := by
  let t := 719+1024*s
  let x := BB6.Agent3Root32HighStopA4Core.a4X t
  let y := BB6.Agent3Root32HighStopA4Core.a4Y t
  let W := 110822278625+157774275120*s
  have hx : x%2=1 := by dsimp [x,t,BB6.Agent3Root32HighStopA4Core.a4X]; omega
  have hy : y%2=1 := by dsimp [y,t,BB6.Agent3Root32HighStopA4Core.a4Y]; omega
  have hy5 : 5≤y := by dsimp [y,t,BB6.Agent3Root32HighStopA4Core.a4Y]; omega
  have hsum : x+y=32*W := by
    dsimp [x,y,t,W,BB6.Agent3Root32HighStopA4Core.a4X,
      BB6.Agent3Root32HighStopA4Core.a4Y]
    omega
  have hWodd : W%2=1 := by dsimp [W]; omega
  have hWgt : 1<W := by dsimp [W]; omega
  have hsumMod64 : (x+y)%64=32 := by rw [hsum]; omega
  have hp := (section_preimage_all_iff a k x y).mp hstep
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp <;> omega
      · have hcase : 4≤y ∧ ∃ n : Nat,
            x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y := by
          simpa [sectionPreimageAll,ha0,hk0,hk1] using hp
        rcases hcase with ⟨_,n,hpow,_⟩
        have heq : 2^2*W=2^n := by rw [hsum] at hpow; omega
        exact False.elim (no_pow2_mul_odd_gt_one 2 W n (by omega) hWodd hWgt heq)
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp <;> omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp <;> omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp <;> omega
            · have hcase :
                  (y=3 ∧ ∃ n : Nat, x+6=2^n*16 ∧
                    (2*k-3)+16+3*n=x+10) ∨
                  (5≤y ∧ ∃ n : Nat, x+y+1=2^n*16 ∧
                    (2*k-3)+16+3*n=x+2*y+2) := by
                simpa [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] using hp
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hodd : (x+y+1)%2=1 := by omega
                have heven : (x+y+1)%2=0 := by
                  rw [hpow]
                  simp [Nat.mul_mod]
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hlow : 2*k≤a
        · have hcase : x=a-2*k ∧ y=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          rcases hcase with ⟨_,hyy⟩
          omega
        · by_cases haeven : a%2=0
          · have hcase : 4≤y ∧ ∃ n : Nat,
                x+y=2^n*(2*(a-1)+6) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨_,n,hpow,hcost⟩
            have hsum' : x+y=2^n*(2*a+4) := by omega
            have hcost' : 2*k+a+7+3*n=x+2*y := by omega
            have hnEven : n%2=0 := by omega
            have hnle : n≤3 := by
              by_cases hn4 : 4≤n
              · have hpowdiv : 2^4∣2^n := Nat.pow_dvd_pow 2 hn4
                have ha2even : (a+2)%2=0 := by omega
                have ha2div : 2∣a+2 :=
                  Nat.dvd_iff_mod_eq_zero.mpr ha2even
                rcases hpowdiv with ⟨p,hp⟩
                rcases ha2div with ⟨q,hq⟩
                have hfac : 2*a+4=4*q := by omega
                have hdiv : 64∣x+y := by
                  refine ⟨p*q,?_⟩
                  calc
                    x+y = 2^n*(2*a+4) := hsum'
                    _ = (2^4*p)*(4*q) := by rw [← hp,hfac]
                    _ = 64*(p*q) := by norm_num [show (2:Nat)^4=16 by decide]; ring
                have hzero := Nat.mod_eq_zero_of_dvd hdiv
                omega
              · omega
            have hdepth : n=0 ∨ n=2 := by omega
            rcases hdepth with hn | hn
            · subst n
              left
              have hT0sum : 2*T0x s = x+y-4 := by
                dsimp [T0x,x,y,t,BB6.Agent3Root32HighStopA4Core.a4X,
                  BB6.Agent3Root32HighStopA4Core.a4Y]
                omega
              have hT0cost : 2*T0y s+T0x s+7=x+2*y := by
                dsimp [T0x,T0y,x,y,t,BB6.Agent3Root32HighStopA4Core.a4X,
                  BB6.Agent3Root32HighStopA4Core.a4Y]
                omega
              constructor
              · omega
              · omega
            · subst n
              right
              have hQ1sum : x+y=8*(A4Q1x s+2) := by
                dsimp [A4Q1x,x,y,t,BB6.Agent3Root32HighStopA4Core.a4X,
                  BB6.Agent3Root32HighStopA4Core.a4Y]
                omega
              have hQ1cost : 2*A4Q1y s+A4Q1x s+13=x+2*y := by
                dsimp [A4Q1x,A4Q1y,x,y,t,BB6.Agent3Root32HighStopA4Core.a4X,
                  BB6.Agent3Root32HighStopA4Core.a4Y]
                omega
              constructor <;> omega
          · have hcase :
                (y=3 ∧ ∃ n : Nat, x+6=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
                (5≤y ∧ ∃ n : Nat,
                  x+y+1=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
            · omega
            · have hodd : (x+y+1)%2=1 := by omega
              have hEvenFactor : (2*(a-1)+8)%2=0 := by omega
              have heven : (x+y+1)%2=0 := by
                rw [hpow,Nat.mul_mod]
                simp [hEvenFactor]
              omega

/-- The q=1 A4 parent is even/even with sum 2 mod 4. Its direct
predecessor is even/odd with sum-plus-one 2 mod 4 and has no parent. -/
theorem a4_q1_parent_unreachable (s : Nat) :
    ¬ RunReach (A4Q1x s) (A4Q1y s) := by
  intro hreach
  have hx : 5<A4Q1x s := by dsimp [A4Q1x]; omega
  have hxe : A4Q1x s%2=0 := by dsimp [A4Q1x]; omega
  have hy : 6≤A4Q1y s := by dsimp [A4Q1y]; omega
  have hye : A4Q1y s%2=0 := by dsimp [A4Q1y]; omega
  have hsum : (A4Q1x s+A4Q1y s)%4=2 := by dsimp [A4Q1x,A4Q1y]; omega
  have hDreach := even_even_sum2_reach_forces_direct
    (A4Q1x s) (A4Q1y s) hx hxe hy hye hsum hreach
  have hDx : A4Q1x s+A4Q1y s-2=A4Q1Dx s := by
    dsimp [A4Q1x,A4Q1y,A4Q1Dx]
    omega
  have hDy : (A4Q1y s-2)/2=A4Q1Dy s := by
    dsimp [A4Q1y,A4Q1Dy]
    omega
  have hD : RunReach (A4Q1Dx s) (A4Q1Dy s) := by
    simpa only [hDx,hDy] using hDreach
  have hDfacts :
      5<A4Q1Dx s ∧ A4Q1Dx s%2=0 ∧
      A4Q1Dy s%2=1 ∧ 5≤A4Q1Dy s ∧
      (A4Q1Dx s+A4Q1Dy s)%2=1 ∧
      (A4Q1Dx s+A4Q1Dy s+1)%4=2 := by
    dsimp [A4Q1Dx,A4Q1Dy]
    omega
  obtain ⟨b,l,_,hstep⟩ :=
    BB6.Agent3Root32HighStopA4Core.run_parent_of_left_gt5
      (A4Q1Dx s) (A4Q1Dy s) hDfacts.1 hD
  exact (BB6.Agent3Root32HighStopR10592LCore.no_parent_evenodd_sumplusone_two
    (A4Q1Dx s) (A4Q1Dy s) hDfacts.1 hDfacts.2.1 hDfacts.2.2.1
    hDfacts.2.2.2.1 hDfacts.2.2.2.2.1 hDfacts.2.2.2.2.2) ⟨b,l,hstep⟩

/-- Any A4 visit on t=719+1024*s has a visit to T0(s); the q=1
parent is eliminated by the complete even/even source fan. -/
theorem a4_reach_implies_t0 (s : Nat)
    (hA4 : RunReach
      (BB6.Agent3Root32HighStopA4Core.a4X (719+1024*s))
      (BB6.Agent3Root32HighStopA4Core.a4Y (719+1024*s))) :
    RunReach (T0x s) (T0y s) := by
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent3Root32HighStopA4Core.run_parent_of_left_gt5
      (BB6.Agent3Root32HighStopA4Core.a4X (719+1024*s))
      (BB6.Agent3Root32HighStopA4Core.a4Y (719+1024*s))
      (by dsimp [BB6.Agent3Root32HighStopA4Core.a4X]; omega) hA4
  rcases a4_source_parent_cases s a k hstep with hq0 | hq1
  · rcases hq0 with ⟨ha,hk⟩
    simpa only [ha,hk] using hprev
  · rcases hq1 with ⟨ha,hk⟩
    have hQ1 : RunReach (A4Q1x s) (A4Q1y s) := by
      simpa only [ha,hk] using hprev
    exact False.elim (a4_q1_parent_unreachable s hQ1)

/-- Exact all-depth parent classification for T0(s). Its only possible
parents are P0(s) (depth zero) and P2(s) (depth two). -/
private theorem t0_source_parent_cases (s a k : Nat)
    (hstep : secNext (a,k)=some (T0x s,T0y s)) :
    (a=P0x s ∧ k=P0y s) ∨
    (a=T0Q1x s ∧ k=T0Q1y s) := by
  let x := T0x s
  let y := T0y s
  let W := 106897339845+152186460300*s
  have hx : x%2=0 := by dsimp [x,T0x]; omega
  have hy : y%2=1 := by dsimp [y,T0y]; omega
  have hy5 : 5≤y := by dsimp [y,T0y]; omega
  have hsumOdd : (x+y)%2=1 := by omega
  have hH : x+y+1=32*W := by dsimp [x,y,T0x,T0y,W]; omega
  have hWodd : W%2=1 := by dsimp [W]; omega
  have hWgt : 1<W := by dsimp [W]; omega
  have hHmod64 : (x+y+1)%64=32 := by rw [hH]; omega
  have hp := (section_preimage_all_iff a k x y).mp hstep
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
      · have hcase : 4≤y ∧ ∃ n : Nat,
            x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y := by
          simpa [sectionPreimageAll,ha0,hk0,hk1] using hp
        rcases hcase with ⟨_,n,hpow,_⟩
        have heven : (x+y)%2=0 := by rw [hpow]; simp [Nat.mul_mod]
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp <;> omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp <;> omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp <;> omega
            · have hcase :
                  (y=3 ∧ ∃ n : Nat, x+6=2^n*16 ∧
                    (2*k-3)+16+3*n=x+10) ∨
                  (5≤y ∧ ∃ n : Nat, x+y+1=2^n*16 ∧
                    (2*k-3)+16+3*n=x+2*y+2) := by
                simpa [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] using hp
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have heq : 2^1*W=2^n := by rw [hH] at hpow; omega
                exact False.elim
                  (no_pow2_mul_odd_gt_one 1 W n (by omega) hWodd hWgt heq)
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hlow : 2*k≤a
        · have hcase : x=a-2*k ∧ y=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          rcases hcase with ⟨_,hyy⟩
          omega
        · by_cases haeven : a%2=0
          · have hcase : 4≤y ∧ ∃ n : Nat,
                x+y=2^n*(2*(a-1)+6) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨_,n,hpow,_⟩
            have heven : (x+y)%2=0 := by rw [hpow]; simp [Nat.mul_mod]
            omega
          · have hcase :
                (y=3 ∧ ∃ n : Nat, x+6=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
                (5≤y ∧ ∃ n : Nat,
                  x+y+1=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,hcost⟩
            · omega
            · have hfactor : 2*(a-1)+8=2*a+6 := by omega
              have hsum' : x+y+1=2^n*(2*a+6) := by
                simpa [hfactor] using hpow
              have hcost' : 2*k+a+7+3*n=x+2*y := by
                rw [hfactor] at hcost
                omega
              have hnEven : n%2=0 := by omega
              have hnle : n≤3 := by
                by_cases hn4 : 4≤n
                · have hpowdiv : 2^4∣2^n := Nat.pow_dvd_pow 2 hn4
                  have ha3even : (a+3)%2=0 := by omega
                  have ha3div : 2∣a+3 :=
                    Nat.dvd_iff_mod_eq_zero.mpr ha3even
                  rcases hpowdiv with ⟨p,hp⟩
                  rcases ha3div with ⟨q,hq⟩
                  have hfac : 2*a+6=4*q := by omega
                  have hdiv : 64∣x+y+1 := by
                    refine ⟨p*q,?_⟩
                    calc
                      x+y+1=2^n*(2*a+6) := hsum'
                      _=(2^4*p)*(4*q) := by rw [← hp,hfac]
                      _=64*(p*q) := by norm_num [show (2:Nat)^4=16 by decide]; ring
                  have hzero := Nat.mod_eq_zero_of_dvd hdiv
                  omega
                · omega
              have hdepth : n=0 ∨ n=2 := by omega
              rcases hdepth with hn | hn
              · subst n
                left
                have hP0sum : 2*P0x s+6=x+y+1 := by
                  dsimp [P0x,x,y,T0x,T0y]
                  omega
                have hP0cost : 2*P0y s+P0x s+7=x+2*y := by
                  dsimp [P0x,P0y,x,y,T0x,T0y]
                  omega
                constructor <;> omega
              · subst n
                right
                have hP2sum : 8*(T0Q1x s+3)=x+y+1 := by
                  dsimp [T0Q1x,x,y,T0x,T0y]
                  omega
                have hP2cost : 2*T0Q1y s+T0Q1x s+13=x+2*y := by
                  dsimp [T0Q1x,T0Q1y,x,y,T0x,T0y]
                  omega
                constructor <;> omega

/-- T0 reachability forces P0 or P2; P2 is excluded, while P0 has
the unique six-even-right predecessor R0. -/
theorem t0_reach_implies_r0 (s : Nat)
    (hT0 : RunReach (T0x s) (T0y s)) :
    RunReach (R0x s) (R0y s) := by
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent3Root32HighStopA4Core.run_parent_of_left_gt5
      (T0x s) (T0y s) (by dsimp [T0x]; omega) hT0
  rcases t0_source_parent_cases s a k hstep with hP0 | hP2
  · rcases hP0 with ⟨ha,hk⟩
    have hP0reach : RunReach (P0x s) (P0y s) := by
      simpa only [ha,hk] using hprev
    have hfacts :
        6≤P0y s ∧ P0y s%2=0 ∧
        (P0x s+P0y s)%8≠0 ∧ (P0x s+P0y s)%8≠7 := by
      dsimp [P0x,P0y]
      omega
    have hP0C : BB6.Agent3.CReach (P0x s) (P0y s) := by
      simpa [RunReach,BB6.Agent3Root32HighStopA4Core.RunReach,
        BB6.Agent3.CReach] using hP0reach
    have hR0C := (BB6.Agent46.six_even_right_blank_reach_iff
      (P0x s) (P0y s) hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2).mp hP0C
    have hR0 : RunReach (R0x s) (R0y s) := by
      have hRx : P0x s+P0y s-2=R0x s := by
        dsimp [P0x,P0y,R0x]
        omega
      have hRy : (P0y s-2)/2=R0y s := by
        dsimp [P0y,R0y]
        omega
      simpa [RunReach,BB6.Agent3Root32HighStopA4Core.RunReach,
        BB6.Agent3.CReach,hRx,hRy] using hR0C
    exact hR0
  · rcases hP2 with ⟨ha,hk⟩
    have hP2reach : RunReach (T0Q1x s) (T0Q1y s) := by
      simpa only [ha,hk] using hprev
    have hfacts :
        5<T0Q1x s ∧ 5≤T0Q1y s ∧ T0Q1y s%2=1 ∧
        (T0Q1x s+T0Q1y s)%4=2 := by
      dsimp [T0Q1x,T0Q1y]
      omega
    exact False.elim
      (BB6.Agent3Root32HighStopA4Core.run_no_odd_sum_two
        (T0Q1x s) (T0Q1y s) hfacts.1 hfacts.2.1 hfacts.2.2.1
        hfacts.2.2.2 hP2reach)

/-- The exact R0(8*m) sum-seven inverse forces the R1 target. -/
theorem r0_eight_unreachable (m : Nat) :
    ¬ RunReach (R0x (8*m)) (R0y (8*m)) := by
  intro hR0
  have hR0facts :
      R0x (8*m)%2=1 ∧ R0y (8*m)%8=6 ∧
      (R0x (8*m)+R0y (8*m)+1)%32=16 ∧
      48≤R0x (8*m)+R0y (8*m)+1 := by
    dsimp [R0x,R0y]
    omega
  have hR0C : BB6.Agent3.CReach (R0x (8*m)) (R0y (8*m)) := by
    simpa [RunReach,BB6.Agent3Root32HighStopA4Core.RunReach,
      BB6.Agent3.CReach] using hR0
  have hR1C := (BB6.Agent19Seven.sumseven_forced_root_iff
    (R0x (8*m)) (R0y (8*m))
    hR0facts.1 hR0facts.2.1 hR0facts.2.2.1 hR0facts.2.2.2).mp hR0C
  have hR1 : RunReach (R1x m) (R1y m) := by
    have hRx : R0x (8*m)+R0y (8*m)-2=R1x m := by
      dsimp [R0x,R0y,R1x]
      omega
    have hRy : (R0y (8*m)-2)/2=R1y m := by
      dsimp [R0y,R1y]
      omega
    simpa [RunReach,BB6.Agent3Root32HighStopA4Core.RunReach,
      BB6.Agent3.CReach,hRx,hRy] using hR1C
  have hR1facts :
      R1x m%2=1 ∧ R1y m%2=0 ∧
      (R1x m+R1y m+1)%16=8 ∧ 64≤R1y m := by
    dsimp [R1x,R1y]
    omega
  have hsplit := (BB6.Agent3.mod16_seven_blank_reach_iff
    (R1x m) (R1y m) hR1facts.1 hR1facts.2.1
    hR1facts.2.2.1 hR1facts.2.2.2).mp
    (by simpa [RunReach,BB6.Agent3Root32HighStopA4Core.RunReach,
      BB6.Agent3.CReach] using hR1)
  rcases hsplit with hD | hB
  · have hDfacts :
        5<D1x m ∧ 6≤D1y m ∧ D1y m%2=0 ∧
        (D1x m+D1y m)%8≠0 ∧ (D1x m+D1y m)%8≠7 := by
      dsimp [D1x,D1y]
      omega
    have hDreach : RunReach (D1x m) (D1y m) := by
      have hDx : R1x m+R1y m-2=D1x m := by
        dsimp [R1x,R1y,D1x]
        omega
      have hDy : (R1y m-2)/2=D1y m := by
        dsimp [R1y,D1y]
        omega
      simpa [RunReach,BB6.Agent3Root32HighStopA4Core.RunReach,
        BB6.Agent3.CReach,hDx,hDy] using hD
    have hE_C := (BB6.Agent46.six_even_right_blank_reach_iff
      (D1x m) (D1y m) hDfacts.2.1 hDfacts.2.2.1
      hDfacts.2.2.2.1 hDfacts.2.2.2.2).mp
      (by simpa [RunReach,BB6.Agent3Root32HighStopA4Core.RunReach,
        BB6.Agent3.CReach] using hDreach)
    have hEreach : RunReach (E1x m) (E1y m) := by
      have hEx : D1x m+D1y m-2=E1x m := by
        dsimp [D1x,D1y,E1x]
        omega
      have hEy : (D1y m-2)/2=E1y m := by
        dsimp [D1y,E1y]
        omega
      simpa [RunReach,BB6.Agent3Root32HighStopA4Core.RunReach,
        BB6.Agent3.CReach,hEx,hEy] using hE_C
    have hEfacts :
        E1x m%2=1 ∧ E1y m%2=1 ∧ 5≤E1y m ∧
        (E1x m+E1y m)%4=0 ∧
        (E1x m+E1y m)%16≠0 ∧ 24≤E1x m+E1y m := by
      dsimp [E1x,E1y]
      omega
    have hF_C := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (E1x m) (E1y m) hEfacts.1 hEfacts.2.1 hEfacts.2.2.1
      hEfacts.2.2.2.1 hEfacts.2.2.2.2.1 hEfacts.2.2.2.2.2).mp
      (by simpa [RunReach,BB6.Agent3Root32HighStopA4Core.RunReach,
        BB6.Agent3.CReach] using hEreach)
    have hFreach : RunReach (F1x m) (F1y m) := by
      have hFx : (E1x m+E1y m-4)/2=F1x m := by
        dsimp [E1x,E1y,F1x]
        omega
      have hFy : (E1x m+3*E1y m-10)/4=F1y m := by
        dsimp [E1x,E1y,F1y]
        omega
      simpa [RunReach,BB6.Agent3Root32HighStopA4Core.RunReach,
        BB6.Agent3.CReach,hFx,hFy] using hF_C
    have hFfacts :
        5<F1x m ∧ 5≤F1y m ∧ F1y m%2=1 ∧
        (F1x m+F1y m)%4=1 := by
      dsimp [F1x,F1y]
      omega
    exact (BB6.Agent3Root32HighStopA4Core.run_no_odd_sum_one
      (F1x m) (F1y m) hFfacts.1 hFfacts.2.1 hFfacts.2.2.1
      hFfacts.2.2.2) hFreach
  · have hBfacts :
        5<B1x m ∧ 6≤B1y m ∧ B1x m%2=1 ∧
        B1y m%2=0 ∧ (B1x m+B1y m)%8=3 := by
      dsimp [B1x,B1y]
      omega
    have hBx :
        (R1x m+R1y m+1)/4-3=B1x m := by
      dsimp [R1x,R1y,B1x]
      omega
    have hBy :
        (R1x m+2*R1y m-((R1x m+R1y m+1)/4-3)-10)/2=B1y m := by
      dsimp [R1x,R1y,B1x,B1y]
      omega
    have hBreach : RunReach (B1x m) (B1y m) := by
      simpa [RunReach,BB6.Agent3Root32HighStopA4Core.RunReach,
        BB6.Agent3.CReach,hBx,hBy] using hB
    obtain ⟨a,k,hprev,hstep⟩ :=
      BB6.Agent3Root32HighStopA4Core.run_parent_of_left_gt5
        (B1x m) (B1y m) hBfacts.1 hBreach
    have hAffine := BB6.Agent46.section_odd_even_iff_affine
      a k (B1x m) (B1y m) hBfacts.2.2.1 hBfacts.2.2.2.1
      hBfacts.2.1 hBfacts.2.2.2.2
    obtain ⟨ha,hk⟩ := hAffine.mp hstep
    have hGreach : RunReach (G1x m) (G1y m) := by
      have hGx : B1x m+B1y m-2=G1x m := by
        dsimp [B1x,B1y,G1x]
        omega
      have hGy : (B1y m-2)/2=G1y m := by
        dsimp [B1y,G1y]
        omega
      simpa only [ha,hk,hGx,hGy] using hprev
    have hGfacts :
        5<G1x m ∧ 5≤G1y m ∧ G1y m%2=1 ∧
        (G1x m+G1y m)%4=2 := by
      dsimp [G1x,G1y]
      omega
    exact (BB6.Agent3Root32HighStopA4Core.run_no_odd_sum_two
      (G1x m) (G1y m) hGfacts.1 hGfacts.2.1 hGfacts.2.2.1
      hGfacts.2.2.2) hGreach

/-- The corrected P7E1E residual is unreachable for t=719+8192*m. -/
theorem p7e1e_unreachable_t719_s8 (m : Nat) :
    ¬ RunReach
      (BB6.Agent3Root32HighStopA4Core.p7e1eX (719+8192*m))
      (BB6.Agent3Root32HighStopA4Core.p7e1eY (719+8192*m)) := by
  intro hP7
  have ht8 : (719+8192*m)%8=7 := by omega
  have hP7Integrated :
      BB6.Agent3Root32HighStopIntegrated.RunReach
        (BB6.Agent3Root32HighStopA4Core.p7e1eX (719+8192*m))
        (BB6.Agent3Root32HighStopA4Core.p7e1eY (719+8192*m)) := by
    simpa [RunReach,BB6.Agent3Root32HighStopA4Core.RunReach,
      BB6.Agent3Root32HighStopIntegrated.RunReach] using hP7
  have hA4Integrated :=
    BB6.Agent3Root32P7E1EGenericA4.p7e1e_reach_implies_a4_t7
      (719+8192*m) ht8 hP7Integrated
  have hA4 : RunReach
      (BB6.Agent3Root32HighStopA4Core.a4X (719+8192*m))
      (BB6.Agent3Root32HighStopA4Core.a4Y (719+8192*m)) := by
    simpa [RunReach,BB6.Agent3Root32HighStopA4Core.RunReach,
      BB6.Agent3Root32HighStopIntegrated.RunReach] using hA4Integrated
  have hT0 := a4_reach_implies_t0 (8*m) (by
    simpa only [show 719+1024*(8*m)=719+8192*m by omega] using hA4)
  have hR0 := t0_reach_implies_r0 (8*m) hT0
  exact r0_eight_unreachable m hR0

#print axioms a4_source_parent_cases
#print axioms a4_q1_parent_unreachable
#print axioms a4_reach_implies_t0
#print axioms t0_source_parent_cases
#print axioms t0_reach_implies_r0
#print axioms r0_eight_unreachable
#print axioms p7e1e_unreachable_t719_s8

end BB6.Agent6A4T719Q0EvenS8
