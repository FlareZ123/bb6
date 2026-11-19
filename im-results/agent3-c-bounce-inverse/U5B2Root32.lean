import SectionAllInverse
import EvenEvenParentFan
import M0EvenEvenSumZero
import HighSumTwo
import OddEvenUnique
import EvenRightUnique
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3U5B2Root32
open BB6.Agent46

/-- The powers of two cycle as 1,2 modulo three. -/
private theorem pow_two_mod_three (n : Nat) :
    2^n%3 = if n%2=0 then 1 else 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ,Nat.mul_mod]
      have htwo : (2:Nat)%3=2 := by decide
      rw [htwo]
      by_cases he : n%2=0
      · have hval : 2^n%3=1 := by simpa [he] using ih
        have hs : (Nat.succ n)%2=1 := by omega
        simp [hval,hs]
      · have hn : n%2=1 := by omega
        have hval : 2^n%3=2 := by simpa [hn] using ih
        have hs : (Nat.succ n)%2=0 := by omega
        simp [hval,hs]

/-- Every odd/odd target of sum divisible by three has only an even-a,
even-depth bounce predecessor in the complete original-section grammar. -/
theorem odd_odd_three_divisible_parent (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (h3 : (x+y)%3=0)
    (hsec : secNext (a,k)=some (x,y)) :
    ∃ n : Nat, a%2=0 ∧ n%2=0 ∧
      x+y=2^n*(2*a+4) ∧ 2*k+a+7+3*n=x+2*y := by
  have hp := (section_preimage_all_iff a k x y).mp hsec
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp <;> omega
      · have hcase : 4≤y ∧ ∃ n : Nat,
            x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y := by
          simpa [sectionPreimageAll,ha0,hk0,hk1] using hp
        rcases hcase with ⟨_,n,hxy,_⟩
        have hpow := pow_two_mod_three n
        have hpowCases : 2^n%3=1 ∨ 2^n%3=2 := by
          by_cases he : n%2=0
          · left
            simpa [he] using hpow
          · right
            have hn : n%2=1 := by omega
            simpa [hn] using hpow
        have hprod : (2^n*8)%3≠0 := by
          rw [Nat.mul_mod]
          have h8 : (8:Nat)%3=2 := by decide
          rw [h8]
          rcases hpowCases with h|h
          · rw [h]
            decide
          · rw [h]
            decide
        rw [hxy] at h3
        exact hprod h3
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
                  (y=3 ∧ ∃ n : Nat, x+6=2^n*16 ∧
                    (2*k-3)+16+3*n=x+10) ∨
                  (5≤y ∧ ∃ n : Nat, x+y+1=2^n*16 ∧
                    (2*k-3)+16+3*n=x+2*y+2) := by
                simpa [sectionPreimageAll,hk0,hk1,hk2,hk3] using hp
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hodd : (x+y+1)%2=1 := by omega
                have heven : (2^n*16)%2=0 := by simp [Nat.mul_mod]
                rw [hpow] at hodd
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hlow : 2*k≤a
        · have hcase : x=a-2*k ∧ y=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          rcases hcase with ⟨hxx,hyy⟩
          omega
        · by_cases haeven : a%2=0
          · have hcase : 4≤y ∧ ∃ n : Nat,
                x+y=2^n*(2*(a-1)+6) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨_,n,hxy,hcost⟩
            have hfac : 2*(a-1)+6=2*a+4 := by omega
            have hsum : x+y=2^n*(2*a+4) := by
              rw [hfac] at hxy
              exact hxy
            have hcost' : 2*k+a+7+3*n=x+2*y := by omega
            have hn : n%2=0 := by omega
            exact ⟨n,haeven,hn,hsum,hcost'⟩
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
              have heven :
                  (2^n*(2*(a-1)+8))%2=0 := by
                simp [Nat.mul_mod]
              rw [hpow] at hodd
              omega

/-- Every even/odd target of sum divisible by three has only an
odd-a, even-depth high-bounce predecessor in the complete source grammar. -/
theorem even_odd_three_divisible_parent (a k x y : Nat)
    (hx : x%2=0) (hy : y%2=1) (hy5 : 5≤y)
    (h3 : (x+y)%3=0)
    (hsec : secNext (a,k)=some (x,y)) :
    ∃ n : Nat, a%2=1 ∧ n%2=0 ∧
      x+y+1=2^n*(2*a+6) ∧ 2*k+a+7+3*n=x+2*y := by
  have hp := (section_preimage_all_iff a k x y).mp hsec
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp <;> omega
      · have hcase : 4≤y ∧ ∃ n : Nat,
            x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y := by
          simpa [sectionPreimageAll,ha0,hk0,hk1] using hp
        rcases hcase with ⟨_,n,hxy,_⟩
        have hsumOdd : (x+y)%2=1 := by omega
        have hsumEven : (x+y)%2=0 := by
          rw [hxy]
          simp [Nat.mul_mod]
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
                  (y=3 ∧ ∃ n : Nat, x+6=2^n*16 ∧
                    (2*k-3)+16+3*n=x+10) ∨
                  (5≤y ∧ ∃ n : Nat, x+y+1=2^n*16 ∧
                    (2*k-3)+16+3*n=x+2*y+2) := by
                simpa [sectionPreimageAll,hk0,hk1,hk2,hk3] using hp
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,hcost⟩
              · omega
              · have hnodd : n%2=1 := by omega
                have hpowCycle := pow_two_mod_three n
                have hpowmod : 2^n%3=2 := by
                  simpa [hnodd] using hpowCycle
                have hleft : (x+y+1)%3=1 := by omega
                have hright : (2^n*16)%3=2 := by
                  rw [Nat.mul_mod]
                  have h16 : (16:Nat)%3=1 := by decide
                  rw [h16,hpowmod]
                  decide
                rw [hpow] at hleft
                rw [hright] at hleft
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hlow : 2*k≤a
        · have hcase : x=a-2*k ∧ y=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          rcases hcase with ⟨hxx,hyy⟩
          omega
        · by_cases haeven : a%2=0
          · have hcase : 4≤y ∧ ∃ n : Nat,
                x+y=2^n*(2*(a-1)+6) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨_,n,hxy,_⟩
            have hsumOdd : (x+y)%2=1 := by omega
            have hsumEven : (x+y)%2=0 := by
              rw [hxy]
              simp [Nat.mul_mod]
            omega
          · have haodd : a%2=1 := by omega
            have hcase :
                (y=3 ∧ ∃ n : Nat, x+6=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
                (5≤y ∧ ∃ n : Nat,
                  x+y+1=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,hcost⟩
            · omega
            · have hfac : 2*(a-1)+8=2*a+6 := by omega
              rw [hfac] at hpow
              have hcost' : 2*k+a+7+3*n=x+2*y := by omega
              have hn : n%2=0 := by omega
              exact ⟨n,haodd,hn,hpow,hcost'⟩

/-- An even/odd target with sum divisible by three and sum-plus-one
congruent to two modulo four has no genuine blank-rooted visit. -/
theorem blank_no_even_odd_three_divisible (x y : Nat)
    (hxgt : 5<x) (hx : x%2=0) (hy : y%2=1) (hy5 : 5≤y)
    (h3 : (x+y)%3=0) (hbad : (x+y+1)%4=2) :
    ¬ BB6.Agent3.CReach x y := by
  intro hr
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      x y hxgt hr
  obtain ⟨n,ha,hn,hpow,hcost⟩ :=
    even_odd_three_divisible_parent a k x y hx hy hy5 h3 hstep
  have hfac : (2*a+6)%4=0 := by omega
  have hmod : (x+y+1)%4=0 := by
    rw [hpow,Nat.mul_mod,hfac]
    simp
  omega

/-- Complete source-parent reduction for the B2 family when u is even:
only the two displayed odd-a high-bounce parents survive. -/
theorem b2_even_parent_fan (u a k : Nat) (hu : u%2=0)
    (hsec : secNext (a,k)=some (734+10944*u,34881+518816*u)) :
    (a=17805+264880*u ∧ k=26342+391848*u) ∨
    (a=4449+66220*u ∧ k=33017+491178*u) := by
  let x := 734+10944*u
  let y := 34881+518816*u
  let W := 1113+16555*u
  have hx : x%2=0 := by dsimp [x]; omega
  have hy : y%2=1 := by dsimp [y]; omega
  have hy5 : 5≤y := by dsimp [y]; omega
  have hxyOdd : (x+y)%2=1 := by omega
  have hA : x+y+1=32*W := by dsimp [x,y,W]; omega
  have hWodd : W%2=1 := by dsimp [W]; omega
  have hWgt : 1113≤W := by dsimp [W]; omega
  have hAmod64 : (x+y+1)%64=32 := by
    rw [hA]
    omega
  have hp := (section_preimage_all_iff a k x y).mp hsec
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp <;> omega
      · have hcase : 4≤y ∧ ∃ n : Nat,
            x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y := by
          simpa [sectionPreimageAll,ha0,hk0,hk1] using hp
        rcases hcase with ⟨_,n,hxy,_⟩
        have hsumEven : (x+y)%2=0 := by
          rw [hxy]
          simp [Nat.mul_mod]
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
                  (y=3 ∧ ∃ n : Nat, x+6=2^n*16 ∧
                    (2*k-3)+16+3*n=x+10) ∨
                  (5≤y ∧ ∃ n : Nat, x+y+1=2^n*16 ∧
                    (2*k-3)+16+3*n=x+2*y+2) := by
                simpa [sectionPreimageAll,hk0,hk1,hk2,hk3] using hp
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · by_cases hn0 : n=0
                · rw [hn0] at hpow
                  have hmod : (2^0*16:Nat)%64=16 := by decide
                  rw [hpow] at hAmod64
                  rw [hmod] at hAmod64
                  omega
                · by_cases hn1 : n=1
                  · have hEq : 32*W=2^n*16 := by
                      calc
                        32*W = x+y+1 := hA.symm
                        _ = 2^n*16 := hpow
                    rw [hn1] at hEq
                    simp at hEq
                    omega
                  · have hn2 : 2≤n := by omega
                    have h4 : 4∣2^n := by
                      have h := Nat.pow_dvd_pow 2 hn2
                      simpa only [show (2:Nat)^2=4 by decide] using h
                    rcases h4 with ⟨q,hq⟩
                    have h64 : 64∣2^n*16 := by
                      refine ⟨q,?_⟩
                      rw [hq]
                      ac_rfl
                    have h64A : 64∣x+y+1 := by
                      rw [hpow]
                      exact h64
                    have hmod := Nat.mod_eq_zero_of_dvd h64A
                    omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hlow : 2*k≤a
        · have hcase : x=a-2*k ∧ y=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          rcases hcase with ⟨hxx,hyy⟩
          omega
        · by_cases haeven : a%2=0
          · have hcase : 4≤y ∧ ∃ n : Nat,
                x+y=2^n*(2*(a-1)+6) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨_,n,hxy,_⟩
            have hsumEven : (x+y)%2=0 := by
              rw [hxy]
              simp [Nat.mul_mod]
            omega
          · have haodd : a%2=1 := by omega
            have hcase :
                (y=3 ∧ ∃ n : Nat, x+6=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
                (5≤y ∧ ∃ n : Nat,
                  x+y+1=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,hcost⟩
            · omega
            · have hfac : 2*(a-1)+8=2*a+6 := by omega
              rw [hfac] at hpow
              have hfactor4 : 4∣2*a+6 := by
                refine ⟨a/2+2,?_⟩
                omega
              have hpoweq : 2^(n+2)=2^n*4 := by
                rw [Nat.pow_add]
                simp
              have hpowdiv : 2^(n+2)∣x+y+1 := by
                rcases hfactor4 with ⟨q,hq⟩
                refine ⟨q,?_⟩
                rw [hpow,hpoweq,hq]
                ac_rfl
              have hnlt : n<4 := by
                by_contra hnot
                have hnge : 4≤n := by omega
                have h6pow : 2^6∣2^(n+2) :=
                  Nat.pow_dvd_pow 2 (by omega)
                have h64 : 64∣x+y+1 := by
                  have h := Nat.dvd_trans h6pow hpowdiv
                  simpa only [show (2:Nat)^6=64 by decide] using h
                have hmod := Nat.mod_eq_zero_of_dvd h64
                omega
              have hcost' : 2*k+a+7+3*n=x+2*y := by omega
              have hnEven : n%2=0 := by omega
              have hncase : n=0 ∨ n=2 := by omega
              rcases hncase with hn0|hn2
              · have hpow0 : x+y+1=2*a+6 := by
                  simpa [hn0] using hpow
                have hEq : 32*W=2*a+6 := by omega
                have ha' : a=17805+264880*u := by
                  dsimp [W] at hEq
                  omega
                have hk' : k=26342+391848*u := by
                  rw [hn0,ha'] at hcost'
                  dsimp [x,y] at hcost'
                  omega
                left
                exact ⟨ha',hk'⟩
              · have hpow2 : x+y+1=4*(2*a+6) := by
                  simpa [hn2] using hpow
                have hEq : 32*W=4*(2*a+6) := by omega
                have ha' : a=4449+66220*u := by
                  dsimp [W] at hEq
                  omega
                have hk' : k=33017+491178*u := by
                  rw [hn2,ha'] at hcost'
                  dsimp [x,y] at hcost'
                  omega
                right
                exact ⟨ha',hk'⟩

/-- A forced odd/even inverse edge transports genuine blank reachability. -/
private theorem cReach_odd_even_parent
    (x y : Nat) (hxgt : 5<x)
    (hx : x%2=1) (hy : y%2=0) (hy6 : 6≤y)
    (hs : (x+y)%8=3)
    (hr : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 x y hxgt hr
  obtain ⟨ha,hk⟩ :=
    (BB6.Agent46.section_odd_even_iff_affine a k x y hx hy hy6 hs).mp hstep
  simpa only [ha,hk] using hprev

/-- The n=0 P4 parent is excluded by the even/even complete fan:
its only possible source parent is an odd-right sum-one state. -/
theorem p4_r32_n0_parent_unreachable (t : Nat) :
    ¬ BB6.Agent3.CReach
      (900668686+3358639200*t) (494467868+1843895760*t) := by
  let x := 900668686+3358639200*t
  let y := 494467868+1843895760*t
  intro hr
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      x y (by dsimp [x]; omega) hr
  have hfan := BB6.Agent3ParentFan.even_even_parent_fan
    a k x y (by dsimp [x]; omega) (by dsimp [x]; omega)
    (by dsimp [y]; omega) (by dsimp [y]; omega) hstep
  have hsum : (x+y)%4=2 := by dsimp [x,y]; omega
  rcases hfan with hdirect | hzero | hbounce
  · rcases hdirect with ⟨ha,hk⟩
    have haD : a=1395136552+5202534960*t := by
      rw [ha]
      dsimp [x,y]
      omega
    have hkD : k=247233933+921947880*t := by
      rw [hk]
      dsimp [y]
      omega
    have hD : BB6.Agent3.CReach
        (1395136552+5202534960*t) (247233933+921947880*t) := by
      simpa only [haD,hkD] using hprev
    have hDsum :
        ((1395136552+5202534960*t)+(247233933+921947880*t))%4=1 := by
      omega
    exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (1395136552+5202534960*t) (247233933+921947880*t)
      (by omega) (by omega) (by omega) hDsum hD
  · rcases hzero with ⟨_,_,n,hxy,_⟩
    have hdiv : 4∣x+y := by
      refine ⟨2^n*2,?_⟩
      rw [hxy]
      ac_rfl
    have hmod := Nat.mod_eq_zero_of_dvd hdiv
    omega
  · rcases hbounce with ⟨_,_,_,_,n,hn,hxy,_⟩
    have h4pow : 4∣2^(n+1) := by
      have h := Nat.pow_dvd_pow 2 (by omega)
      simpa only [show (2:Nat)^2=4 by decide] using h
    have hdiv : 4∣x+y := by
      rcases h4pow with ⟨q,hq⟩
      refine ⟨q*(a+2),?_⟩
      rw [hxy,hq]
      ac_rfl
    have hmod := Nat.mod_eq_zero_of_dvd hdiv
    omega

/-- The n=2 P4 parent has no source predecessor: every such predecessor
would force its sum-plus-one to be divisible by four, but it is 2 mod 4. -/
theorem p4_r32_n2_parent_unreachable (t : Nat) :
    ¬ BB6.Agent3.CReach
      (225167170+839659800*t) (832218623+3103385460*t) := by
  exact blank_no_even_odd_three_divisible
    (225167170+839659800*t) (832218623+3103385460*t)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Exact source-parent fan for the remaining P4 target on the root-index
r=32 (mod 64) cylinder has only depths n=0 and n=2. -/
theorem p4_r32_parent_fan (t a k : Nat)
    (hsec : secNext (a,k)=some
      (63895+950614*(1802+6720*t),3291+48981*(1802+6720*t))) :
    (a=900668686+3358639200*t ∧ k=494467868+1843895760*t) ∨
    (a=225167170+839659800*t ∧ k=832218623+3103385460*t) := by
  let u := 1802+6720*t
  let x := 63895+950614*u
  let y := 3291+48981*u
  have hx : x%2=1 := by dsimp [x]; omega
  have hy : y%2=1 := by dsimp [y]; omega
  have hy5 : 5≤y := by dsimp [y]; omega
  have h3 : (x+y)%3=0 := by dsimp [x,y,u]; omega
  have hSmod64 : (x+y)%64=32 := by dsimp [x,y,u]; omega
  have hparent :=
    odd_odd_three_divisible_parent a k x y hx hy hy5 h3 hsec
  rcases hparent with ⟨n,haeven,hn,hpow,hcost⟩
  have hfactor4 : 4∣2*a+4 := by
    refine ⟨a/2+1,?_⟩
    omega
  have hpoweq : 2^(n+2)=2^n*4 := by
    rw [Nat.pow_add]
    simp
  have hpowdiv : 2^(n+2)∣x+y := by
    rcases hfactor4 with ⟨q,hq⟩
    refine ⟨q,?_⟩
    rw [hpow,hpoweq,hq]
    ac_rfl
  have hnlt : n<4 := by
    by_contra hnot
    have hnge : 4≤n := by omega
    have h6pow : 2^6∣2^(n+2) := Nat.pow_dvd_pow 2 (by omega)
    have h64 : 64∣x+y := by
      have h := Nat.dvd_trans h6pow hpowdiv
      simpa only [show (2:Nat)^6=64 by decide] using h
    have hmod := Nat.mod_eq_zero_of_dvd h64
    omega
  have hncase : n=0 ∨ n=2 := by omega
  rcases hncase with hn0|hn2
  · have hpow0 : x+y=2*a+4 := by simpa [hn0] using hpow
    have hEq : 32*(56291793+209914950*t)=2*a+4 := by
      have hS : x+y=32*(56291793+209914950*t) := by
        dsimp [x,y,u]
        omega
      omega
    have ha' : a=900668686+3358639200*t := by omega
    have hcost' : 2*k+a+7=x+2*y := by
      rw [hn0] at hcost
      omega
    have hk' : k=494467868+1843895760*t := by
      rw [ha'] at hcost'
      dsimp [x,y,u] at hcost'
      omega
    left
    exact ⟨ha',hk'⟩
  · have hpow2 : x+y=4*(2*a+4) := by simpa [hn2] using hpow
    have hS : x+y=32*(56291793+209914950*t) := by
      dsimp [x,y,u]
      omega
    have hEq : 32*(56291793+209914950*t)=4*(2*a+4) := by omega
    have ha' : a=225167170+839659800*t := by omega
    have hcost' : 2*k+a+13=x+2*y := by
      rw [hn2] at hcost
      omega
    have hk' : k=832218623+3103385460*t := by
      rw [ha'] at hcost'
      dsimp [x,y,u] at hcost'
      omega
    right
    exact ⟨ha',hk'⟩

/-- The P4 family for u=1802+6720t is absent from the genuine blank
section orbit: its only possible parents are the two excluded families. -/
theorem blank_no_p4_root32 (t : Nat) :
    ¬ BB6.Agent3.CReach
      (63895+950614*(1802+6720*t))
      (3291+48981*(1802+6720*t)) := by
  intro hr
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (63895+950614*(1802+6720*t))
      (3291+48981*(1802+6720*t)) (by omega) hr
  rcases p4_r32_parent_fan t a k hstep with hP0|hP2
  · have hP0reach : BB6.Agent3.CReach
        (900668686+3358639200*t) (494467868+1843895760*t) := by
      simpa only [hP0.1,hP0.2] using hprev
    exact p4_r32_n0_parent_unreachable t hP0reach
  · have hP2reach : BB6.Agent3.CReach
        (225167170+839659800*t) (832218623+3103385460*t) := by
      simpa only [hP2.1,hP2.2] using hprev
    exact p4_r32_n2_parent_unreachable t hP2reach

/-- The B2 family corresponding to root indices 32 modulo 64 is absent
from the genuine blank section orbit. This composes the complete B2
source-parent fan, two forced odd/even inverses, the even-right inverse,
and the exact P4 root-stratum closure. -/
theorem blank_no_b2_root32 (t : Nat) :
    ¬ BB6.Agent3.CReach
      (734+10944*(1802+6720*t))
      (34881+518816*(1802+6720*t)) := by
  let u := 1802+6720*t
  let x := 734+10944*u
  let y := 34881+518816*u
  have huEven : u%2=0 := by dsimp [u]; omega
  have hu8 : u%8=2 := by dsimp [u]; omega
  intro hr
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      x y (by dsimp [x,y,u]; omega) hr
  rcases b2_even_parent_fan u a k huEven hstep with hP0|hP1
  · have hP0reach : BB6.Agent3.CReach
        (17805+264880*u) (26342+391848*u) := by
      simpa only [hP0.1,hP0.2] using hprev
    have hP2reach : BB6.Agent3.CReach
        (44145+656728*u) (13170+195924*u) := by
      have h := cReach_odd_even_parent
        (17805+264880*u) (26342+391848*u)
        (by omega) (by omega) (by omega) (by omega) (by omega) hP0reach
      have hxEq :
          (17805+264880*u)+(26342+391848*u)-2 =
            44145+656728*u := by omega
      have hyEq :
          ((26342+391848*u)-2)/2=13170+195924*u := by omega
      simpa only [hxEq,hyEq] using h
    have hP3reach : BB6.Agent3.CReach
        (57313+852652*u) (6584+97962*u) := by
      have h := cReach_odd_even_parent
        (44145+656728*u) (13170+195924*u)
        (by omega) (by omega) (by omega) (by omega) (by omega) hP2reach
      have hxEq :
          (44145+656728*u)+(13170+195924*u)-2 =
            57313+852652*u := by omega
      have hyEq :
          ((13170+195924*u)-2)/2=6584+97962*u := by omega
      simpa only [hxEq,hyEq] using h
    have hP3run :
        ∃ time : Nat,
          BB6.Agent8Section.run secNext time (some (5,1)) =
            some (57313+852652*u,6584+97962*u) := by
      simpa [BB6.Agent3.CReach] using hP3reach
    have hP4run :=
      (BB6.Agent15.blank_reach_iff_even_right
        (57313+852652*u) (6584+97962*u)
        (by omega) (by omega) (by omega) (by omega)).mp hP3run
    have hP4reach : BB6.Agent3.CReach
        (63895+950614*u) (3291+48981*u) := by
      have hxEq :
          (57313+852652*u)+(6584+97962*u)-2 =
            63895+950614*u := by omega
      have hyEq :
          ((6584+97962*u)-2)/2=3291+48981*u := by omega
      simpa [BB6.Agent3.CReach,hxEq,hyEq] using hP4run
    exact (blank_no_p4_root32 t) (by simpa [u] using hP4reach)
  · have hP1reach : BB6.Agent3.CReach
        (4449+66220*u) (33017+491178*u) := by
      simpa only [hP1.1,hP1.2] using hprev
    have hsum :
        ((4449+66220*u)+(33017+491178*u))%4=2 := by
      omega
    exact BB6.Agent11High.blank_no_odd_sum_two
      (4449+66220*u) (33017+491178*u)
      (by omega) (by omega) hsum hP1reach

#print axioms odd_odd_three_divisible_parent
#print axioms even_odd_three_divisible_parent
#print axioms blank_no_even_odd_three_divisible
#print axioms b2_even_parent_fan
#print axioms p4_r32_parent_fan
#print axioms blank_no_p4_root32
#print axioms blank_no_b2_root32

/-- If the P4 coordinate sum in the residual parameterization
u=122+840*w has exact 2-adic valuation five, then w=2 mod 8 and
u=1802+6720*t. This is the arithmetic bridge from the root32
valuation stratum to the cylinder closed above. -/
theorem p4_root32_u_parameter (w : Nat)
    (hS : (67186+999595*(122+840*w))%64=32) :
    ∃ t : Nat, 122+840*w=1802+6720*t := by
  have hfactor :
      67186+999595*(122+840*w)=8*(15252222+104957475*w) := by omega
  have hQ : (15252222+104957475*w)%8=4 := by
    rw [hfactor] at hS
    omega
  have hw : w%8=2 := by omega
  refine ⟨w/8,?_⟩
  omega

/-- The exact residual root equation transfers r=32 mod 64 to
v2(P4.x+P4.y)=5. The hypothesis is the rearranged integer identity
from the B2 residual reduction; E>=19 is more than enough for its
power-of-two term to vanish modulo 64. -/
theorem p4_sum_mod64_of_root32 (r E u : Nat)
    (hr : r%64=32) (hE : 19≤E)
    (hExact :
      211*(67186+999595*u)+7*(2570932352+3163718175*r)
        =19991900*2^(E-13)) :
    (67186+999595*u)%64=32 := by
  have hA : (2570932352+3163718175*r)%64=32 := by omega
  have hpow : (2^(E-13))%64=0 := by
    have hdiv : 64∣2^(E-13) := by
      have h := Nat.pow_dvd_pow 2 (by omega)
      simpa only [show (2:Nat)^6=64 by decide] using h
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hsum :
      (211*(67186+999595*u)+7*(2570932352+3163718175*r))%64=0 := by
    rw [hExact,Nat.mul_mod,hpow]
    simp
  omega

/-- Algebraic conversion of the exact residual root equation to
the P4-sum identity. -/
theorem p4_exact_residual_identity (r E u : Nat)
    (hRoot : 18018+211*u+22155*r=20*2^(E-13)) :
    211*(67186+999595*u)+7*(2570932352+3163718175*r)
      =19991900*2^(E-13) := by
  have hAlg :
      211*(67186+999595*u)+7*(2570932352+3163718175*r)
        =999595*(18018+211*u+22155*r) := by omega
  rw [hRoot] at hAlg
  omega

/-- Root32 valuation cylinder exclusion in the original w parameter. -/
theorem blank_no_b2_root32_from_p4_sum (w : Nat)
    (hS : (67186+999595*(122+840*w))%64=32) :
    ¬ BB6.Agent3.CReach
      (734+10944*(122+840*w))
      (34881+518816*(122+840*w)) := by
  obtain ⟨t,ht⟩ := p4_root32_u_parameter w hS
  have h := blank_no_b2_root32 t
  simpa only [ht] using h

/-- Conditional root-index form of the root32 exclusion, using the
exact residual root equation rather than a separately copied identity. -/
theorem blank_no_b2_root32_from_root_index (r E w : Nat)
    (hr : r%64=32)
    (hE : E=201+3360*(6657+8192*r))
    (hRoot : 18018+211*(122+840*w)+22155*r=20*2^(E-13)) :
    ¬ BB6.Agent3.CReach
      (734+10944*(122+840*w))
      (34881+518816*(122+840*w)) := by
  have hE19 : 19≤E := by omega
  have hExact :=
    p4_exact_residual_identity r E (122+840*w) hRoot
  have hS := p4_sum_mod64_of_root32 r E (122+840*w) hr hE19 hExact
  exact blank_no_b2_root32_from_p4_sum w hS

#print axioms p4_sum_mod64_of_root32
#print axioms p4_exact_residual_identity
#print axioms p4_root32_u_parameter
#print axioms blank_no_b2_root32_from_p4_sum
#print axioms blank_no_b2_root32_from_root_index

end BB6.Agent3U5B2Root32
