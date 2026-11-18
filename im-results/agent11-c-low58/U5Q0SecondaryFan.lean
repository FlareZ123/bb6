import EvenEvenParentFan
import M0EvenEvenSumZeroParents
import U5M8Q0Partial
import Lean.Elab.Tactic.Omega

/-!
A source-exact reduction of the q=0 U5 even/even parent P0 on the
w = 1 (mod 16) branch.  It eliminates the exceptional zero-left parent
and the depth-one even-a bounce, and reduces the direct parent to one
explicit state.  All deeper odd bounce depths are retained parametrically.

This is an intermediate source-parent theorem, not a blank-root
nonreachability result and not a BB(6) solution.
-/

namespace BB6.Agent11U5Q0SecondaryFan

open BB6.Agent46

private theorem even_even_sum_two_reach_implies_direct
    (x y : Nat)
    (hxpos : 0<x) (hxe : x%2=0)
    (hy6 : 6≤y) (hye : y%2=0)
    (hsum : (x+y)%4=2)
    (hreach : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
  rcases hreach with ⟨time, hrun⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hrun
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run, hp] at hrun
      | some p =>
          rcases p with ⟨a,k⟩
          have hedge : secNext (a,k)=some (x,y) := by
            simpa [BB6.Agent8Section.run, hp] using hrun
          have hfan := BB6.Agent3ParentFan.even_even_parent_fan
            a k x y hxpos hxe hy6 hye hedge
          rcases hfan with hD | hZ | hB
          · rcases hD with ⟨ha,hk⟩
            refine ⟨n, ?_⟩
            simpa only [ha,hk] using hp
          · rcases hZ with ⟨ha,hk,hdepth,hsum',hcost⟩
            have hdiv8 : 8 ∣ x+y := by
              rw [hsum']
              refine ⟨2^hdepth, ?_⟩
              ac_rfl
            have hdiv4 : 4 ∣ x+y :=
              dvd_trans (by decide : 4 ∣ 8) hdiv8
            have hmod : (x+y)%4=0 :=
              Nat.dvd_iff_mod_eq_zero.mp hdiv4
            omega
          · rcases hB with ⟨ha2,haeven,hkpos,halow,hdepth,hodd,hsum',hcost⟩
            have hdiv4 : 4 ∣ 2^(hdepth+1) := by
              have hd : (2:Nat)^2 ∣ (2:Nat)^(hdepth+1) :=
                Nat.pow_dvd_pow 2 (by omega)
              simpa only [show (2:Nat)^2=4 by decide] using hd
            have hdiv2 : 2 ∣ a+2 := by
              refine ⟨a/2+1, ?_⟩
              omega
            have hdiv8 : 8 ∣ 2^(hdepth+1)*(a+2) := by
              rcases hdiv4 with ⟨u,hu⟩
              rcases hdiv2 with ⟨v,hv⟩
              refine ⟨u*v, ?_⟩
              rw [hu,hv]
              ac_rfl
            have hdiv : 8 ∣ x+y := by
              rw [hsum']
              exact hdiv8
            have hdiv4' : 4 ∣ x+y :=
              dvd_trans (by decide : 4 ∣ 8) hdiv
            have hmod : (x+y)%4=0 :=
              Nat.dvd_iff_mod_eq_zero.mp hdiv4'
            omega

private theorem u5_q0_direct_parent_reduction (h : Nat)
    (hD : BB6.Agent3.CReach (3326+5472*h) (826+1360*h)) :
    BB6.Agent3.CReach (1036+1708*h) (1966+3242*h) := by
  have hsum : (3326+5472*h)+(826+1360*h)=8*(519+854*h) := by omega
  have hSgt : 2<519+854*h := by omega
  have hS4 : (519+854*h)%4≠0 := by omega
  have hparents :=
    BB6.Agent11M0SumZero.eveneven_sumzero_blank_reach_parent
      (3326+5472*h) (826+1360*h) (519+854*h)
      (by omega) (by omega) (by omega) (by omega)
      hsum hSgt hS4 hD
  rcases hparents with hQ | hE
  · have hQ' : BB6.Agent3.CReach (4150+6832*h) (412+680*h) := by
      have hx : (3326+5472*h)+(826+1360*h)-2=4150+6832*h := by omega
      have hy : ((826+1360*h)-2)/2=412+680*h := by omega
      simpa only [hx,hy] using hQ
    have hQdirect :=
      even_even_sum_two_reach_implies_direct
        (4150+6832*h) (412+680*h)
        (by omega) (by omega) (by omega) (by omega)
        (by omega) hQ'
    have hQdirect' : BB6.Agent3.CReach
        (4560+7512*h) (205+340*h) := by
      have hx : (4150+6832*h)+(412+680*h)-2=4560+7512*h := by omega
      have hy : ((412+680*h)-2)/2=205+340*h := by omega
      simpa only [hx,hy] using hQdirect
    have hsumOdd : ((4560+7512*h)+(205+340*h))%4=1 := by omega
    exact (BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (4560+7512*h) (205+340*h)
      (by omega) (by omega) (by omega) hsumOdd hQdirect').elim
  · have hx : 2*(519+854*h)-2=1036+1708*h := by omega
    have hy :
        ((3326+5472*h)+2*(826+1360*h)-2*(519+854*h)-8)/2
          =1966+3242*h := by omega
    simpa only [hx,hy] using hE

/--
If the q=0 U5 even/even parent
P0=(1674+2752h,1654+2720h) is blank-reachable, then either its
direct-parent branch descends to the explicit state E_h, or one of the
odd-depth even-a bounce parents B_(r,h) is blank-reachable.  The
zero-left alternative and the n=1 bounce alternative are eliminated
uniformly.  The remaining r>=1 fan is exact and unbounded in h.
-/
theorem u5_q0_secondary_parent_reduction (h : Nat)
    (hP : BB6.Agent3.CReach (1674+2752*h) (1654+2720*h)) :
    BB6.Agent3.CReach (1036+1708*h) (1966+3242*h) ∨
    ∃ r q : Nat,
      1≤r ∧ 4^r*q=416+684*h ∧
      BB6.Agent3.CReach (2*q-2) (2487+4096*h-q-3*r) := by
  let t := 39+64*h
  let S := 416+684*h
  let x := 1674+2752*h
  let y := 1654+2720*h
  have hxpos : 0<x := by dsimp [x]; omega
  have hxe : x%2=0 := by dsimp [x]; omega
  have hy6 : 6≤y := by dsimp [y]; omega
  have hye : y%2=0 := by dsimp [y]; omega
  have hsum : x+y=8*S := by dsimp [x,y,S]; omega
  have hS : 16*S+13=171*t := by dsimp [S,t]; omega
  rcases hP with ⟨time, hrun⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hrun
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run, hp] at hrun
      | some p =>
          rcases p with ⟨a,k⟩
          have hedge : secNext (a,k)=some (x,y) := by
            simpa [BB6.Agent8Section.run, hp] using hrun
          have hfan := BB6.Agent3ParentFan.even_even_parent_fan
            a k x y hxpos hxe hy6 hye hedge
          rcases hfan with hD | hZ | hB
          · rcases hD with ⟨ha,hk⟩
            have hDreach : BB6.Agent3.CReach
                (3326+5472*h) (826+1360*h) := by
              refine ⟨n, ?_⟩
              have hax : a=3326+5472*h := by
                rw [ha]
                dsimp [x,y]
                omega
              have hky : k=826+1360*h := by
                rw [hk]
                dsimp [y]
                omega
              simpa only [hax,hky] using hp
            exact Or.inl (u5_q0_direct_parent_reduction h hDreach)
          · rcases hZ with ⟨ha,hk,hdepth,hzero,hcost⟩
            have hzero' : 8*S=2^hdepth*8 := by
              calc
                8*S = x+y := hsum.symm
                _ = 2^hdepth*8 := hzero
            exact (BB6.Agent11U5M8Q0Partial.u5_q0_zero_left_branch_impossible
              t S hdepth hS hzero').elim
          · rcases hB with ⟨ha2,haeven,hkpos,halow,hdepth,hodd,hbounce,hcost⟩
            obtain ⟨r,hrdepth⟩ : ∃ r : Nat, hdepth=2*r+1 := by omega
            by_cases hr0 : r=0
            · subst r
              have hdepth1 : hdepth=1 := by omega
              have haEq : a=830+1368*h := by
                rw [hdepth1] at hbounce
                norm_num at hbounce
                dsimp [x,y] at hbounce
                omega
              have hkEq : k=2071+3412*h := by
                rw [hdepth1] at hcost
                norm_num at hcost
                dsimp [x,y] at hcost
                omega
              have hparent : BB6.Agent3.CReach
                  (830+1368*h) (2071+3412*h) := by
                refine ⟨n, ?_⟩
                simpa only [haEq,hkEq] using hp
              have hsumOdd :
                  ((830+1368*h)+(2071+3412*h))%4=1 := by omega
              exact (BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
                (830+1368*h) (2071+3412*h)
                (by omega) (by omega) (by omega) hsumOdd hparent).elim
            · have hrpos : 1≤r := by omega
              let q := (a+2)/2
              have haq : a+2=2*q := by
                dsimp [q]
                omega
              have hpow : (2:Nat)^(2*r+3)=8*4^r := by
                calc
                  (2:Nat)^(2*r+3) = (2:Nat)^(2*r)*(2:Nat)^3 := by
                    rw [Nat.pow_add]
                  _ = ((2:Nat)^2)^r*8 := by
                    rw [Nat.pow_mul]
                    norm_num
                  _ = 4^r*8 := by norm_num
                  _ = 8*4^r := by rw [Nat.mul_comm]
              have hSQ : S=4^r*q := by
                have hmul : 8*S=8*(4^r*q) := by
                  calc
                    8*S = x+y := hsum.symm
                    _ = 2^(hdepth+1)*(a+2) := hbounce
                    _ = 2^(2*r+2)*(2*q) := by rw [hrdepth,haq]
                    _ = 2^(2*r+3)*q := by
                      rw [Nat.pow_succ]
                      ac_rfl
                    _ = 8*(4^r*q) := by rw [hpow]; ac_rfl
                omega
              have haEq : a=2*q-2 := by omega
              have hkEq : k=2487+4096*h-q-3*r := by
                rw [hrdepth,haEq] at hcost
                dsimp [x,y] at hcost
                omega
              have hparent : BB6.Agent3.CReach
                  (2*q-2) (2487+4096*h-q-3*r) := by
                refine ⟨n, ?_⟩
                simpa only [haEq,hkEq] using hp
              exact Or.inr ⟨r,q,hrpos,by dsimp [S] at hSQ; exact hSQ.symm,hparent⟩

#print axioms even_even_sum_two_reach_implies_direct
#print axioms u5_q0_direct_parent_reduction
#print axioms u5_q0_secondary_parent_reduction

end BB6.Agent11U5Q0SecondaryFan
