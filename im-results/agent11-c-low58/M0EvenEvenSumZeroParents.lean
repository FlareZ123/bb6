import SectionAllInverse
import M0FourRoot
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0SumZero
open BB6.Agent46

/--
Forward-only complete parent classification for an even/even target in
the sum-zero mod-8 sector when its quotient has 2-adic valuation at most
one.  The original all-depth source grammar leaves exactly two possible
parents: the direct/low parent and the unique depth-one even-a bounce
parent.  No finite inverse-depth cutoff is used.
-/
theorem eveneven_sumzero_parent_necessity
    (a k x y S : Nat)
    (hxpos : 0<x) (hx : x%2=0) (hy : y%2=0) (hy6 : 6≤y)
    (hsum : x+y=8*S) (hS2 : 2<S) (hS4 : S%4≠0)
    (hedge : secNext (a,k)=some (x,y)) :
    (a=x+y-2 ∧ k=(y-2)/2) ∨
    (a=2*S-2 ∧ 2*k+2*S+8=x+2*y) := by
  have hpre : sectionPreimageAll a k x y :=
    (section_preimage_all_iff a k x y).mp hedge
  by_cases ha0 : a=0
  · subst a
    by_cases hk0 : k=0
    · simp [sectionPreimageAll, hk0] at hpre
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll, hk0, hk1] at hpre
        omega
      · simp [sectionPreimageAll, hk0, hk1] at hpre
        rcases hpre with ⟨_, n, hsum', _⟩
        have hpowEq : S=2^n := by
          rw [hsum] at hsum'
          omega
        by_cases hn : n<2
        · have hn01 : n=0 ∨ n=1 := by omega
          rcases hn01 with rfl | rfl <;> simp at hpowEq <;> omega
        · have hn2 : 2≤n := by omega
          have hdiv : 4∣2^n := by
            have hd : (2:Nat)^2∣(2:Nat)^n := Nat.pow_dvd_pow 2 hn2
            simpa only [show (2:Nat)^2=4 by decide] using hd
          have hdivS : 4∣S := by rw [hpowEq]; exact hdiv
          have hmod : S%4=0 := Nat.dvd_iff_mod_eq_zero.mp hdivS
          omega
  · by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · simp [sectionPreimageAll, hk0] at hpre
        omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll, hk0, hk1] at hpre
          omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll, hk0, hk1, hk2] at hpre
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll, hk0, hk1, hk2, hk3] at hpre
              omega
            · simp [sectionPreimageAll, hk0, hk1, hk2, hk3] at hpre
              rcases hpre with ⟨hy3, _⟩ | ⟨_, n, hsum', _⟩
              · omega
              · have hodd : (x+y+1)%2=1 := by omega
                have hdiv : 2∣2^n*16 := by
                  refine ⟨2^n*8, ?_⟩
                  ac_rfl
                have hzero : (2^n*16)%2=0 :=
                  Nat.dvd_iff_mod_eq_zero.mp hdiv
                rw [hsum'] at hodd
                rw [hzero] at hodd
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll, ha0, ha1, hk0] at hpre
        omega
      · by_cases hlow : 2*k≤a
        · simp [sectionPreimageAll, ha0, ha1, hk0, hlow] at hpre
          left
          rcases hpre with ⟨hxx, hyy⟩
          omega
        · by_cases haeven : a%2=0
          · simp [sectionPreimageAll, ha0, ha1, hk0, hlow, haeven] at hpre
            rcases hpre with ⟨_, n, hsum', hcost⟩
            have hcost' : 2*k+a+7+3*n=x+2*y := by omega
            have hnodd : n%2=1 := by omega
            have hn1 : n=1 := by
              by_contra hn
              have hn3 : 3≤n := by omega
              have hdiv8 : 8∣2^n := by
                have hd : (2:Nat)^3∣(2:Nat)^n := Nat.pow_dvd_pow 2 hn3
                simpa only [show (2:Nat)^3=8 by decide] using hd
              have haEq2 : a=2*(a/2) := by omega
              have hdiv4 : 4∣2*a+4 := by
                refine ⟨a/2+1, ?_⟩
                rw [haEq2]
                omega
              have hdiv32 : 32∣2^n*(2*a+4) := by
                rcases hdiv8 with ⟨u, hu⟩
                rcases hdiv4 with ⟨v, hv⟩
                refine ⟨u*v, ?_⟩
                rw [hu, hv]
                ac_rfl
              have hsum'' : x+y=2^n*(2*a+4) := by
                calc
                  x+y=2^n*(2*(a-1)+6) := hsum'
                  _=2^n*(2*a+4) := by congr 1 <;> omega
              have hdivx : 32∣x+y := by
                rw [hsum'']
                exact hdiv32
              have hdivS : 4∣S := by
                rw [hsum] at hdivx
                rcases hdivx with ⟨q, hq⟩
                refine ⟨q, ?_⟩
                omega
              have hmod : S%4=0 := Nat.dvd_iff_mod_eq_zero.mp hdivS
              omega
            have hsum'' : x+y=2^n*(2*a+4) := by
              calc
                x+y=2^n*(2*(a-1)+6) := hsum'
                _=2^n*(2*a+4) := by congr 1 <;> omega
            have hsum1 : x+y=4*a+8 := by
              simp [hn1] at hsum''
              omega
            have haEq : a=2*S-2 := by
              rw [hsum] at hsum1
              omega
            have hkEq : 2*k+2*S+8=x+2*y := by
              simp [hn1] at hcost'
              omega
            exact Or.inr ⟨haEq, hkEq⟩
          · simp [sectionPreimageAll, ha0, ha1, hk0, hlow, haeven] at hpre
            rcases hpre with ⟨hy3, _⟩ | ⟨_, n, hsum', _⟩
            · omega
            · have hodd : (x+y+1)%2=1 := by omega
              have hfactor : 2*(a-1)+8=2*(a+3) := by omega
              have hdiv : 2∣2^n*(2*(a-1)+8) := by
                refine ⟨2^n*(a+3), ?_⟩
                rw [hfactor]
                ac_rfl
              have hzero :
                  (2^n*(2*(a-1)+8))%2=0 :=
                Nat.dvd_iff_mod_eq_zero.mp hdiv
              rw [hsum'] at hodd
              rw [hzero] at hodd
              omega

/--
Every genuine blank-root visit to such a target has a genuine blank-root
visit to one of the two classified source parents.  The time-zero case is
separated explicitly; the positive-time case extracts the actual previous
section state and applies the complete source inverse grammar.
-/
theorem eveneven_sumzero_blank_reach_parent
    (x y S : Nat)
    (hxpos : 0<x) (hx : x%2=0) (hy : y%2=0) (hy6 : 6≤y)
    (hsum : x+y=8*S) (hS2 : 2<S) (hS4 : S%4≠0)
    (hreach : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) ∨
    BB6.Agent3.CReach (2*S-2) ((x+2*y-2*S-8)/2) := by
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
          have hed : secNext (a,k)=some (x,y) := by
            simpa [BB6.Agent8Section.run, hp] using hrun
          have hparents :=
            eveneven_sumzero_parent_necessity a k x y S
              hxpos hx hy hy6 hsum hS2 hS4 hed
          rcases hparents with ⟨ha,hk⟩ | ⟨ha,hk⟩
          · left
            refine ⟨n, ?_⟩
            simpa only [ha,hk] using hp
          · right
            have hk' : k=(x+2*y-2*S-8)/2 := by omega
            refine ⟨n, ?_⟩
            simpa only [ha,hk'] using hp

/--
The odd-parameter residual A_s=(130+208s,94+152s) has exactly the
two source-parent reachability alternatives L_s and B_(0,s).
For odd s its quotient S=28+45s is odd, so all deeper even-a bounce
branches are excluded by the generic parent lemma.
-/
theorem mzero_odd_sumzero_reach_parents (s : Nat) (hs : s%2=1)
    (hreach : BB6.Agent3.CReach (130+208*s) (94+152*s)) :
    BB6.Agent3.CReach (222+360*s) (46+76*s) ∨
    BB6.Agent3.CReach (54+90*s) (127+211*s) := by
  have hparents :=
    eveneven_sumzero_blank_reach_parent
      (130+208*s) (94+152*s) (28+45*s)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hreach
  rcases hparents with hL | hB
  · left
    have hx : (130+208*s)+(94+152*s)-2=222+360*s := by omega
    have hy : ((94+152*s)-2)/2=46+76*s := by omega
    simpa only [hx,hy] using hL
  · right
    have hx : 2*(28+45*s)-2=54+90*s := by omega
    have hy :
        ((130+208*s)+2*(94+152*s)-2*(28+45*s)-8)/2 =
          127+211*s := by omega
    simpa only [hx,hy] using hB

#print axioms eveneven_sumzero_parent_necessity
#print axioms eveneven_sumzero_blank_reach_parent
#print axioms mzero_odd_sumzero_reach_parents

end BB6.Agent11M0SumZero
