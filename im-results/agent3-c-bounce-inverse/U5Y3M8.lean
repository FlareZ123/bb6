import U5Y3ParentFan
import U5M8Q0Partial
import EvenRightSixOrbit
import OddOddVal3Orbit
import EvenOddFourExact
import HighSumTwo
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3U5M8

open BB6.Agent3
open BB6.Agent46
open BB6.Agent3U5DepthFan
open BB6.Agent11High

/-- The finite section orbit obtained by repeatedly applying the exact
six-even-right inverse map. -/
def u5Orbit (s : Nat) : Nat → Nat × Nat
  | 0 => (54+90*s,127+211*s)
  | n+1 =>
      let p := u5Orbit s n
      (p.1+p.2-2,(p.2-2)/2)

/-- The right counter along the u=5 chain has a closed form. -/
private theorem u5Orbit_snd (M s n : Nat)
    (hs : 211*s+129=5*2^(201+420*M))
    (hn : n≤201+420*M) :
    (u5Orbit s n).2 = 5*2^(201+420*M-n)-2 := by
  let r := 201+420*M
  induction n with
  | zero =>
      simp [u5Orbit,r]
      omega
  | succ n ih =>
      have hprev : n≤r := by omega
      have hlt : n<r := by omega
      have hq : r-n=(r-(n+1))+1 := by omega
      have hpow : 2^(r-n)=2^(r-(n+1))*2 := by
        rw [hq,Nat.pow_succ]
      have hprev' : (u5Orbit s n).2=5*2^(r-n)-2 := by
        simpa [r] using ih hprev
      change ((u5Orbit s n).2-2)/2=5*2^(r-(n+1))-2
      rw [hprev',hpow]
      omega

/-- The weighted mass x+2y+4n is invariant along the six-even-right
normalization chain. -/
private theorem u5Orbit_mass (M s n : Nat)
    (hs : 211*s+129=5*2^(201+420*M))
    (hn : n≤201+420*M) :
    (u5Orbit s n).1+2*(u5Orbit s n).2+4*n=308+512*s := by
  let r := 201+420*M
  induction n with
  | zero =>
      simp [u5Orbit]
      omega
  | succ n ih =>
      have hprev : n≤r := by omega
      have hlt : n<r := by omega
      have hprevMass := ih hprev
      have hy : (u5Orbit s n).2=5*2^(r-n)-2 := by
        simpa [r] using u5Orbit_snd M s n hs hprev
      have hdiv2 : 2∣2^(r-n) := by
        change 2^1∣2^(r-n)
        exact Nat.pow_dvd_pow 2 (by omega)
      have hpowPos : 0<2^(r-n) := Nat.pow_pos (by decide)
      have hpowGe : 2≤2^(r-n) := by
        rcases hdiv2 with ⟨v,hv⟩
        have hvpos : 0<v := by omega
        omega
      have hyGe : 2≤(u5Orbit s n).2 := by
        rw [hy]
        omega
      have hdiv : 2*((u5Orbit s n).2-2)/2=(u5Orbit s n).2-2 := by
        have heven : ((u5Orbit s n).2-2)%2=0 := by
          rw [hy]
          have hmod := Nat.mod_eq_zero_of_dvd hdiv2
          omega
        omega
      simp only [u5Orbit]
      rw [hdiv]
      omega

/-- Before the final two inverse steps, the left counter alternates
between 0 and 4 modulo eight. -/
private theorem u5Orbit_xmod8 (M s n : Nat)
    (hs : 211*s+129=5*2^(201+420*M))
    (hn : n≤201+420*M-2) :
    (u5Orbit s n).1%8=(4*n)%8 := by
  let r := 201+420*M
  induction n with
  | zero =>
      have hr3 : 3≤r := by omega
      have hdiv : 8∣2^r := by
        change 2^3∣2^r
        exact Nat.pow_dvd_pow 2 hr3
      have hpowmod : (2^r)%8=0 := Nat.mod_eq_zero_of_dvd hdiv
      have hsmod : (211*s+129)%8=0 := by
        rw [hs]
        omega
      have hs5 : s%8=5 := by omega
      simp [u5Orbit]
      omega
  | succ n ih =>
      have hprev : n≤r-2 := by omega
      have hq : 3≤r-n := by omega
      have hy : (u5Orbit s n).2=5*2^(r-n)-2 := by
        simpa [r] using u5Orbit_snd M s n hs (by omega)
      have hdiv : 8∣2^(r-n) := by
        change 2^3∣2^(r-n)
        exact Nat.pow_dvd_pow 2 hq
      have hpowmod : (2^(r-n))%8=0 :=
        Nat.mod_eq_zero_of_dvd hdiv
      have hy8 : (u5Orbit s n).2%8=6 := by
        rw [hy]
        omega
      have hx := ih hprev
      change ((u5Orbit s n).1+(u5Orbit s n).2-2)%8 =
        (4*(n+1))%8
      omega

/-- The penultimate left counter is 4 modulo eight; the preceding
alternation stops changing at the q=2 step. -/
private theorem u5Orbit_last_xmod8 (M s : Nat)
    (hs : 211*s+129=5*2^(201+420*M)) :
    (u5Orbit s (201+420*M-1)).1%8=4 := by
  let r := 201+420*M
  have hrOdd : r%2=1 := by dsimp [r]; omega
  have hx := u5Orbit_xmod8 M s (r-2) hs (by omega)
  have hy : (u5Orbit s (r-2)).2=5*2^(r-(r-2))-2 := by
    simpa [r] using u5Orbit_snd M s (r-2) hs (by omega)
  have hq : r-(r-2)=2 := by omega
  have hyEq : (u5Orbit s (r-2)).2=18 := by
    rw [hy,hq]
    decide
  have hidx : r-1=(r-2)+1 := by omega
  have hstep : (u5Orbit s (r-1)).1=
      (u5Orbit s (r-2)).1+(u5Orbit s (r-2)).2-2 := by
    rw [hidx]
    rfl
  rw [hyEq] at hstep
  omega

/-- Every nonterminal state in this chain satisfies the exact six-residue
even-right inverse gate. The last two cases are handled separately; this
is why the condition r=201 (mod 420), rather than merely r odd, matters. -/
private theorem u5Orbit_gate (M s n : Nat)
    (hs : 211*s+129=5*2^(201+420*M))
    (hn : n<201+420*M) :
    6≤(u5Orbit s n).2 ∧
    (u5Orbit s n).2%2=0 ∧
    ((u5Orbit s n).1+(u5Orbit s n).2)%8≠0 ∧
    ((u5Orbit s n).1+(u5Orbit s n).2)%8≠7 := by
  let r := 201+420*M
  have hy : (u5Orbit s n).2=5*2^(r-n)-2 := by
    simpa [r] using u5Orbit_snd M s n hs (by omega)
  have hqpos : 1≤r-n := by omega
  have hdiv2 : 2∣2^(r-n) := by
    change 2^1∣2^(r-n)
    exact Nat.pow_dvd_pow 2 hqpos
  have hpowPos : 0<2^(r-n) := Nat.pow_pos (by decide)
  have hpowGe : 2≤2^(r-n) := by
    rcases hdiv2 with ⟨v,hv⟩
    have hvpos : 0<v := by omega
    omega
  have hy6 : 6≤(u5Orbit s n).2 := by
    rw [hy]
    omega
  have hyEven : (u5Orbit s n).2%2=0 := by
    rw [hy]
    have hmod := Nat.mod_eq_zero_of_dvd hdiv2
    omega
  by_cases hq3 : 3≤r-n
  · have hx := u5Orbit_xmod8 M s n hs (by omega)
    have hdiv8 : 8∣2^(r-n) := by
      change 2^3∣2^(r-n)
      exact Nat.pow_dvd_pow 2 hq3
    have hpowmod : (2^(r-n))%8=0 :=
      Nat.mod_eq_zero_of_dvd hdiv8
    have hy8 : (u5Orbit s n).2%8=6 := by
      rw [hy]
      omega
    have hsum : ((u5Orbit s n).1+(u5Orbit s n).2)%8=2 ∨
        ((u5Orbit s n).1+(u5Orbit s n).2)%8=6 := by
      omega
    rcases hsum with hsum|hsum <;> exact ⟨hy6,hyEven,by omega,by omega⟩
  · by_cases hq2 : r-n=2
    · have hnEq : n=r-2 := by omega
      have hx := u5Orbit_xmod8 M s n hs (by omega)
      have hyEq : (u5Orbit s n).2=18 := by
        rw [hy,hq2]
        decide
      have hrOdd : r%2=1 := by dsimp [r]; omega
      have hnOdd : (r-2)%2=1 := by omega
      have hsum : ((u5Orbit s n).1+(u5Orbit s n).2)%8=6 := by
        rw [hyEq]
        omega
      exact ⟨hy6,hyEven,by omega,by omega⟩
    · have hq1 : r-n=1 := by omega
      have hnEq : n=r-1 := by omega
      have hx := u5Orbit_last_xmod8 M s hs
      have hyEq : (u5Orbit s n).2=8 := by
        rw [hy,hq1]
        decide
      have hsum : ((u5Orbit s n).1+(u5Orbit s n).2)%8=4 := by
        rw [hyEq]
        omega
      exact ⟨hy6,hyEven,by omega,by omega⟩

/-- One exact, source-certified inverse step in the u=5 chain. -/
private theorem u5Orbit_reach_iff (M s n : Nat)
    (hs : 211*s+129=5*2^(201+420*M))
    (hn : n<201+420*M) :
    CReach (u5Orbit s n).1 (u5Orbit s n).2 ↔
    CReach (u5Orbit s (n+1)).1 (u5Orbit s (n+1)).2 := by
  obtain ⟨hy,he,h0,h7⟩ := u5Orbit_gate M s n hs hn
  have hiff := BB6.Agent46.six_even_right_blank_reach_iff
    (u5Orbit s n).1 (u5Orbit s n).2 hy he h0 h7
  simpa [u5Orbit,CReach] using hiff

/-- The entire u=5 family B_s is exactly equivalent, at unbounded
time, to its terminal y=3 state. This proves all r inverse gates in one
parametric theorem and uses the authentic original-section source map. -/
theorem u5_residual_six_even_right_chain (M s : Nat)
    (hs : 211*s+129=5*2^(201+420*M)) :
    CReach (54+90*s) (127+211*s) ↔
    CReach (302+512*s-4*(201+420*M)) 3 := by
  let r := 201+420*M
  have hchain : ∀ n, n≤r →
      CReach (u5Orbit s 0).1 (u5Orbit s 0).2 ↔
      CReach (u5Orbit s n).1 (u5Orbit s n).2 := by
    intro n
    induction n with
    | zero =>
        intro hn
        simp [u5Orbit]
    | succ n ih =>
        intro hn
        have hprev : n≤r := by omega
        have hstep := u5Orbit_reach_iff M s n hs (by omega)
        exact (ih hprev).trans hstep
  have hlast := hchain r (by omega)
  have hyLast : (u5Orbit s r).2=3 := by
    have hh := u5Orbit_snd M s r hs (by omega)
    simpa [r] using hh
  have hmass := u5Orbit_mass M s r hs (by omega)
  have hxLast : (u5Orbit s r).1=302+512*s-4*r := by
    rw [hyLast] at hmass
    omega
  simpa [u5Orbit,r,hxLast,hyLast] using hlast

/-- For p=m+1 in the residue class p=1 (mod 8), the q=1 member of the
u=5 y=3 predecessor fan is already in the forbidden odd-right sum-two
image. -/
private theorem u5_q1_parent_unreachable (p : Nat)
    (hp8 : p%8=1) (hpge : 3≤p) :
    ¬ CReach (2*p-3) (7*p-4) := by
  apply blank_no_odd_sum_two
  · omega
  · omega
  · omega

/-- Infinite new u=5 residual cylinder: for M=8*w with w even or
w=3 mod 8, every possible original-source predecessor of the terminal
y=3 state is excluded. The other odd residue classes of w remain open. -/
theorem blank_no_u5_residual_m8w_partial (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%2=0 ∨ w%8=3) :
    ¬ CReach (302+512*s-4*(201+3360*w)) 3 := by
  have hs' : 211*s+129=5*2^(201+420*(8*w)) := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hs
  have hm' : 32*s=32+105*(8*w)+m := by omega
  have hid := u5_residual_m_identity (8*w) s m hs' hm'
  have hm7 := u5_residual_m_mod7 (8*w) m hid
  have hp8 : (m+1)%8=1 := by
    have hr3 : 3≤201+3360*w := by omega
    have hdiv : 8∣2^(201+3360*w) := by
      change 2^3∣2^(201+3360*w)
      exact Nat.pow_dvd_pow 2 hr3
    have hpowmod : (2^(201+3360*w))%8=0 :=
      Nat.mod_eq_zero_of_dvd hdiv
    have hNmod : (10669+22155*(8*w))%8=5 := by omega
    have hsum0 :
        (211*(m+1)+10669+22155*(8*w))%8=0 := by
      rw [hid]
      rw [show 201+420*(8*w)=201+3360*w by omega]
      rw [Nat.mul_mod]
      omega
    omega
  have hpge : 33≤m+1 := by omega
  have hX : 302+512*s-4*(201+3360*w)=16*m+10 := by omega
  intro hreach
  rcases hreach with ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      cases hprev : BB6.Agent8Section.run BB6.Agent46.secNext n
          (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hprev] at ht
      | some state =>
          rcases state with ⟨a,k⟩
          have hedge : BB6.Agent46.secNext (a,k)=some (16*m+10,3) := by
            simpa [BB6.Agent8Section.run,hprev,hX] using ht
          have hX' : 302+512*s-4*(201+420*(8*w))=16*m+10 := by omega
          have hedge' : BB6.Agent46.secNext (a,k)=
              some (302+512*s-4*(201+420*(8*w)),3) := by
            simpa only [hX'] using hedge
          rcases u5_residual_y3_parent_fan (8*w) s m a k hs' hm' hedge' with
              hq0 | ⟨q,U,hqpos,hqbound,hdecomp,hU,hk⟩
          · have hparent : CReach (8*(m+1)-3) (4*(m+1)-1) := by
              rw [hq0.1,hq0.2] at hprev
              exact ⟨n,hprev⟩
            let t := (m+1)/8
            have hp : m+1=8*t+1 := by
              dsimp [t]
              omega
            have ht : 1≤t := by dsimp [t]; omega
            rcases hw with hwEven|hw3
            · exact BB6.Agent11U5M8Q0Partial.blank_no_u5_q0_parent_w_even
                w s m t hs hm hp hwEven ht hparent
            · exact BB6.Agent11U5M8Q0Partial.blank_no_u5_q0_parent_w3
                w s m t hs hm hp hw3 ht hparent
          · have hq1 : q=1 := by
              by_contra hne
              have hq2 : 2≤q := by omega
              have hdiv : 4∣2^(2*q-2) := by
                change 2^2∣2^(2*q-2)
                exact Nat.pow_dvd_pow 2 (by omega)
              rcases hdiv with ⟨d,hd⟩
              have hpdiv : 4∣m+1 := by
                refine ⟨d*U,?_⟩
                calc
                  m+1=2^(2*q-2)*U := hdecomp
                  _=(4*d)*U := by rw [hd]
                  _=4*(d*U) := by ac_rfl
              omega
            subst q
            have hUeq : U=m+1 := by simpa using hdecomp.symm
            have hA : a=2*(m+1)-3 := by omega
            have hK : k=7*(m+1)-4 := by omega
            have hparent : CReach (2*(m+1)-3) (7*(m+1)-4) := by
              rw [hA,hK] at hprev
              exact ⟨n,hprev⟩
            exact u5_q1_parent_unreachable (m+1) hp8 hpge hparent

/-- The u=5 residual B_s cylinder is blank-unreachable for M=8*w
when w is even or w=3 mod 8. -/
theorem blank_no_u5_B_s_m8w_partial (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%2=0 ∨ w%8=3) :
    ¬ CReach (54+90*s) (127+211*s) := by
  have hs' : 211*s+129=5*2^(201+420*(8*w)) := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hs
  have hm' : 32*s=32+105*(8*w)+m := by omega
  intro h
  have hterminal :=
    (u5_residual_six_even_right_chain (8*w) s hs').mp h
  have hX : 302+512*s-4*(201+3360*w)=16*m+10 := by omega
  have hterminal' : CReach (302+512*s-4*(201+3360*w)) 3 := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hterminal
  exact blank_no_u5_residual_m8w_partial w s m hs hm hw hterminal'

#print axioms u5_residual_six_even_right_chain
#print axioms blank_no_u5_residual_m8w_partial
#print axioms blank_no_u5_B_s_m8w_partial

end BB6.Agent3U5M8
