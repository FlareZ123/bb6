import DyadicLowTower
import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace BB6.Agent31OddDepthTower

open BB6.Agent3
open BB6.Agent46
open BB6.Agent11M0SumZeroVerified

/-- One exact even-right inverse step on the C-section counters. -/
def dyadicStep (a b : Nat) : Nat × Nat := (a+b-2,(b-2)/2)

/-- Iterate the exact even-right inverse, applying the first step first. -/
def dyadicIter : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | n+1, p => dyadicIter n (dyadicStep p.1 p.2)

/-- Closed form for the terminal state after n-1 even-right inverses. -/
theorem dyadicIter_terminal (n a b u : Nat)
    (hn : 1≤n) (hb : b+2=2^n*u) :
    (dyadicIter (n-1) (a,b)).2 + 2 = 2*u ∧
    (dyadicIter (n-1) (a,b)).1 + (dyadicIter (n-1) (a,b)).2 + 4*n + 2*u =
      a + u*2^(n+1)+2 := by
  induction n generalizing a b u with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          simp [dyadicIter] at *
          omega
      | succ t =>
          have hpow : (2:Nat)^(t+2)*u = 2*(2^(t+1)*u) := by
            rw [Nat.pow_succ]
            ac_rfl
          have hb0 := hb
          rw [hpow] at hb0
          have hEven : b%2=0 := by omega
          let X : Nat := 2^(t+1)*u
          have hu1 : 1≤u := by
            by_cases hz : u=0
            · subst u
              simp [X] at hb0
            · omega
          have hX : 2≤X := by
            change 2≤2^(t+1)*u
            have hp : 2≤(2:Nat)^(t+1) := by
              have ht : 1≤(2:Nat)^t := Nat.pow_pos (by decide)
              rw [Nat.pow_succ]
              omega
            have hm := Nat.mul_le_mul hp hu1
            omega
          have hbX : b+2=2*X := by simpa [X] using hb0
          have hbge : 2≤b := by omega
          have hbminus : b-2=2*(X-2) := by omega
          have hb' : (b-2)/2+2=X := by rw [hbminus]; omega
          have ih' := ih (a+b-2) ((b-2)/2) u (by omega) hb'
          rcases ih' with ⟨hB,hSum⟩
          constructor
          · change (dyadicIter t (dyadicStep a b)).2 + 2 = 2*u
            simpa [dyadicStep] using hB
          · change (dyadicIter t (dyadicStep a b)).1 +
              (dyadicIter t (dyadicStep a b)).2 + 4*(t+2) + 2*u =
              a + u*2^(t+3)+2
            have hsum' : (dyadicIter t (dyadicStep a b)).1 +
                (dyadicIter t (dyadicStep a b)).2 + 4*(t+1) + 2*u =
                (a+b-2) + u*2^(t+2)+2 := by
              simpa [dyadicStep] using hSum
            have hpow2 : (2:Nat)^(t+3) = 2*(2^(t+2)) := by
              rw [Nat.pow_succ]
              ac_rfl
            have hmul : u*2^(t+3)=2*(u*2^(t+2)) := by
              rw [hpow2]
              ac_rfl
            have hbsub : b-2+4=u*2^(t+2) := by
              have hbcomm : b+2=u*2^(t+2) := by simpa [Nat.mul_comm] using hb
              omega
            have hbge : 2≤b := by omega
            omega

/--
Mass-residue-4 odd-depth cone.

At exponent one the terminal pair is even-even with sum divisible by eight.
The source-verified even-even parent theorem leaves only its direct and bounce
parents; the mass and terminal-sum residues force both parents into the
forbidden odd-right, sum-one-mod-four image.
-/
theorem dyadic_six_cone_mass4_no_blank (r a b u S : Nat)
    (hr : 1≤r) (hu : 9≤u) (hu4 : u%4=1)
    (hb : b+2=2^r*u)
    (hmass : (a+2*b+4*r)%8=4)
    (hterm : (dyadicIter (r-1) (a,b)).1 + (dyadicIter (r-1) (a,b)).2 = 8*S)
    (hA : 5 < (dyadicIter (r-1) (a,b)).1)
    (hS4 : S%4=3) (hSgt : 4≤S) :
    ¬ CReach a b := by
  induction r generalizing a b with
  | zero => omega
  | succ s ih =>
      cases s with
      | zero =>
          have hterm' : a+b=8*S := by simpa [dyadicIter] using hterm
          have hB : b+2=2*u := by simpa using hb
          have hb8 : b%8=0 := by omega
          have ha8 : a%8=0 := by omega
          have hxe : a%2=0 := by omega
          have hye : b%2=0 := by omega
          have hy : 6≤b := by omega
          have hDleft : a+b-2=8*S-2 := by omega
          have hDright : (b-2)/2=u-2 := by omega
          have hD : ¬ CReach (a+b-2) ((b-2)/2) := by
            rw [hDleft,hDright]
            apply blank_no_odd_sum_one
            · omega
            · omega
            · omega
            · omega
          have hEy : (a+2*b-2*S-8)/2 = 3*S+u-5 := by
            have haeq : a=8*S-b := by omega
            have hbEq : b=2*u-2 := by omega
            have hnum : a+2*b-2*S-8=2*(3*S+u-5) := by omega
            rw [hnum]
            omega
          have hE : ¬ CReach (2*S-2) ((a+2*b-2*S-8)/2) := by
            rw [hEy]
            apply blank_no_odd_sum_one
            · omega
            · omega
            · omega
            · omega
          exact blank_no_sumzero_target a b S
            (by simpa [dyadicIter] using hA) hxe hy hye hterm' (by omega) (by omega) hD hE
      | succ t =>
          intro hreach
          have hpow : (2:Nat)^(t+2)*u = 2*(2^(t+1)*u) := by
            rw [Nat.pow_succ]
            ac_rfl
          have hb0 := hb
          rw [hpow] at hb0
          let X : Nat := 2^(t+1)*u
          have hX : 9≤X := by
            change 9≤2^(t+1)*u
            have hp : 1≤(2:Nat)^(t+1) := Nat.pow_pos (by decide)
            have hm : u≤2^(t+1)*u := by simpa using Nat.mul_le_mul_right u hp
            omega
          have hbX : b+2=2*X := by simpa [X] using hb0
          have hEven : b%2=0 := by omega
          have hB : 6≤b := by omega
          have ha4 : a%4=0 := by omega
          have hb4 : b%4=2 := by
            have hp : 4∣b+2 := by
              refine ⟨2^t*u, ?_⟩
              have hpow4 : (2:Nat)^(t+2)=4*2^t := by
                calc
                  (2:Nat)^(t+2) = (2^t*2)*2 := by
                    rw [Nat.pow_succ, Nat.pow_succ]
                  _ = 4*2^t := by omega
              rw [hb, hpow4]
              ac_rfl
            omega
          have hmod : (a+b)%8≠0 ∧ (a+b)%8≠7 := by omega
          have hnext : CReach (a+b-2) ((b-2)/2) :=
            (six_even_right_blank_reach_iff a b hB hEven hmod.1 hmod.2).mp hreach
          have hbminus : b-2=2*(X-2) := by omega
          have hbnext : (b-2)/2+2=2^(t+1)*u := by
            rw [hbminus]
            simp [X]
            omega
          have hdiv : 2*((b-2)/2)=b-2 := by omega
          have hmassEq : (a+b-2)+2*((b-2)/2)+4*(t+1) =
              a+2*b+4*(t+2)-8 := by omega
          have hmassnext : ((a+b-2)+2*((b-2)/2)+4*(t+1))%8=4 := by omega
          have htermnext :
              (dyadicIter t (dyadicStep a b)).1 +
              (dyadicIter t (dyadicStep a b)).2 = 8*S := by
            simpa [dyadicIter,dyadicStep] using hterm
          have hAnext : 5 < (dyadicIter t (dyadicStep a b)).1 := by
            simpa [dyadicIter,dyadicStep] using hA
          exact ih (a+b-2) ((b-2)/2) (by omega) hbnext hmassnext htermnext hAnext hnext

theorem exists_eq_64_add_96_mul_of_mod (n : Nat) :
    n%96=64 → ∃ w, n=64+96*w := by
  intro h
  have hdiv := Nat.mod_add_div n 96
  refine ⟨n/96, ?_⟩
  omega

theorem pow_even_mod96 (t : Nat) :
    (2:Nat)^(2*t+6) % 96 = 64 := by
  induction t with
  | zero => decide
  | succ t ih =>
      have hp : (2:Nat)^(2*(t+1)+6) = 4 * 2^(2*t+6) := by
        have he : 2*(t+1)+6 = (2*t+6)+2 := by omega
        rw [he, Nat.pow_add]
        rw [show (2:Nat)^2=4 by decide]
        ac_rfl
      rw [hp, Nat.mul_mod, ih]

theorem pow_even_mod96_from4 (t : Nat) (ht : 1≤t) :
    (2:Nat)^(2*t+4) % 96 = 64 := by
  cases t with
  | zero => omega
  | succ t =>
      have h := pow_even_mod96 t
      have he : 2*(t+1)+4=2*t+6 := by omega
      rw [he]
      exact h

theorem oddS_mod4 (n u S q w t : Nat)
    (hnform : n=2*t+1)
    (huform : u=6*n+7+48*q)
    (hformula : 24*S+12*n = u*(58+96*w)+2) :
    S%4=3 := by
  let Z : Nat := (6*n+7)*w+29*q+48*q*w
  have hprod1 : (6*n+7+48*q)*(58+96*w) =
      (6*n+7)*58 + (6*n+7)*(96*w) + (48*q)*58 + (48*q)*(96*w) := by
    simp [Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hprod2 : (6*n+7+48*q)*(58+96*w) = 58*(6*n+7)+96*Z := by
    calc
      (6*n+7+48*q)*(58+96*w)
          = (6*n+7)*58 + (6*n+7)*(96*w) + (48*q)*58 + (48*q)*(96*w) := hprod1
      _ = 58*(6*n+7)+96*Z := by
        dsimp [Z]
        rw [show (6*n+7)*(96*w)=96*((6*n+7)*w) by ac_rfl]
        rw [show (48*q)*58=96*(29*q) by omega]
        rw [show (48*q)*(96*w)=96*(48*q*w) by ac_rfl]
        rw [show (6*n+7)*58=58*(6*n+7) by ac_rfl]
        omega
  have hsum : 24*S+12*n = 58*(6*n+7)+96*Z+2 := by
    rw [hformula, huform, hprod2]
  have hS : S=28*t+31+4*Z := by
    rw [hnform] at hsum
    omega
  rw [hS]
  omega

/--
For every odd depth n≥3, the low odd/odd gate is excluded on the residue
class u = 6n+7 (mod 48). The even-depth mass-zero cone is replaced here by
the mass-four terminal-parent argument above.
-/
theorem odd_gate_dyadic_tower_mass4_no_blank (n k u q : Nat)
    (hn : 3≤n) (hne : n%2=1)
    (huform : u=6*n+7+48*q)
    (hgate : 3*k=2^(n+2)*u+1) :
    ¬ CReach 1 k := by
  have hu : 9≤u := by rw [huform]; omega
  have hu4 : u%4=1 := by rw [huform]; omega
  have hpow16 : 16∣2^(n+2) := by
    have h16 : 4≤n+2 := by omega
    exact Nat.pow_dvd_pow 2 h16
  rcases hpow16 with ⟨v,hv⟩
  have h3k : 3*k=16*(v*u)+1 := by
    calc
      3*k = 2^(n+2)*u+1 := hgate
      _ = 16*(v*u)+1 := by rw [hv]; ac_rfl
  have hk16 : k%16=11 := by omega
  have hvpos : 1≤v := by
    have hpos : 0<2^(n+2) := Nat.pow_pos (by decide)
    omega
  have hvu : 9≤v*u := by
    have hm : u≤v*u := by simpa using Nat.mul_le_mul_right u hvpos
    omega
  have hkbig : 24≤k+1 := by omega
  let a : Nat := (1+k-4)/2
  let b : Nat := (1+3*k-10)/4
  have hrel1 : 1+k=2*a+4 := by dsimp [a]; omega
  have hrel2 : 1+3*k=4*b+10 := by dsimp [b]; omega
  have hfactor : (2:Nat)^(n+2)=4*2^n := by
    rw [Nat.pow_add]
    rw [show (2:Nat)^2=4 by decide]
    ac_rfl
  have h3k2 : 3*k=4*(2^n*u)+1 := by
    calc
      3*k = 2^(n+2)*u+1 := hgate
      _ = 4*(2^n*u)+1 := by rw [hfactor]; ac_rfl
  have hb : b+2=2^n*u := by
    have hsum : 1+3*k=4*(2^n*u)+2 := by omega
    dsimp [b]
    omega
  have hmass : a+2*b+6=2*k := by omega
  have hdivPow8 : 8∣2^n := by
    have h : 2^3∣2^n := Nat.pow_dvd_pow 2 (by omega)
    simpa using h
  have hdivB8 : 8∣b+2 := by
    rcases hdivPow8 with ⟨w,hw⟩
    refine ⟨w*u, ?_⟩
    rw [hb,hw]
    ac_rfl
  have hb8 : b%8=6 := by omega
  have ha8 : a%8=4 := by omega
  have hcong4 : (a+2*b+4*n)%8=4 := by omega
  have hpred : CReach 1 k ↔ CReach a b :=
    BB6.Agent3.oddodd_lowval_blank_reach_iff 1 k
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hterminal := dyadicIter_terminal n a b u (by omega) hb
  rcases hterminal with ⟨hBplus,hSumPlus⟩
  let p : Nat × Nat := dyadicIter (n-1) (a,b)
  have hBplus' : p.2+2=2*u := by simpa [p] using hBplus
  have hSumPlus' : p.1+p.2+4*n+2*u=a+u*2^(n+1)+2 := by simpa [p] using hSumPlus
  have hdivPow8' : 8∣2^(n+1) := by
    have h : 2^3∣2^(n+1) := Nat.pow_dvd_pow 2 (by omega)
    simpa using h
  have hdivTerm8 : 8∣u*2^(n+1) := by
    rcases hdivPow8' with ⟨w,hw⟩
    refine ⟨u*w, ?_⟩
    rw [hw]
    ac_rfl
  have hsumMod8 : (p.1+p.2)%8=0 := by
    have h2u : (2*u)%8=2 := by omega
    have h4n : (4*n)%8=4 := by omega
    have hterm8 : (u*2^(n+1))%8=0 := by omega
    omega
  let S : Nat := (p.1+p.2)/8
  have hterm : p.1+p.2=8*S := by
    dsimp [S]
    have hdiv := Nat.mod_add_div (p.1+p.2) 8
    omega
  have ha10 : 10≤a := by omega
  have hpow16' : 16≤2^(n+1) := by
    have hdiv : 16∣2^(n+1) := by
      have h : 2^4∣2^(n+1) := Nat.pow_dvd_pow 2 (by omega)
      simpa using h
    rcases hdiv with ⟨w,hw⟩
    have hwpos : 1≤w := by
      have hpos :0<2^(n+1) := Nat.pow_pos (by decide)
      omega
    omega
  have hmulPow : 16*u≤u*2^(n+1) := by
    have h := Nat.mul_le_mul_left u hpow16'
    simpa [Nat.mul_comm] using h
  have hsmall : 4*(n-1)+4*u≤16*u := by rw [huform]; omega
  have hAeq : p.1+4*n+4*u=a+u*2^(n+1)+4 := by omega
  have hA : 10≤p.1 := by omega
  have hB8 : p.2%8=0 := by omega
  have hA8 : p.1%8=0 := by omega
  have hB16 : 16≤p.2 := by omega
  have hA16 : 16≤p.1 := by omega
  have hSgt : 4≤S := by omega
  have h3a : 3*a+4=u*2^(n+1) := by
    have hk : k=2*a+3 := by omega
    have hpow : (2:Nat)^(n+1)=2*2^n := by
      rw [Nat.pow_succ]
      ac_rfl
    have h6a : 6*a+8=4*(2^n*u) := by
      rw [hk] at h3k2
      omega
    have hpowMul : u*2^(n+1)=2*(2^n*u) := by
      rw [hpow]
      ac_rfl
    have h2eq : 2*(3*a+4)=2*(u*2^(n+1)) := by
      calc
        2*(3*a+4) = 6*a+8 := by omega
        _ = 4*(2^n*u) := h6a
        _ = 2*(u*2^(n+1)) := by rw [hpowMul]; omega
    omega
  have hpow3 : (2:Nat)^(n+3)=4*2^(n+1) := by
    have he : n+3=(n+1)+2 := by omega
    rw [he, Nat.pow_add, show (2:Nat)^2=4 by decide]
    ac_rfl
  have hSum3 : 24*S+12*n+6*u=u*2^(n+3)+2 := by
    have hsum3 : 3*(p.1+p.2)+12*n+6*u=3*a+3*(u*2^(n+1))+6 := by omega
    rw [hterm] at hsum3
    have hRhs : 3*a+3*(u*2^(n+1))+6=4*(u*2^(n+1))+2 := by omega
    rw [hRhs] at hsum3
    have hpowMul : u*2^(n+3)=4*(u*2^(n+1)) := by rw [hpow3]; ac_rfl
    rw [← hpowMul] at hsum3
    omega
  have ht : 1≤n/2 := by omega
  have hnform : n=2*(n/2)+1 := by
    have hdiv := Nat.mod_add_div n 2
    omega
  have hpowmod : (2:Nat)^(n+3)%96=64 := by
    rw [hnform]
    exact pow_even_mod96_from4 (n/2) ht
  obtain ⟨w,hpowExact⟩ := exists_eq_64_add_96_mul_of_mod (2^(n+3)) hpowmod
  have hformula :24*S+12*n=u*(58+96*w)+2 := by
    have hmul : u*(64+96*w)=u*(58+96*w)+6*u := by
      rw [Nat.mul_add, Nat.mul_add]
      omega
    rw [hpowExact] at hSum3
    omega
  have hS4 : S%4=3 := oddS_mod4 n u S q w (n/2) hnform huform hformula
  have hcone : ¬ CReach a b :=
    dyadic_six_cone_mass4_no_blank n a b u S (by omega) hu hu4 hb hcong4 hterm
      (by omega) hS4 hSgt
  intro hroot
  exact hcone (hpred.mp hroot)

end BB6.Agent31OddDepthTower
