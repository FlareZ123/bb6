import P1FiniteInverse
import P1InverseLog
import ShadowGraphFeeders
import ShadowDepthArithmetic
import ShadowCast

namespace BB6.Shadow
open BB6.Agent1Quarter
open BB6.Agent47P1

private theorem pow_two_injective (j k : Nat) (h : 2^j = 2^k) : j = k := by
  by_cases hlt : j < k
  · have hp := Nat.pow_lt_pow_right (show 1 < (2:Nat) by decide) hlt
    omega
  · by_cases hgt : k < j
    · have hp := Nat.pow_lt_pow_right (show 1 < (2:Nat) by decide) hgt
      omega
    · omega

/-- A source inverse started at b>=12 cannot return a left coordinate below 2. -/
theorem inverseAt_left_ge_two (b d t k c : Nat)
    (hb : 12 ≤ b) (hb4 : b%4=0)
    (hi : inverseAt b d t = some (k,c)) : 2 ≤ k := by
  induction t generalizing k c with
  | zero =>
      simp only [inverseAt] at hi
      rw [if_pos ⟨by omega, hb4⟩] at hi
      obtain ⟨hk,hc⟩ := Prod.mk.inj (Option.some.inj hi)
      omega
  | succ t ih =>
      simp only [inverseAt] at hi
      split at hi
      · simp at hi
      · next k0 c0 heq =>
        split at hi
        · next hcond =>
          obtain ⟨hk,hc⟩ := Prod.mk.inj (Option.some.inj hi)
          have hprev := ih k0 c0 heq
          omega
        · simp at hi

private theorem self_add_one_le_two_pow (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

private theorem three_mul_add4_le_two_pow (k : Nat) (hk : 4 ≤ k) :
    3*k+4 ≤ 2^k := by
  have aux : ∀ n : Nat, 4 ≤ n → 3*n+4 ≤ 2^n := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
        by_cases hbase : n+1=4
        · have hnEq : n=3 := by omega
          subst n
          norm_num
        · have hn4 : 4 ≤ n := by omega
          have hp := ih hn4
          rw [Nat.pow_succ]
          omega
  exact aux k hk

/-- For N>=2M+7 and L<=N+9, the parameter width dominates every
    shadow coordinate of cost at most M. -/
theorem shadow_width_bound (N L M : Nat)
    (hN : 2*M+7 ≤ N) (hL : L ≤ N+9) :
    L+M ≤ 2^(N-M-3) := by
  have hK : M+4 ≤ N-M-3 := by omega
  have hthree := three_mul_add4_le_two_pow (N-M-3) (by omega)
  have hlin : L+M ≤ 3*(N-M-3)+4 := by omega
  exact le_trans hlin hthree

/-- The four-unit interior offset is invariant along every abstract shadow path. -/
theorem shadow_reach_invariants
    (L z0 m z : Nat) (hL : 8 ≤ L)
    (hz0 : 0 < z0) (hw0 : z0+4 ≤ L)
    (h : ShadowReach L z0 m z) :
    0 < z ∧ z+4 ≤ L+m := by
  induction h with
  | root =>
      exact ⟨hz0,hw0⟩
  | @step m z t r zp hprev hdiv hnext ih =>
      exact shadow_step_preserves_offset L m z t r zp hL ih.1 ih.2 hdiv hnext

private theorem width_forces_exponent (N L M : Nat)
    (hLlo : N+8 ≤ L)
    (hwidth : L+M ≤ 2^(N-M-3)) :
    4 ≤ N-M-3 := by
  by_contra hnot
  have hKle : N-M-3 ≤ 3 := by omega
  have hpow : 2^(N-M-3) ≤ 8 := by
    calc
      2^(N-M-3) ≤ 2^3 :=
        Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hKle
      _ = 8 := by norm_num
  have hlin : N-M-3+11 ≤ L+M := by omega
  omega

/-- Exact source-coordinate encoding of an abstract node forces a very
    large, 4-divisible original left counter. -/
theorem shadow_encoded_left_properties
    (N L M m z alpha b : Nat)
    (hLlo : N+8 ≤ L)
    (hwidth : L+M ≤ 2^(N-M-3))
    (hm : m ≤ M) (hz : 0 < z)
    (hw : 4 ≤ L+m-z) (ha : 28 ≤ alpha)
    (hcoord : 2^m*(b+4*(L+m-z))=alpha*2^N) :
    440*2^(N-M-4) ≤ b ∧ 12 ≤ b ∧ b%4=0 := by
  let w := L+m-z
  have hK4 := width_forces_exponent N L M hLlo hwidth
  have hmN : m ≤ N := by omega
  have henc : b+4*w=alpha*2^(N-m) := by
    have h := unscale_coordinate N m b w alpha hmN (by simpa [w] using hcoord)
    simpa [w] using h
  have hwle : w ≤ L+M := by dsimp [w]; omega
  have hpowmono : 2^(N-M) ≤ 2^(N-m) :=
    Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
  have hprod1 : 28*2^(N-M) ≤ 28*2^(N-m) :=
    Nat.mul_le_mul_left 28 hpowmono
  have hprod2 : 28*2^(N-m) ≤ alpha*2^(N-m) :=
    Nat.mul_le_mul_right (2^(N-m)) ha
  have hprod : 28*2^(N-M) ≤ alpha*2^(N-m) := le_trans hprod1 hprod2
  have hpow16 : 2^(N-M)=16*2^(N-M-4) := by
    rw [show N-M=(N-M-4)+4 by omega, Nat.pow_add]
    norm_num [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have hpow2 : 2^(N-M-3)=2*2^(N-M-4) := by
    rw [show N-M-3=(N-M-4)+1 by omega, Nat.pow_succ]
    simp [Nat.mul_comm]
  have h4w : 4*w ≤ 8*2^(N-M-4) := by
    calc
      4*w ≤ 4*(L+M) := Nat.mul_le_mul_left 4 hwle
      _ ≤ 4*2^(N-M-3) := Nat.mul_le_mul_left 4 hwidth
      _ = 8*2^(N-M-4) := by rw [hpow2]; omega
  have hprodStrong : 448*2^(N-M-4) ≤ alpha*2^(N-m) := by
    rw [hpow16] at hprod
    norm_num [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] at hprod
    exact hprod
  have hbStrong : 440*2^(N-M-4) ≤ b := by
    rw [←henc] at hprodStrong
    omega
  have hpowPos : 1 ≤ 2^(N-M-4) := Nat.one_le_pow _ _ (by decide)
  have hb12 : 12 ≤ b := by
    have h440 : 440 ≤ 440*2^(N-M-4) := Nat.mul_le_mul_left 440 hpowPos
    omega
  have hpowDiv2 : 2^2 ∣ 2^(N-m) := Nat.pow_dvd_pow 2 (by omega)
  have hpowDiv4 : 4 ∣ 2^(N-m) := by simpa using hpowDiv2
  have hmulDiv : 4 ∣ alpha*2^(N-m) := by
    obtain ⟨v,hv⟩ := hpowDiv4
    refine ⟨alpha*v, ?_⟩
    rw [hv]
    simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have hplusDiv : 4 ∣ b+4*w := by rw [henc]; exact hmulDiv
  have htailDiv : 4 ∣ 4*w := ⟨w,rfl⟩
  have hbDiv : 4 ∣ b := by
    have h := Nat.dvd_sub hplusDiv htailDiv
    simpa using h
  have hbmod : b%4=0 := Nat.dvd_iff_mod_eq_zero.mp hbDiv
  exact ⟨hbStrong,hb12,hbmod⟩

/-- Converse to the bounded source-to-shadow simulation:
    every abstract feeder-rooted shadow path of total cost <=M is an
    authentic original-source OddCone path under the direct width bound.

    This is a finite-word statement; it does not give a lift uniform in
    unbounded cost at fixed N, nor blank-root forward reachability. -/
theorem shadow_reach_lifts_to_odd_cone_of_width
    (N L z0 w0 alpha0 b0 d0 M m z : Nat)
    (hLlo : N+8 ≤ L)
    (hwidth : L+M ≤ 2^(N-M-3))
    (hrootOff : L=w0+z0) (hrootW : 4≤w0) (hrootZ : 0<z0)
    (hrootMass : b0+d0+2*L+3=56*2^N)
    (hrootCoord : b0+4*w0=alpha0*2^N)
    (hb0 : 12≤b0) (hb04 : b0%4=0) (hd0 : d0%2=1)
    (ha0 : 28≤alpha0) (ha0lt : alpha0<56)
    (hgraph : ShadowReach L z0 m z) (hm : m≤M) :
    ∃ b d alpha,
      OddCone b0 d0 b d m ∧ 12≤b ∧ b%4=0 ∧ d%2=1 ∧
      28≤alpha ∧ alpha<56*2^m ∧
      2^m*(b+4*(L+m-z))=alpha*2^N := by
  have hK4 := width_forces_exponent N L M hLlo hwidth
  have hL8 : 8≤L := by omega
  have hw0 : z0+4≤L := by omega
  revert hm
  induction hgraph with
  | root =>
      intro hm
      refine ⟨b0,d0,alpha0,OddCone.root,hb0,hb04,hd0,ha0,?_,?_⟩
      · simpa using ha0lt
      · have hrootWcalc : L+0-z0=w0 := by omega
        simpa [hrootWcalc] using hrootCoord
  | @step m z t r zp hprev hdiv hnext ih =>
      intro hm
      have hmParent : m≤M := by omega
      obtain ⟨b,d,alpha,hcone,hb12,hb4,hd,haLo,haHi,hcoord⟩ := ih hmParent
      have hprevInv := shadow_reach_invariants L z0 m z hL8 hrootZ hw0 hprev
      rcases hprevInv with ⟨hz,hzmargin⟩
      let w := L+m-z
      have hw4 : 4≤w := by dsimp [w]; omega
      have hoff : L+m=w+z := by dsimp [w]; omega
      have hrpos : 1≤r := by
        by_contra h
        have hr0 : r=0 := by omega
        subst r
        simp at hdiv
        omega
      have hpowle : 2^t≤z := by
        rw [hdiv]
        have hmul := Nat.mul_le_mul_left (2^t) hrpos
        simpa using hmul
      have hzlt : z<2^(N-M-3) := by
        have hzLM : z<L+M := by omega
        exact lt_of_lt_of_le hzLM hwidth
      have htBound : t≤N-M-4 := by
        by_contra hnot
        have hle : N-M-3≤t := by omega
        have hpow : 2^(N-M-3)≤2^t :=
          Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hle
        omega
      have hsafe : m+t+3≤N := by omega
      have hmN : m≤N := by omega
      have henc : b+4*w=alpha*2^(N-m) := by
        have h := unscale_coordinate N m b (L+m-z) alpha hmN (by simpa using hcoord)
        simpa [w] using h
      have hconeMass := odd_cone_mass b0 d0 b d m hcone
      have hmass : b+d+2*m+2*L+3=56*2^N := by omega
      have hbeven : b%2=0 := by omega
      obtain ⟨hbStrong,_,_⟩ :=
        shadow_encoded_left_properties N L M m z alpha b hLlo hwidth hmParent hz hw4 haLo hcoord
      have hBhalf : 220*2^(N-M-4)≤b/2 := by
        have hbEven : b=2*(b/2) := by omega
        omega
      let s := d+b/2+3
      obtain ⟨Q,hQ⟩ := encoded_shift_divisible N L m t b d w z alpha
        hmass hoff henc hbeven hsafe
      have hdivS : 2^t∣s := by
        have h1 : 2^t∣s+2*z := by
          refine ⟨4*Q, ?_⟩
          calc
            s+2*z = 2^(t+2)*Q := by simpa [s] using hQ
            _ = 2^t*(4*Q) := by
              rw [Nat.pow_add]
              norm_num [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
        have h2 : 2^t∣2*z := by
          refine ⟨2*r, ?_⟩
          rw [hdiv]
          simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
        have h := Nat.dvd_sub h1 h2
        simpa using h
      obtain ⟨C,hC⟩ := hdivS
      have hCfactor : 2^t*(C+2*r)=2^t*(4*Q) := by
        calc
          2^t*(C+2*r)=2^t*C+2^t*(2*r) := by rw [Nat.mul_add]
          _ = s+2*(2^t*r) := by
            rw [←hC]
            congr 1
            simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          _ = s+2*z := by rw [←hdiv]
          _ = 2^(t+2)*Q := by simpa [s] using hQ
          _ = 2^t*(4*Q) := by
            rw [Nat.pow_add]
            norm_num [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      have hpowPosT : 0<2^t := Nat.two_pow_pos t
      have hCeq : C+2*r=4*Q := Nat.mul_left_cancel hpowPosT hCfactor
      have hCdiv2 : 2∣C := by
        have h1 : 2∣C+2*r := by
          rw [hCeq]
          exact ⟨2*Q, by omega⟩
        have h2 : 2∣2*r := ⟨r,rfl⟩
        have h := Nat.dvd_sub h1 h2
        simpa using h
      have hCeven : C%2=0 := Nat.dvd_iff_mod_eq_zero.mp hCdiv2
      have hpowT : 2^t≤2^(N-M-4) :=
        Nat.pow_le_pow_right (by decide : 0<(2:Nat)) htBound
      have hS6 : 6*2^t≤s := by
        have hmul1 : 6*2^t≤6*2^(N-M-4) := Nat.mul_le_mul_left 6 hpowT
        have hmul2 : 6*2^(N-M-4)≤220*2^(N-M-4) := by omega
        have hdpos : 1≤d := by omega
        dsimp [s]
        omega
      have hC6 : 6≤C := by
        by_contra hlt
        have hC5 : C≤5 := by omega
        have hmul : 2^t*C≤2^t*5 := Nat.mul_le_mul_left (2^t) hC5
        rw [←hC] at hmul
        have hpowPosT : 0<2^t := Nat.two_pow_pos t
        omega
      let c := C-3
      have hc3 : 3≤c := by dsimp [c]; omega
      have hcodd : c%2=1 := by dsimp [c]; omega
      have hcplus : c+3=C := by dsimp [c]; omega
      have hpower : d+b/2+3=2^t*(c+3) := by
        calc
          d+b/2+3 = s := by rfl
          _ = 2^t*C := hC
          _ = 2^t*(c+3) := by rw [hcplus]
      have hAnc : ∃ k, GAncestor b d k c :=
        (ancestor_exists_iff_power b d c (by omega) hb4).2 ⟨t,hpower⟩
      obtain ⟨k,hAncK⟩ := hAnc
      obtain ⟨t',hi',_⟩ := inverseAt_complete b d k c hAncK
      have hp' := inverseAt_power b d t' k c hi'
      have hpowEq : 2^t=2^t' :=
        Nat.eq_of_mul_eq_mul_right (by omega : 0<c+3) (hpower.symm.trans hp')
      have hdepth : t=t' := pow_two_injective t t' hpowEq
      subst t'
      have hk2 := inverseAt_left_ge_two b d t k c hb12 hb4 hi'
      have hpoly := original_odd_edge_polynomial N L m t b d w z alpha k c r zp b0 d0
        hcone hrootMass hoff hcoord hb12 hb4 hd hi' hcodd hdiv hnext
      have hmargin := shadow_step_preserves_offset L m z t r zp hL8 hz hzmargin hdiv hnext
      have hzpBound : zp≤L+m+t+1 := by omega
      have hnat := shadow_poly_cast N L m t k zp alpha hk2 hzpBound hpoly
      let m' := m+t+1
      let alpha' := alpha+112*2^m*(2^t-1)
      have hm' : m'≤M := by dsimp [m']; omega
      have hm'N : m'≤N := by omega
      have hAlphaLo' : 28≤alpha' := by dsimp [alpha']; omega
      have hMulShift :
          112*2^m*(2^t-1)+112*2^m=112*2^m*2^t := by
        calc
          112*2^m*(2^t-1)+112*2^m
              =112*2^m*((2^t-1)+1) := by rw [Nat.mul_add]; simp
          _ =112*2^m*2^t := by congr 1; omega
      have hId : alpha'+112*2^m=alpha+112*2^m*2^t := by
        calc
          alpha'+112*2^m
              =alpha+(112*2^m*(2^t-1)+112*2^m) := by dsimp [alpha']; omega
          _ =alpha+112*2^m*2^t := by rw [hMulShift]
      have hR : 56*2^(m+t+1)=112*2^m*2^t := by
        rw [show m+t+1=m+(t+1) by omega, Nat.pow_add, Nat.pow_succ]
        simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      have hAlphaHi' : alpha'<56*2^m' := by
        dsimp [m']
        rw [hR]
        have hA : alpha<112*2^m := by omega
        omega
      have hcoord' :
          2^m'*((2*k-4)+4*(L+m'-zp))=alpha'*2^N := by
        simpa [m',alpha',Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hnat
      have hw' : 4≤L+m'-zp := by dsimp [m']; omega
      have hchildProps := shadow_encoded_left_properties N L M m' zp alpha' (2*k-4)
        hLlo hwidth hm' hmargin.1 hw' hAlphaLo' hcoord'
      rcases hchildProps with ⟨hbStrong',hb12',hb4'⟩
      have hd' : (c+4)%2=1 := by omega
      refine ⟨2*k-4,c+4,alpha',
        OddCone.parent b d m t k c hcone (by omega) hb4 hd hi' hk2 hcodd,
        hb12',hb4',hd',hAlphaLo',hAlphaHi',?_⟩
      simpa [m'] using hcoord'

/-- The simple linear budget N>=2M+7 implies the exact width
    hypothesis needed by the finite-word converse. -/
theorem shadow_reach_lifts_to_odd_cone
    (N L z0 w0 alpha0 b0 d0 M m z : Nat)
    (hN : 2*M+7 ≤ N)
    (hLlo : N+8 ≤ L) (hLhi : L ≤ N+9)
    (hrootOff : L=w0+z0) (hrootW : 4≤w0) (hrootZ : 0<z0)
    (hrootMass : b0+d0+2*L+3=56*2^N)
    (hrootCoord : b0+4*w0=alpha0*2^N)
    (hb0 : 12≤b0) (hb04 : b0%4=0) (hd0 : d0%2=1)
    (ha0 : 28≤alpha0) (ha0lt : alpha0<56)
    (hgraph : ShadowReach L z0 m z) (hm : m≤M) :
    ∃ b d alpha,
      OddCone b0 d0 b d m ∧ 12≤b ∧ b%4=0 ∧ d%2=1 ∧
      28≤alpha ∧ alpha<56*2^m ∧
      2^m*(b+4*(L+m-z))=alpha*2^N := by
  have hwidth := shadow_width_bound N L M hN hLhi
  exact shadow_reach_lifts_to_odd_cone_of_width
    N L z0 w0 alpha0 b0 d0 M m z hLlo hwidth
    hrootOff hrootW hrootZ hrootMass hrootCoord hb0 hb04 hd0 ha0 ha0lt
    hgraph hm

/-- The L0 feeder's every finite shadow word of cost <=M has an
    authentic original-source OddCone realization whenever 16q>=2M+7. -/
theorem l0_bounded_shadow_word_has_source
    (q M u m z : Nat)
    (hN : 2*M+7≤16*q)
    (hu : u+4*q+3=7*2^(16*q))
    (hgraph : ShadowReach (16*q+8) (12*q+4) m z)
    (hm : m≤M) :
    ∃ b d alpha,
      OddCone (4*u-4) (4*u+9) b d m ∧
      12≤b ∧ b%4=0 ∧ d%2=1 ∧ 28≤alpha ∧ alpha<56*2^m ∧
      2^m*(b+4*(16*q+8+m-z))=alpha*2^(16*q) := by
  have hu4 : 4≤u := by
    have hpow := self_add_one_le_two_pow (16*q)
    have hmul := Nat.mul_le_mul_left 7 hpow
    omega
  have hu1 : 1≤u := by omega
  obtain ⟨hmass,hcoord,_,_⟩ :=
    two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  have h := shadow_reach_lifts_to_odd_cone
    (16*q) (16*q+8) (12*q+4) (4*q+4) 28 (4*u-4) (4*u+9) M m z
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hmass hcoord (by omega) (by omega) (by omega) (by omega) (by omega)
    hgraph hm
  simpa using h

/-- The L1 feeder's every finite shadow word of cost <=M has an
    authentic original-source OddCone realization whenever 16q>=2M+7. -/
theorem l1_bounded_shadow_word_has_source
    (q M u m z : Nat)
    (hN : 2*M+7≤16*q)
    (hu : u+4*q+3=7*2^(16*q))
    (hgraph : ShadowReach (16*q+9) (10*q+4) m z)
    (hm : m≤M) :
    ∃ b d alpha,
      OddCone (6*u-2) (2*u+5) b d m ∧
      12≤b ∧ b%4=0 ∧ d%2=1 ∧ 28≤alpha ∧ alpha<56*2^m ∧
      2^m*(b+4*(16*q+9+m-z))=alpha*2^(16*q) := by
  have hu4 : 4≤u := by
    have hpow := self_add_one_le_two_pow (16*q)
    have hmul := Nat.mul_le_mul_left 7 hpow
    omega
  have hu1 : 1≤u := by omega
  have huOdd : u%2=1 := by
    have hexp : 16*q=(16*q-1)+1 := by omega
    have hpowEven : (2^(16*q))%2=0 := by
      rw [hexp,Nat.pow_succ]
      simp [Nat.mul_mod]
    have heven : (u+4*q+3)%2=0 := by
      rw [hu]
      simp [Nat.mul_mod,hpowEven]
    omega
  obtain ⟨_,_,hmass,hcoord⟩ :=
    two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  have h := shadow_reach_lifts_to_odd_cone
    (16*q) (16*q+9) (10*q+4) (6*q+5) 42 (6*u-2) (2*u+5) M m z
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hmass hcoord (by omega) (by omega) (by omega) (by omega) (by omega)
    hgraph hm
  simpa using h

#print axioms shadow_width_bound
#print axioms shadow_encoded_left_properties
#print axioms shadow_reach_lifts_to_odd_cone_of_width
#print axioms shadow_reach_lifts_to_odd_cone
#print axioms l0_bounded_shadow_word_has_source
#print axioms l1_bounded_shadow_word_has_source

end BB6.Shadow
