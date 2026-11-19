import ShadowGraphConverse

namespace BB6.Shadow
open BB6.Agent1Quarter
open BB6.Agent47P1
open BB6.P1Reduction

private theorem wide_self_add_one_le_two_pow (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

private theorem wide_pow_two_injective (j k : Nat) (h : 2^j = 2^k) : j = k := by
  by_cases hlt : j < k
  · have hp := Nat.pow_lt_pow_right (show 1 < (2:Nat) by decide) hlt
    omega
  · by_cases hgt : k < j
    · have hp := Nat.pow_lt_pow_right (show 1 < (2:Nat) by decide) hgt
      omega
    · omega

/-- The extra size invariant needed for the wide finite-word converse.
    The root-size hypothesis is preserved because every legal shadow
    quotient has positive residual r, including r=1. -/
theorem shadow_reach_size_invariant_wide
    (L z0 m z : Nat)
    (hL : 8≤L) (hz0 : 0<z0) (hw0 : z0+4≤L)
    (hrootSize : L≤2*z0+1)
    (h : ShadowReach L z0 m z) :
    L+m≤2*z+1 := by
  induction h with
  | root =>
      exact hrootSize
  | @step m z t r zp hprev hdiv hnext ih =>
      have hz : 0<z :=
        (shadow_reach_invariants L z0 m z hL hz0 hw0 hprev).1
      have hr : 0<r := by
        rw [hdiv] at hz
        omega
      omega

/-- A wide-window terminal node needs only 4-divisibility of its
    original left counter. The stronger lower bound is recovered locally
    at every node from which another inverse edge is constructed. -/
private theorem shadow_encoded_left_divisible_wide
    (N M m w alpha b : Nat)
    (hK : 2≤N-M) (hm : m≤M) (ha : 28≤alpha)
    (hcoord : 2^m*(b+4*w)=alpha*2^N) :
    b%4=0 := by
  have hmN : m≤N := by omega
  have henc : b+4*w=alpha*2^(N-m) := by
    have h := unscale_coordinate N m b w alpha hmN hcoord
    simpa using h
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
  exact Nat.dvd_iff_mod_eq_zero.mp hbDiv

private theorem wide_s_bound
    (A K t : Nat) (hA : 28≤A) (hK : 2≤K) :
    6*2^t≤A*2^K*(2^t-1)+10 := by
  have hpowK : 4≤2^K := by
    calc
      4=2^2 := by decide
      _ ≤2^K :=
        Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hK
  have hcoeff : 112≤A*2^K := by
    calc
      112=28*4 := by norm_num
      _ ≤A*2^K := Nat.mul_le_mul hA hpowK
  by_cases ht0 : t=0
  · simp [ht0]
  · have htpos : 1≤t := by omega
    have hpowT : 2≤2^t := by
      have h := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) htpos
      norm_num at h
      exact h
    have hterm :
        112*(2^t-1)≤A*2^K*(2^t-1) :=
      Nat.mul_le_mul_right (2^t-1) hcoeff
    omega

/-- Wide finite-word converse. If K=N-M is at least two and
    L+M+7≤A*2^K, with A≥28 and the root-size invariant L≤2*z0+1,
    then every feeder-rooted ShadowReach path of cost at most M lifts
    to the authentic original-source OddCone. The final node is required
    only to have b%4=0; b≥12 is proved at each actual parent edge. -/
theorem shadow_reach_lifts_to_odd_cone_of_wide_window
    (N L z0 w0 A alpha0 b0 d0 M m z : Nat)
    (hLlo : N+8≤L)
    (hK : 2≤N-M)
    (hwide : L+M+7≤A*2^(N-M))
    (hrootSize : L≤2*z0+1)
    (hrootOff : L=w0+z0) (hrootW : 4≤w0) (hrootZ : 0<z0)
    (hrootMass : b0+d0+2*L+3=56*2^N)
    (hrootCoord : b0+4*w0=alpha0*2^N)
    (hb0 : 12≤b0) (hb04 : b0%4=0) (hd0 : d0%2=1)
    (hA : 28≤A) (hAlpha0 : A≤alpha0) (hAlpha0lt : alpha0<56)
    (hgraph : ShadowReach L z0 m z) (hm : m≤M) :
    ∃ b d alpha,
      OddCone b0 d0 b d m ∧ b%4=0 ∧ d%2=1 ∧
      A≤alpha ∧ alpha<56*2^m ∧
      2^m*(b+4*(L+m-z))=alpha*2^N := by
  have hL8 : 8≤L := by omega
  have hw0 : z0+4≤L := by omega
  revert hm
  induction hgraph with
  | root =>
      intro hm
      refine ⟨b0,d0,alpha0,OddCone.root,hb04,hd0,hAlpha0,?_,?_⟩
      · simpa using hAlpha0lt
      · have hrootWcalc : L-z0=w0 := by omega
        simp only [Nat.pow_zero,Nat.one_mul,Nat.add_zero]
        rw [hrootWcalc]
        exact hrootCoord
  | @step m z t r zp hprev hdiv hnext ih =>
      intro hm
      have hmParent : m≤M := by omega
      have hmChild : m+t+1≤M := by omega
      obtain ⟨b,d,alpha,hcone,hb4,hd,haLo,haHi,hcoord⟩ :=
        ih hmParent
      have hconeMass := odd_cone_mass b0 d0 b d m hcone
      have hmass : b+d+2*m+2*L+3=56*2^N := by omega
      have hprevInv := shadow_reach_invariants L z0 m z hL8 hrootZ hw0 hprev
      rcases hprevInv with ⟨hz,hzmargin⟩
      have hprevSize :=
        shadow_reach_size_invariant_wide L z0 m z hL8 hrootZ hw0 hrootSize hprev
      let w := L+m-z
      have hw4 : 4≤w := by dsimp [w]; omega
      have hoff : L+m=w+z := by dsimp [w]; omega
      have hsizeBound : 2*w+6≤A*2^(N-M) := by
        have h2w : 2*w+6≤L+M+7 := by
          dsimp [w]
          omega
        exact Nat.le_trans h2w hwide
      have hrne : r≠0 := by
        intro hr0
        rw [hr0] at hdiv
        simp at hdiv
        omega
      have hrpos : 1≤r := by omega
      have hpowle : 2^t≤z := by
        rw [hdiv]
        have hmul := Nat.mul_le_mul_left (2^t) hrpos
        simpa using hmul
      have hNmt : N-M+t+1≤N-m := by omega
      have hpowmono : 2^(N-M+t+1)≤2^(N-m) :=
        Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hNmt
      have hmN : m≤N := by omega
      have henc : b+4*w=alpha*2^(N-m) := by
        have h := unscale_coordinate N m b w alpha hmN (by simpa [w] using hcoord)
        simpa [w] using h
      have hpowRewrite :
          A*2^(N-M+t+1)=2*A*2^(N-M)*2^t := by
        calc
          A*2^(N-M+t+1)
              = A*(2^(N-M)*2^(t+1)) := by
                  rw [show N-M+t+1=(N-M)+(t+1) by omega, Nat.pow_add]
          _ = A*(2^(N-M)*(2^t*2)) := by rw [Nat.pow_succ]
          _ = 2*A*2^(N-M)*2^t := by ring
      have hlarge1 : A*2^(N-M+t+1)≤alpha*2^(N-m) := by
        calc
          A*2^(N-M+t+1)≤A*2^(N-m) :=
            Nat.mul_le_mul_left A hpowmono
          _ ≤alpha*2^(N-m) :=
            Nat.mul_le_mul_right (2^(N-m)) haLo
      have hlarge : 2*A*2^(N-M)*2^t≤b+4*w := by
        calc
          2*A*2^(N-M)*2^t=A*2^(N-M+t+1) := hpowRewrite.symm
          _ ≤alpha*2^(N-m) := hlarge1
          _ =b+4*w := henc.symm
      have hpowT1 : 1≤2^t := Nat.one_le_pow _ _ (by decide)
      have hsafe : m+t+3≤N := by omega
      have h4w : 4*w+12≤2*A*2^(N-M) := by omega
      have hprodLower :
          2*A*2^(N-M)≤2*A*2^(N-M)*2^t := by
        have h := Nat.mul_le_mul_left (2*A*2^(N-M)) hpowT1
        simpa using h
      have hb12 : 12≤b := by omega
      have hbeven : b%2=0 := by omega
      have hhalfEq : b+4*w=2*(b/2+2*w) := by omega
      have hhalfLarge : A*2^(N-M)*2^t≤b/2+2*w := by
        have hlargeHalf : 2*(A*2^(N-M)*2^t)≤b+4*w := by
          calc
            2*(A*2^(N-M)*2^t)=2*A*2^(N-M)*2^t := by ring
            _ ≤b+4*w := hlarge
        rw [hhalfEq] at hlargeHalf
        omega
      have hsplit :
          A*2^(N-M)*2^t =
            A*2^(N-M)*(2^t-1)+A*2^(N-M) := by
        calc
          A*2^(N-M)*2^t =
              A*2^(N-M)*((2^t-1)+1) := by
                congr 1
                omega
          _ = A*2^(N-M)*(2^t-1)+A*2^(N-M) := by
                rw [Nat.mul_add]
                simp
      have hBhalf : A*2^(N-M)*(2^t-1)+6≤b/2 := by
        rw [hsplit] at hhalfLarge
        omega
      let s := d+b/2+3
      obtain ⟨Q,hQ⟩ := encoded_shift_divisible N L m t b d w z alpha
        hmass hoff henc hbeven hsafe
      have hdivS : 2^t∣s := by
        have h1 : 2^t∣s+2*z := by
          refine ⟨4*Q,?_⟩
          calc
            s+2*z=2^(t+2)*Q := by simpa [s] using hQ
            _=2^t*(4*Q) := by
              rw [Nat.pow_add]
              change (2^t*4)*Q=2^t*(4*Q)
              ac_rfl
        have h2 : 2^t∣2*z := by
          refine ⟨2*r,?_⟩
          rw [hdiv]
          simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
        have h := Nat.dvd_sub h1 h2
        simpa using h
      obtain ⟨C,hC⟩ := hdivS
      have hCfactor : 2^t*(C+2*r)=2^t*(4*Q) := by
        calc
          2^t*(C+2*r)=2^t*C+2^t*(2*r) := by rw [Nat.mul_add]
          _ =s+2*(2^t*r) := by
            rw [←hC]
            congr 1
            simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          _ =s+2*z := by rw [←hdiv]
          _ =2^(t+2)*Q := by simpa [s] using hQ
          _ =2^t*(4*Q) := by
            rw [Nat.pow_add]
            change (2^t*4)*Q=2^t*(4*Q)
            ac_rfl
      have hpowPosT : 0<2^t := Nat.two_pow_pos t
      have hCeq : C+2*r=4*Q := Nat.mul_left_cancel hpowPosT hCfactor
      have hCdiv2 : 2∣C := by
        have h1 : 2∣C+2*r := by
          rw [hCeq]
          exact ⟨2*Q,by omega⟩
        have h2 : 2∣2*r := ⟨r,rfl⟩
        have h := Nat.dvd_sub h1 h2
        simpa using h
      have hCeven : C%2=0 := Nat.dvd_iff_mod_eq_zero.mp hCdiv2
      have hS6 : 6*2^t≤s := by
        have hdpos : 1≤d := by omega
        have hbase := wide_s_bound A (N-M) t hA hK
        dsimp [s]
        omega
      have hC6 : 6≤C := by
        by_cases hCsmall : 6≤C
        · exact hCsmall
        · have hC5 : C≤5 := by omega
          have hmul : 2^t*C≤2^t*5 := Nat.mul_le_mul_left (2^t) hC5
          rw [←hC] at hmul
          omega
      let c := C-3
      have hc3 : 3≤c := by dsimp [c]; omega
      have hcodd : c%2=1 := by dsimp [c]; omega
      have hcplus : c+3=C := by dsimp [c]; omega
      have hpower : d+b/2+3=2^t*(c+3) := by
        calc
          d+b/2+3=s := by rfl
          _=2^t*C := hC
          _=2^t*(c+3) := by rw [hcplus]
      have hAnc : ∃ k, GAncestor b d k c :=
        (ancestor_exists_iff_power b d c (by omega) hb4).2 ⟨t,hpower⟩
      obtain ⟨k,hAncK⟩ := hAnc
      obtain ⟨t',hi',_⟩ := inverseAt_complete b d k c hAncK
      have hp' := inverseAt_power b d t' k c hi'
      have hpowEq : 2^t=2^t' :=
        Nat.eq_of_mul_eq_mul_right (by omega : 0<c+3) (hpower.symm.trans hp')
      have hdepth : t=t' := wide_pow_two_injective t t' hpowEq
      subst t'
      have hk2 := inverseAt_left_ge_two b d t k c hb12 hb4 hi'
      have hpoly := original_odd_edge_polynomial N L m t b d w z alpha k c r zp b0 d0
        hcone hrootMass hoff hcoord (by omega) hb4 hd hi' hcodd hdiv hnext
      have hmargin := shadow_step_preserves_offset L m z t r zp hL8 hz hzmargin hdiv hnext
      have hzpBound : zp≤L+m+t+1 := by omega
      have hnat := shadow_poly_cast N L m t k zp alpha hk2 hzpBound hpoly
      let m' := m+t+1
      let alpha' := alpha+112*2^m*(2^t-1)
      have hm' : m'≤M := by dsimp [m']; omega
      have hm'N : m'≤N := by omega
      have hAlphaLo' : A≤alpha' := by dsimp [alpha']; omega
      have hMulShift :
          112*2^m*(2^t-1)+112*2^m=112*2^m*2^t := by
        calc
          112*2^m*(2^t-1)+112*2^m
              =112*2^m*((2^t-1)+1) := by rw [Nat.mul_add]; simp
          _=112*2^m*2^t := by congr 1; omega
      have hId : alpha'+112*2^m=alpha+112*2^m*2^t := by
        calc
          alpha'+112*2^m
              =alpha+(112*2^m*(2^t-1)+112*2^m) := by dsimp [alpha']; omega
          _=alpha+112*2^m*2^t := by rw [hMulShift]
      have hR : 56*2^(m+t+1)=112*2^m*2^t := by
        rw [show m+t+1=m+(t+1) by omega, Nat.pow_add, Nat.pow_succ]
        have h56 : 56*2=112 := by decide
        calc
          56*(2^m*(2^t*2))=(56*2)*(2^m*2^t) := by ac_rfl
          _=112*(2^m*2^t) := by rw [h56]
          _=112*2^m*2^t := by ac_rfl
      have hAlphaHi' : alpha'<56*2^m' := by
        dsimp [m']
        rw [hR]
        have hAold : alpha<112*2^m := by omega
        omega
      have hcoord' :
          2^m'*((2*k-4)+4*(L+m'-zp))=alpha'*2^N := by
        simpa [m',alpha',Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hnat
      have hw' : 4≤L+m'-zp := by dsimp [m']; omega
      have hb4' :=
        shadow_encoded_left_divisible_wide N M m' (L+m'-zp) alpha' (2*k-4)
          hK hm' (Nat.le_trans hA hAlphaLo') hcoord'
      have hd' : (c+4)%2=1 := by omega
      refine ⟨2*k-4,c+4,alpha',
        OddCone.parent b d m t k c hcone (by omega) hb4 hd hi' hk2 hcodd,
        hb4',hd',hAlphaLo',hAlphaHi',?_⟩
      simpa [m'] using hcoord'

/-- L0 finite-word converse with the coefficient 28 wide window. -/
theorem l0_bounded_shadow_word_has_source_of_wide_window
    (q M u m z : Nat)
    (hK : 2≤16*q-M)
    (hwide : 16*q+8+M+7≤28*2^(16*q-M))
    (hu : u+4*q+3=7*2^(16*q))
    (hgraph : ShadowReach (16*q+8) (12*q+4) m z)
    (hm : m≤M) :
    ∃ b d alpha,
      OddCone (4*u-4) (4*u+9) b d m ∧
      b%4=0 ∧ d%2=1 ∧ 28≤alpha ∧ alpha<56*2^m ∧
      2^m*(b+4*(16*q+8+m-z))=alpha*2^(16*q) := by
  have hpow := wide_self_add_one_le_two_pow (16*q)
  have hmul := Nat.mul_le_mul_left 7 hpow
  have hu4 : 4≤u := by omega
  have hu1 : 1≤u := by omega
  obtain ⟨hmass,hcoord,_,_⟩ :=
    two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  have h := shadow_reach_lifts_to_odd_cone_of_wide_window
    (16*q) (16*q+8) (12*q+4) (4*q+4) 28 28 (4*u-4) (4*u+9) M m z
    (by omega) hK hwide (by omega) (by omega) (by omega)
    hmass hcoord (by omega) (by omega) (by omega) (by decide) (by rfl)
    (by omega) hm
  simpa using h

/-- L1 finite-word converse with the stronger coefficient 42 window. -/
theorem l1_bounded_shadow_word_has_source_of_wide_window
    (q M u m z : Nat)
    (hK : 2≤16*q-M)
    (hwide : 16*q+9+M+7≤42*2^(16*q-M))
    (hu : u+4*q+3=7*2^(16*q))
    (hgraph : ShadowReach (16*q+9) (10*q+4) m z)
    (hm : m≤M) :
    ∃ b d alpha,
      OddCone (6*u-2) (2*u+5) b d m ∧
      b%4=0 ∧ d%2=1 ∧ 42≤alpha ∧ alpha<56*2^m ∧
      2^m*(b+4*(16*q+9+m-z))=alpha*2^(16*q) := by
  have hpow := wide_self_add_one_le_two_pow (16*q)
  have hmul := Nat.mul_le_mul_left 7 hpow
  have hu4 : 4≤u := by omega
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
  have h := shadow_reach_lifts_to_odd_cone_of_wide_window
    (16*q) (16*q+9) (10*q+4) (6*q+5) 42 42 (6*u-2) (2*u+5) M m z
    (by omega) hK hwide (by omega) (by omega) (by omega)
    hmass hcoord (by omega) (by omega) (by omega) (by omega) (by rfl)
    (by omega) hm
  simpa using h

#print axioms shadow_reach_size_invariant_wide
#print axioms shadow_encoded_left_divisible_wide
#print axioms shadow_reach_lifts_to_odd_cone_of_wide_window
#print axioms l0_bounded_shadow_word_has_source_of_wide_window
#print axioms l1_bounded_shadow_word_has_source_of_wide_window

end BB6.Shadow
