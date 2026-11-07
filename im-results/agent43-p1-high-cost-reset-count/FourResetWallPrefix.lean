import DepthIndexedResetFloor
import ThreeResetWallPrefix
import FourResetCore

set_option maxHeartbeats 5000000

namespace BB6.Agent43DepthResetFloor

open BB6.Agent28 BB6.Agent1UpperTail BB6.Agent1Quarter
open BB6.Agent43LastResetStrength BB6.Agent43LastResetDraft BB6.Agent43CountedEnergy
open BB6.Agent50RightFive BB6.Agent50RightFiveThree

private theorem source_predecessor_wall_relation_four
    (bp dp mp n P t c : Nat)
    (hMass : bp+dp+2*mp+2*n+13=14*P)
    (hPow : dp+bp/2+3=2^t*(c+3))
    (hBpHalf : 2*(bp/2)=bp)
    (hMulPow : 2^(t+1)*(c+3)=2*(2^t*(c+3))) :
    bp+4*mp+4*n+20+2^(t+1)*(c+3)=28*P := by
  rw [hMulPow]
  omega

private theorem upper_tail_one_right
    (b0 d0 m0 b d m : Nat)
    (h : UpperTail b0 d0 m0 b d m 1) :
    d=d0+b0/2+4 := by
  cases h with
  | root => omega
  | step b' d' m' r k c hprev hb hb4 hd hi hk hc =>
    have hr : r=0 := by omega
    subst r
    cases hprev with
    | root =>
      have hzero := inv0_halve b0 d0 k c hi hk
      omega

/-- No original-source four-positive-reset CountCone prefix can lie on the
exact shifted 12*2^n wall for n>=14. The proof peels all four positive resets,
removes each following zero-depth tail, and closes the final root-connected
one-reset cases by the kernel-checked arithmetic in FourResetCore. -/
theorem source_no_four_reset_shifted_wall
    (n b d m : Nat) (hn : 14≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m 4)
    (hwall : b+4*m+4*n+20=12*2^n) : False := by
  let P : Nat := 2^n
  let K : Nat := 14*P-2*n-16
  rcases BB6.ThreeResetCore.three_reset_numeric_bounds n P hn rfl with
    ⟨hP1100,hGap0,hGap1,hGap2,hP14,hFive⟩
  have hwallP : b+4*m+4*n+20=12*P := by simpa [P] using hwall
  have hfinalOdd : OddCone K 3 b d m :=
    counted_to_odd_cone K 3 b d m 4 (by simpa [K,P] using h)
  have hfinalMass := odd_cone_mass K 3 b d m hfinalOdd
  have hfinalMassExact : b+d+2*m+2*n+13=14*P := by
    dsimp [K] at hfinalMass
    omega
  have hcostAll := source_counted_cost_linear_in_resets n b d m 4 hn
    (by simpa [K,P] using h)
  have hcostAllBound : m≤9*n+13 := by omega
  have hbLarge : 11*P≤b := by omega

  obtain ⟨b3,d3,m3,z3,t4,k4,c4,s4,hpre3Raw,hcount3,hb3,hb34,
      hd3,hi4,hk4,hc4,ht4,htail4⟩ :=
    counted_last_positive_reset K 3 b d m 4
      (by simpa [K,P] using h) (by omega)
  have hz3 : z3=3 := by omega
  have hpre3 : CountCone K 3 b3 d3 m3 3 := by simpa [hz3] using hpre3Raw
  have hpre3Odd : OddCone K 3 b3 d3 m3 :=
    counted_to_odd_cone K 3 b3 d3 m3 3 hpre3
  have hpre3Mass := odd_cone_mass K 3 b3 d3 m3 hpre3Odd
  have hpre3MassExact : b3+d3+2*m3+2*n+13=14*P := by
    dsimp [K] at hpre3Mass
    omega
  have hcost3 := source_counted_cost_linear_in_resets n b3 d3 m3 3 hn
    (by simpa [K,P] using hpre3)
  have hcost3Bound : m3≤7*n+10 := by omega

  have hInv4 := (inverseAt_iff_power_mass b3 d3 t4 k4 c4
    (by omega) hb34 hd3).mp hi4
  have hpost4Dy := upper_tail_dyadic (2*k4-4) (c4+4) (m3+t4+1)
    b d m s4 htail4
  have hpost4Pow : 2^s4*(b+12)=2*k4+8 := by omega
  have hpost4LeftBound : 2*k4+8≤14*P := by omega
  have hs4Zero : s4=0 := by
    by_cases hs : s4=0
    · exact hs
    · have hspos : 1≤s4 := by omega
      have hpow : 2≤2^s4 := by
        have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hspos
        simpa using hh
      have htwice : 2*(b+12)≤2^s4*(b+12) :=
        Nat.mul_le_mul_right (b+12) hpow
      omega
  have hpost4Right : d=c4+4 :=
    upper_tail_zero_right _ _ _ _ _ _ _ htail4 hs4Zero
  have hpost4Cost : m=m3+t4+1 := by omega
  have hfinalRight : d=2*P+2*m+2*n+7 := by omega
  have hC4 : c4+3=2*P+2*m+2*n+6 := by omega
  have hb3Half : 2*(b3/2)=b3 := by omega
  have hMulPow4 : 2^(t4+1)*(c4+3)=2*(2^t4*(c4+3)) := by
    rw [Nat.pow_succ]
    ac_rfl
  have hwallPre4 := source_predecessor_wall_relation_four b3 d3 m3 n P t4 c4
    hpre3MassExact hInv4.1 hb3Half hMulPow4
  have hS4Upper : d3+b3/2+3≤14*P := by omega
  have hC4Lower : 2*P≤c4+3 := by omega
  have ht4le : t4≤2 := by
    by_cases ht : t4≤2
    · exact ht
    · have ht3 : 3≤t4 := by omega
      have hpow : 8≤2^t4 := by
        have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ht3
        simpa using hh
      have hmul : 16*P≤2^t4*(c4+3) := by
        have h8 : 16*P≤8*(c4+3) := Nat.mul_le_mul_left 8 hC4Lower
        have hpowmul : 8*(c4+3)≤2^t4*(c4+3) :=
          Nat.mul_le_mul_right (c4+3) hpow
        exact Nat.le_trans h8 hpowmul
      omega
  have ht4Cases : t4=1 ∨ t4=2 := by omega
  rcases ht4Cases with ht4eq | ht4eq
  · have hC4one : c4+3=2*P+2*m3+2*n+10 := by
      rw [hpost4Cost, ht4eq] at hC4
      omega
    have hpow4 : 2^(t4+1)=4 := by simp [ht4eq]
    have hwallPre4one : b3+4*m3+4*n+20+4*(c4+3)=28*P := by
      rw [hpow4] at hwallPre4
      exact hwallPre4
    have hD3Bad : d3+6*P=10*m3+10*n+47 := by omega
    have hPBad : 6*P>80*n+147 := by omega
    omega
  · have hC4two : c4+3=2*P+2*m3+2*n+12 := by
      rw [hpost4Cost, ht4eq] at hC4
      omega
    have hpow4 : 2^(t4+1)=8 := by simp [ht4eq]
    have hB3Exact : b3+20*m3+20*n+116=12*P := by
      rw [hpow4] at hwallPre4
      omega
    have hD3Exact : d3=2*P+18*m3+18*n+103 := by omega
    have hb3Large : 11*P≤b3 := by omega

    obtain ⟨b2,d2,m2,z2,t3,k3,c3,s3,hpre2Raw,hcount2,hb2,hb24,
        hd2,hi3,hk3,hc3,ht3,htail3⟩ :=
      counted_last_positive_reset K 3 b3 d3 m3 3 hpre3 (by omega)
    have hz2 : z2=2 := by omega
    have hpre2 : CountCone K 3 b2 d2 m2 2 := by simpa [hz2] using hpre2Raw
    have hpre2Odd : OddCone K 3 b2 d2 m2 :=
      counted_to_odd_cone K 3 b2 d2 m2 2 hpre2
    have hpre2Mass := odd_cone_mass K 3 b2 d2 m2 hpre2Odd
    have hpre2MassExact : b2+d2+2*m2+2*n+13=14*P := by
      dsimp [K] at hpre2Mass
      omega
    have hcost2 := source_counted_cost_linear_in_resets n b2 d2 m2 2 hn
      (by simpa [K,P] using hpre2)
    have hcost2Bound : m2≤5*n+7 := by omega
    have hm2Lower : 4≤m2 := by
      have hcount := counted_cost_at_least_twice_resets K 3 b2 d2 m2 2 hpre2
      omega

    have hInv3 := (inverseAt_iff_power_mass b2 d2 t3 k3 c3
      (by omega) hb24 hd2).mp hi3
    have hpost3Dy := upper_tail_dyadic (2*k3-4) (c3+4) (m2+t3+1)
      b3 d3 m3 s3 htail3
    have hpost3Pow : 2^s3*(b3+12)=2*k3+8 := by omega
    have hpost3LeftBound : 2*k3+8≤14*P := by omega
    have hs3Zero : s3=0 := by
      by_cases hs : s3=0
      · exact hs
      · have hspos : 1≤s3 := by omega
        have hpow : 2≤2^s3 := by
          have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hspos
          simpa using hh
        have htwice : 2*(b3+12)≤2^s3*(b3+12) :=
          Nat.mul_le_mul_right (b3+12) hpow
        omega
    have hpost3Right : d3=c3+4 :=
      upper_tail_zero_right _ _ _ _ _ _ _ htail3 hs3Zero
    have hpost3Cost : m3=m2+t3+1 := by omega
    have hC3 : c3+3=2*P+18*m3+18*n+102 := by omega
    have hb2Half : 2*(b2/2)=b2 := by omega
    have hMulPow3 : 2^(t3+1)*(c3+3)=2*(2^t3*(c3+3)) := by
      rw [Nat.pow_succ]
      ac_rfl
    have hwallPre3 := source_predecessor_wall_relation_four b2 d2 m2 n P t3 c3
      hpre2MassExact hInv3.1 hb2Half hMulPow3
    have hS3Upper : d2+b2/2+3≤14*P := by omega
    have hC3Lower : 2*P≤c3+3 := by omega
    have ht3le : t3≤2 := by
      by_cases ht : t3≤2
      · exact ht
      · have htLarge : 3≤t3 := by omega
        have hpow : 8≤2^t3 := by
          have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) htLarge
          simpa using hh
        have h8 : 16*P≤8*(c3+3) := Nat.mul_le_mul_left 8 hC3Lower
        have hpowmul : 8*(c3+3)≤2^t3*(c3+3) :=
          Nat.mul_le_mul_right (c3+3) hpow
        have hmul : 16*P≤2^t3*(c3+3) := Nat.le_trans h8 hpowmul
        omega
    have ht3Cases : t3=1 ∨ t3=2 := by omega
    rcases ht3Cases with ht3eq | ht3eq
    · have hC3one : c3+3=2*P+18*m2+18*n+138 := by
        rw [hpost3Cost, ht3eq] at hC3
        omega
      have hpow3 : 2^(t3+1)=4 := by simp [ht3eq]
      have hwallPre3one : b2+4*m2+4*n+20+4*(c3+3)=28*P := by
        rw [hpow3] at hwallPre3
        exact hwallPre3
      have hD2Bad : d2+6*P=74*m2+74*n+559 := by omega
      have hPBad : 6*P>444*n+1077 := by omega
      omega
    · have hC3two : c3+3=2*P+18*m2+18*n+156 := by
        rw [hpost3Cost, ht3eq] at hC3
        omega
      have hpow3 : 2^(t3+1)=8 := by simp [ht3eq]
      have hB2Exact : b2+148*m2+148*n+1268=12*P := by
        rw [hpow3] at hwallPre3
        omega
      have hD2Exact : d2=2*P+146*m2+146*n+1255 := by omega
      have hb2Large : 11*P≤b2 := by omega

      obtain ⟨b1,d1,m1,z1,t2,k2,c2,s2,hpre1Raw,hcount1,hb1,hb14,
          hd1,hi2,hk2,hc2,ht2,htail2⟩ :=
        counted_last_positive_reset K 3 b2 d2 m2 2 hpre2 (by omega)
      have hz1 : z1=1 := by omega
      have hpre1 : CountCone K 3 b1 d1 m1 1 := by simpa [hz1] using hpre1Raw
      have hpre1Odd : OddCone K 3 b1 d1 m1 :=
        counted_to_odd_cone K 3 b1 d1 m1 1 hpre1
      have hpre1Mass := odd_cone_mass K 3 b1 d1 m1 hpre1Odd
      have hpre1MassExact : b1+d1+2*m1+2*n+13=14*P := by
        dsimp [K] at hpre1Mass
        omega
      have hcost1 := source_counted_cost_linear_in_resets n b1 d1 m1 1 hn
        (by simpa [K,P] using hpre1)
      have hcost1Bound : m1≤3*n+4 := by omega

      have hInv2 := (inverseAt_iff_power_mass b1 d1 t2 k2 c2
        (by omega) hb14 hd1).mp hi2
      have hpost2Dy := upper_tail_dyadic (2*k2-4) (c2+4) (m1+t2+1)
        b2 d2 m2 s2 htail2
      have hpost2Pow : 2^s2*(b2+12)=2*k2+8 := by omega
      have hpost2LeftBound : 2*k2+8≤14*P := by omega
      have hs2Zero : s2=0 := by
        by_cases hs : s2=0
        · exact hs
        · have hspos : 1≤s2 := by omega
          have hpow : 2≤2^s2 := by
            have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hspos
            simpa using hh
          have htwice : 2*(b2+12)≤2^s2*(b2+12) :=
            Nat.mul_le_mul_right (b2+12) hpow
          omega
      have hpost2Right : d2=c2+4 :=
        upper_tail_zero_right _ _ _ _ _ _ _ htail2 hs2Zero
      have hpost2Cost : m2=m1+t2+1 := by omega
      have hC2 : c2+3=2*P+146*m2+146*n+1254 := by omega
      have hb1Half : 2*(b1/2)=b1 := by omega
      have hMulPow2 : 2^(t2+1)*(c2+3)=2*(2^t2*(c2+3)) := by
        rw [Nat.pow_succ]
        ac_rfl
      have hwallPre2 := source_predecessor_wall_relation_four b1 d1 m1 n P t2 c2
        hpre1MassExact hInv2.1 hb1Half hMulPow2
      have hS2Upper : d1+b1/2+3≤14*P := by omega
      have hC2Lower : 2*P≤c2+3 := by omega
      have ht2le : t2≤2 := by
        by_cases ht : t2≤2
        · exact ht
        · have htLarge : 3≤t2 := by omega
          have hpow : 8≤2^t2 := by
            have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) htLarge
            simpa using hh
          have h8 : 16*P≤8*(c2+3) := Nat.mul_le_mul_left 8 hC2Lower
          have hpowmul : 8*(c2+3)≤2^t2*(c2+3) :=
            Nat.mul_le_mul_right (c2+3) hpow
          have hmul : 16*P≤2^t2*(c2+3) := Nat.le_trans h8 hpowmul
          omega
      have ht2Cases : t2=1 ∨ t2=2 := by omega
      rcases ht2Cases with ht2eq | ht2eq
      · have hC2one : c2+3=2*P+146*m1+146*n+1546 := by
          rw [hpost2Cost, ht2eq] at hC2
          omega
        have hpow2 : 2^(t2+1)=4 := by simp [ht2eq]
        have hwallPre2one : b1+4*m1+4*n+20+4*(c2+3)=28*P := by
          rw [hpow2] at hwallPre2
          exact hwallPre2
        have hD1Bad : d1+6*P=586*m1+586*n+6191 := by omega
        have hPBad : 6*P>2344*n+8535 := by omega
        omega
      · have hC2two : c2+3=2*P+146*m1+146*n+1692 := by
          rw [hpost2Cost, ht2eq] at hC2
          omega
        have hpow2 : 2^(t2+1)=8 := by simp [ht2eq]
        have hB1Exact : b1+1172*m1+1172*n+13556=12*P := by
          rw [hpow2] at hwallPre2
          omega
        have hD1Exact : d1=2*P+1170*m1+1170*n+13543 := by omega
        have hb1Large : 6*P≤b1 := by omega

        obtain ⟨B,D,R,r,u,j,c1,s1,hupperPre,hB,hB4,hD,hInv1,hj,
            hc1,hu,hupperPost⟩ :=
          (cone_shape K 3 b1 d1 m1 1 hpre1).2 rfl
        have hpre1Dy := upper_tail_dyadic K 3 0 B D R r hupperPre
        have hpre1Mass := upper_tail_mass K 3 0 B D R r hupperPre
        have hrootCost : R=r := by omega
        have hrootMassExact : B+D+2*r+2*n+13=14*P := by
          dsimp [K] at hpre1Mass
          omega
        have hrootEq : 2^r*(B+12)+2*n+4=14*P := by
          dsimp [K] at hpre1Dy
          omega
        have hrootMassR : B+D+2*R+2*n+13=14*P := by
          simpa [hrootCost] using hrootMassExact
        have hrootEqR : 2^R*(B+12)+2*n+4=14*P := by
          simpa [hrootCost] using hrootEq
        have hInv1Facts := (inverseAt_iff_power_mass B D u j c1
          (by omega) hB4 hD).mp hInv1
        have hfirstLeftBound : 2*j+8≤14*P := by omega
        have hpost1Dy := upper_tail_dyadic (2*j-4) (c1+4) (R+u+1)
          b1 d1 m1 s1 hupperPost
        have hpost1Pow : 2^s1*(b1+12)=2*j+8 := by omega
        have hs1Le : s1≤1 := by
          by_cases hs : s1≤1
          · exact hs
          · have hs2 : 2≤s1 := by omega
            have hpow : 4≤2^s1 := by
              have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hs2
              simpa using hh
            have hmul : 4*(b1+12)≤2^s1*(b1+12) :=
              Nat.mul_le_mul_right (b1+12) hpow
            omega
        have hpost1Cost : m1=R+u+1+s1 := by omega
        have hL : D+B/2+3=2^u*(c1+3) := hInv1Facts.1
        have hBeven : 2*(B/2)=B := by omega
        have hs1Cases : s1=0 ∨ s1=1 := by omega
        rcases hs1Cases with hs1Zero | hs1One
        · have hpost1Right : d1=c1+4 :=
            upper_tail_zero_right _ _ _ _ _ _ _ hupperPost hs1Zero
          have hC1 : c1+3=2*P+1170*m1+1170*n+13542 := by omega
          have hm1Lower : 2≤m1 := by omega
          exact BB6.Agent43FourResetCore.no_four_reset_root_zero_tail
            n P m1 r B D (c1+3) (D+B/2+3) u hn rfl hB4
            hrootMassExact hrootEq rfl hInv1Facts.1 hC1
            hm1Lower hcost1Bound hu
        · have hpost1OneRight := upper_tail_one_right
            (2*j-4) (c1+4) (R+u+1) b1 d1 m1 hupperPost
          have hRight : d1=c1+j+6 := by omega
          have hpost1PowOne : 2*(b1+12)=2*j+8 := by
            simpa [hs1One] using hpost1Pow
          have hpost1CostOne : m1=R+u+2 := by omega
          have hm1Bound : m1≤2*n+3 := by
            have hbound := BB6.Agent43FourResetCore.one_tail_prefix_cost_bound
              n P B D R u c1 hn rfl hrootMassR hrootEqR
              hInv1Facts.1 hc1
            omega
          exact BB6.Agent43FourResetCore.no_four_reset_root_one_tail
            n P b1 d1 m1 j c1 hn rfl hm1Bound hpre1MassExact
            hD1Exact hpost1PowOne hRight

/-- The depth dichotomy plus the four-reset shifted-wall exclusion raises
original-source right-five histories from five to six positive-depth resets. -/
theorem source_right_five_six_reset_floor_shifted_wall
    (n b m z : Nat) (hn : 14≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z) : 6≤z := by
  have hfive := source_right_five_five_reset_floor_shifted_wall n b m z hn h
  by_cases hsix : 6≤z
  · exact hsix
  · have hzFive : z=5 := by omega
    have hnum := BB6.ThreeResetCore.three_reset_numeric_bounds n (2^n) hn rfl
    have hP1100 : 1100*n≤2^n := hnum.1
    have hsmall : (2*n+3)*z<3*2^n := by rw [hzFive]; omega
    rcases source_right_five_depth_reset_dichotomy n b m z hn h with hlarge | hprefix
    · omega
    · rcases hprefix with ⟨bp,dp,mp,zp,k,hpre,hzEq,hzp,hip,hb,hkm,
        hbpExact,hwall,hdpExact,hmEq,hcost⟩
      have hzpFour : zp=4 := by omega
      have hpreFour : CountCone (14*2^n-2*n-16) 3 bp dp mp 4 := by
        simpa [hzpFour] using hpre
      exact False.elim (source_no_four_reset_shifted_wall n bp dp mp hn hpreFour hwall)

#print axioms BB6.Agent43DepthResetFloor.source_no_four_reset_shifted_wall
#print axioms BB6.Agent43DepthResetFloor.source_right_five_six_reset_floor_shifted_wall

end BB6.Agent43DepthResetFloor
