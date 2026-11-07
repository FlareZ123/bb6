import TwoResetWallPrefix
import ThreeResetCore

set_option maxHeartbeats 3000000

namespace BB6.Agent43DepthResetFloor

open BB6.Agent28 BB6.Agent1UpperTail BB6.Agent1Quarter
open BB6.Agent43LastResetStrength BB6.Agent43LastResetDraft BB6.Agent43CountedEnergy
open BB6.Agent50RightFive BB6.Agent50RightFiveThree

private theorem upper_tail_cost_three (b0 d0 m0 b d m r : Nat)
    (h : UpperTail b0 d0 m0 b d m r) : m=m0+r := by
  induction h with
  | root => rfl
  | step b d m r k c hprev hb hb4 hd hi hk hc ih => omega

private theorem source_c1_relation_three
    (bp dp mp n P t2 c2 c1 : Nat)
    (hMass : bp+dp+2*mp+2*n+13=14*P)
    (hPow : dp+bp/2+3=2^t2*(c2+3))
    (hBpHalf : 2*(bp/2)=bp)
    (hDp : dp=c1+4)
    (hMulPow : 2^(t2+1)*(c2+3)=2*(2^t2*(c2+3))) :
    c1+3+14*P=2^(t2+1)*(c2+3)+2*n+2*mp+6 := by
  rw [hMulPow]
  omega

private theorem source_predecessor_wall_relation_three
    (bp dp mp n P t2 c2 : Nat)
    (hMass : bp+dp+2*mp+2*n+13=14*P)
    (hPow : dp+bp/2+3=2^t2*(c2+3))
    (hBpHalf : 2*(bp/2)=bp)
    (hMulPow : 2^(t2+1)*(c2+3)=2*(2^t2*(c2+3))) :
    bp+4*mp+4*n+20+2^(t2+1)*(c2+3)=28*P := by
  rw [hMulPow]
  omega

/-- No original-source three-positive-reset CountCone prefix can lie on the
    shifted 12*2^n wall for n>=14. The proof peels all three genuine positive
    resets, eliminates their zero-depth tails, and finishes with a dyadic gap
    at the root-connected first reset. -/
theorem source_no_three_reset_shifted_wall
    (n b d m : Nat) (hn : 14≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m 3)
    (hwall : b+4*m+4*n+20=12*2^n) : False := by
  let P : Nat := 2^n
  let K : Nat := 14*P-2*n-16
  rcases BB6.ThreeResetCore.three_reset_numeric_bounds n P hn rfl with
    ⟨hP1100,hGap0,hGap1,hGap2,hP14,hFive⟩
  have hP200 : 200*n≤P := by omega
  have hwallP : b+4*m+4*n+20=12*P := by simpa [P] using hwall
  have hfinalOdd : OddCone K 3 b d m :=
    counted_to_odd_cone K 3 b d m 3 (by simpa [K,P] using h)
  have hfinalMass := odd_cone_mass K 3 b d m hfinalOdd
  have hfinalMassExact : b+d+2*m+2*n+13=14*P := by
    dsimp [K] at hfinalMass
    omega
  have hcostAll := source_counted_cost_linear_in_resets n b d m 3 hn
    (by simpa [K,P] using h)
  have hcostAllBound : m≤7*n+10 := by omega
  have hbLarge : 11*P≤b := by omega

  obtain ⟨b2,d2,m2,z2,t3,k3,c3,s3,hpre3,hcount3,hb3,hb43,
      hd3,hi3,hk3,hc3,ht3,htail3⟩ :=
    counted_last_positive_reset K 3 b d m 3
      (by simpa [K,P] using h) (by omega)
  have hz2 : z2=2 := by omega
  have hpre2 : CountCone K 3 b2 d2 m2 2 := by simpa [hz2] using hpre3
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
    have hcost := counted_cost_at_least_twice_resets K 3 b2 d2 m2 2 hpre2
    omega

  have hInv3 := (inverseAt_iff_power_mass b2 d2 t3 k3 c3
    (by omega) hb43 hd3).mp hi3
  have hpost3Dy := upper_tail_dyadic (2*k3-4) (c3+4) (m2+t3+1)
    b d m s3 htail3
  have hpost3Pow : 2^s3*(b+12)=2*k3+8 := by omega
  have hpost3LeftBound : 2*k3+8≤14*P := by omega
  have hs3Zero : s3=0 := by
    by_cases hs : s3=0
    · exact hs
    · have hspos : 1≤s3 := by omega
      have hpow : 2≤2^s3 := by
        have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hspos
        simpa using hh
      have htwice : 2*(b+12)≤2^s3*(b+12) :=
        Nat.mul_le_mul_right (b+12) hpow
      omega
  have hpost3Right : d=c3+4 :=
    upper_tail_zero_right _ _ _ _ _ _ _ htail3 hs3Zero
  have hpost3Cost0 := upper_tail_cost_three (2*k3-4) (c3+4)
    (m2+t3+1) b d m s3 htail3
  have hpost3Cost : m=m2+t3+1 := by omega
  have hpost3Mass := upper_tail_mass (2*k3-4) (c3+4)
    (m2+t3+1) b d m s3 htail3
  have hpost3Left : b=2*k3-4 := by omega
  have hfinalRight : d=2*P+2*m+2*n+7 := by omega
  have hC3 : c3+3=2*P+2*m+2*n+6 := by omega
  have hb2Half : 2*(b2/2)=b2 := by omega
  have hMulPow3 : 2^(t3+1)*(c3+3)=2*(2^t3*(c3+3)) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hwallPre3 := source_predecessor_wall_relation_three b2 d2 m2 n P t3 c3
    hpre2MassExact hInv3.1 hb2Half hMulPow3
  have hS3Upper : d2+b2/2+3≤14*P := by omega
  have hC3Lower : 2*P≤c3+3 := by omega
  have ht3le : t3≤2 := by
    by_cases ht : t3≤2
    · exact ht
    · have ht3 : 3≤t3 := by omega
      have hpow : 8≤2^t3 := by
        have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ht3
        simpa using hh
      have hmul : 16*P≤2^t3*(c3+3) := by
        have hh := Nat.mul_le_mul_right (c3+3) hpow
        omega
      omega
  have ht3one : t3=1 ∨ t3=2 := by omega
  rcases ht3one with ht3eq | ht3eq
  · have hC3one : c3+3=2*P+2*m2+2*n+10 := by
      rw [hpost3Cost, ht3eq] at hC3
      omega
    have hwall2one : b2+4*m2+4*n+20+4*(c3+3)=28*P := by
      rw [show 2^(t3+1)=4 by simp [ht3eq]] at hwallPre3
      exact hwallPre3
    have hD2Bad : d2+6*P=10*m2+10*n+47 := by omega
    have hPBad : 6*P>60*n+117 := by omega
    omega
  · have hC3two : c3+3=2*P+2*m2+2*n+12 := by
      rw [hpost3Cost, ht3eq] at hC3
      omega
    have hB2Exact : b2+20*m2+20*n+116=12*P := by
      rw [show 2^(t3+1)=8 by simp [ht3eq]] at hwallPre3
      omega
    have hD2Exact : d2=2*P+18*m2+18*n+103 := by omega
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
    have hpost2Cost0 := upper_tail_cost_three (2*k2-4) (c2+4)
      (m1+t2+1) b2 d2 m2 s2 htail2
    have hpost2Cost : m2=m1+t2+1 := by omega
    have hpost2Mass := upper_tail_mass (2*k2-4) (c2+4)
      (m1+t2+1) b2 d2 m2 s2 htail2
    have hpost2Left : b2=2*k2-4 := by omega
    have hC2 : c2+3=2*P+18*m2+18*n+102 := by omega
    have hb1Half : 2*(b1/2)=b1 := by omega
    have hMulPow2 : 2^(t2+1)*(c2+3)=2*(2^t2*(c2+3)) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hwallPre2 := source_predecessor_wall_relation_three b1 d1 m1 n P t2 c2
      hpre1MassExact hInv2.1 hb1Half hMulPow2
    have hS2Upper : d1+b1/2+3≤14*P := by omega
    have hC2Lower : 2*P≤c2+3 := by omega
    have ht2le : t2≤2 := by
      by_cases ht : t2≤2
      · exact ht
      · have ht3 : 3≤t2 := by omega
        have hpow : 8≤2^t2 := by
          have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ht3
          simpa using hh
        have hmul : 16*P≤2^t2*(c2+3) := by
          have hh := Nat.mul_le_mul_right (c2+3) hpow
          omega
        omega
    have ht2one : t2=1 ∨ t2=2 := by omega
    rcases ht2one with ht2eq | ht2eq
    · have hwall1one : b1+4*m1+4*n+20+4*(c2+3)=28*P := by
        rw [show 2^(t2+1)=4 by simp [ht2eq]] at hwallPre2
        exact hwallPre2
      have hD1Bad : d1+6*P=74*m2+74*n+411 := by omega
      have hPBad : 6*P>444*n+929 := by omega
      omega
    · have hwall1two : b1+4*m1+4*n+20+8*(c2+3)=28*P := by
        rw [show 2^(t2+1)=8 by simp [ht2eq]] at hwallPre2
        exact hwallPre2
      have hB1Exact : b1+148*m2+148*n+824=12*P := by omega
      have hD1Exact : d1=2*P+146*m2+146*n+817 := by omega
      have hb1Large : 11*P≤b1 := by omega

      obtain ⟨B,D,R,r,u,j,c1,s1,hupperPre,hB,hB4,hD,hInv1,hj,
          hc1,hu,hupperPost⟩ :=
        (cone_shape K 3 b1 d1 m1 1 hpre1).2 rfl
      have hpre1Dy := upper_tail_dyadic K 3 0 B D R r hupperPre
      have hpre1Mass := upper_tail_mass K 3 0 B D R r hupperPre
      have hpre1Cost0 := upper_tail_cost_three K 3 0 B D R r hupperPre
      have hRr : R=r := by omega
      have hrootMassExact : B+D+2*r+2*n+13=14*P := by
        dsimp [K] at hpre1Mass
        omega
      have hrootEq : 2^r*(B+12)+2*n+4=14*P := by
        dsimp [K] at hpre1Dy
        omega
      have hInv1 := (inverseAt_iff_power_mass B D u j c1
        (by omega) hB4 hD).mp hInv1
      have hfirstLeftBound : 2*j+8≤14*P := by omega
      have hpost1Dy := upper_tail_dyadic (2*j-4) (c1+4) (R+u+1)
        b1 d1 m1 s1 hupperPost
      have hpost1Pow : 2^s1*(b1+12)=2*j+8 := by omega
      have hs1Zero : s1=0 := by
        by_cases hs : s1=0
        · exact hs
        · have hspos : 1≤s1 := by omega
          have hpow : 2≤2^s1 := by
            have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hspos
            simpa using hh
          have htwice : 2*(b1+12)≤2^s1*(b1+12) :=
            Nat.mul_le_mul_right (b1+12) hpow
          omega
      have hpost1Right : d1=c1+4 :=
        upper_tail_zero_right _ _ _ _ _ _ _ hupperPost hs1Zero
      have hpost1Cost0 := upper_tail_cost_three (2*j-4) (c1+4)
        (R+u+1) b1 d1 m1 s1 hupperPost
      have hpost1Cost : m1=R+u+1 := by omega
      have hr : r≤m2 := by omega
      have hBeven : 2*(B/2)=B := by omega
      have hL : D+B/2+3=2^u*(c1+3) := hInv1.1
      have hC1Eq := source_c1_relation_three b1 d1 m1 n P t2 c2 c1
        hpre1MassExact hInv2.1 hb1Half hpost1Right hMulPow2
      have hC1 : c1+3=2*P+146*m2+146*n+816 := by
        rw [show 2^(t2+1)=8 by simp [ht2eq], hC2] at hC1Eq
        omega
      exact BB6.ThreeResetCore.no_three_reset_root_power
        n P m2 r B D (c1+3) (D+B/2+3) u hn hm2Lower hcost2Bound hr
        hC1 rfl hL hu hrootMassExact hrootEq hBeven
        hGap0 hGap1 hGap2 hP14 hFive

#print axioms BB6.Agent43DepthResetFloor.source_no_three_reset_shifted_wall

/-- The depth dichotomy and the three-reset shifted-wall exclusion raise the
    original-source right-five reset floor from four to five. -/
theorem source_right_five_five_reset_floor_shifted_wall
    (n b m z : Nat) (hn : 14≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z) : 5≤z := by
  have hnum := BB6.ThreeResetCore.three_reset_numeric_bounds n (2^n) hn rfl
  have hP1100 : 1100*n≤2^n := hnum.1
  by_cases hfive : 5≤z
  · exact hfive
  · have hfour := source_right_five_four_reset_floor_shifted_wall n b m z hn h
    have hzFour : z=4 := by omega
    have hsmall : (2*n+3)*z<3*2^n := by rw [hzFour]; omega
    rcases source_right_five_depth_reset_dichotomy n b m z hn h with hlarge | hprefix
    · omega
    · rcases hprefix with ⟨bp,dp,mp,zp,k,hpre,hzEq,hzp,hip,hb,hkm,
        hbpExact,hwall,hdpExact,hmEq,hcost⟩
      have hzpThree : zp=3 := by omega
      have hpreThree : CountCone (14*2^n-2*n-16) 3 bp dp mp 3 := by
        simpa [hzpThree] using hpre
      exact False.elim (source_no_three_reset_shifted_wall n bp dp mp hn hpreThree hwall)

#print axioms BB6.Agent43DepthResetFloor.source_right_five_five_reset_floor_shifted_wall

end BB6.Agent43DepthResetFloor