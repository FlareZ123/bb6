import DepthIndexedResetFloor
import RightFiveThreeSource

namespace BB6.Agent43DepthResetFloor

open BB6.Agent28 BB6.Agent1UpperTail BB6.Agent1Quarter
open BB6.Agent43LastResetStrength BB6.Agent43LastResetDraft BB6.Agent43CountedEnergy
open BB6.Agent50RightFive BB6.Agent50RightFiveThree

private theorem upper_tail_cost (b0 d0 m0 b d m r : Nat)
    (h : UpperTail b0 d0 m0 b d m r) : m=m0+r := by
  induction h with
  | root => rfl
  | step b d m r k c hprev hb hb4 hd hi hk hc ih => omega

private theorem two_hundred_mul_le_pow (n : Nat) (hn : 14 ≤ n) :
    200*n ≤ 2^n := by
  have hbase : 200*14 ≤ 2^14 := by decide
  have hrec : ∀ k : Nat, 200*(14+k) ≤ 2^(14+k) := by
    intro k
    induction k with
    | zero => exact hbase
    | succ k ih =>
      have hp : 0 < (2:Nat)^(14+k) := Nat.pow_pos (by decide)
      have hidx : 14+(k+1)=(14+k)+1 := by omega
      rw [hidx, Nat.pow_succ]
      omega
  have heq : 14+(n-14)=n := by omega
  simpa [heq] using hrec (n-14)

/-- No genuine two-positive-reset CountCone can lie on the shifted 12*2^n wall.
    The proof peels the last two positive resets, removes their zero-depth
    suffixes using large-left bounds, and traps the first reset's power
    strictly between consecutive dyadic multiples. -/
theorem source_no_two_reset_shifted_wall
    (n b d m : Nat) (hn : 14≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m 2)
    (hwall : b+4*m+4*n+20=12*2^n) : False := by
  let P : Nat := 2^n
  let K : Nat := 14*P-2*n-16
  have hP200 : 200*n≤P := by simpa [P] using two_hundred_mul_le_pow n hn
  have hwallP : b+4*m+4*n+20=12*P := by simpa [P] using hwall
  have hfinalOdd : OddCone K 3 b d m := by
    exact counted_to_odd_cone K 3 b d m 2 (by simpa [K,P] using h)
  have hfinalMass := odd_cone_mass K 3 b d m hfinalOdd
  have hfinalMassExact : b+d+2*m+2*n+13=14*P := by
    dsimp [K] at hfinalMass
    omega
  have hcostAll := source_counted_cost_linear_in_resets n b d m 2 hn
    (by simpa [K,P] using h)
  have hcostAllBound : m≤5*n+7 := by omega
  have hbLarge : 11*P≤b := by omega

  obtain ⟨bp,dp,mp,zp,t2,k2,c2,s2,hpre2,hcount2,hbp2,hbp42,
      hdp2,hi2,hk2,hc2,ht2,htail2⟩ :=
    counted_last_positive_reset K 3 b d m 2 (by simpa [K,P] using h) (by omega)
  have hzp : zp=1 := by omega
  have hpreOne : CountCone K 3 bp dp mp 1 := by simpa [hzp] using hpre2
  have hpreOneOdd : OddCone K 3 bp dp mp :=
    counted_to_odd_cone K 3 bp dp mp 1 hpreOne
  have hpreOneMass := odd_cone_mass K 3 bp dp mp hpreOneOdd
  have hpreOneMassExact : bp+dp+2*mp+2*n+13=14*P := by
    dsimp [K] at hpreOneMass
    omega
  have hInv2 := (inverseAt_iff_power_mass bp dp t2 k2 c2 (by omega) hbp42 hdp2).mp hi2
  have hpost2Dy := upper_tail_dyadic (2*k2-4) (c2+4) (mp+t2+1) b d m s2 htail2
  have hpost2Pow : 2^s2*(b+12)=2*k2+8 := by omega
  have hpost2LeftBound : 2*k2+8≤14*P := by omega
  have hs2Zero : s2=0 := by
    by_cases hs : s2=0
    · exact hs
    · have hspos : 1≤s2 := by omega
      have hpow : 2≤2^s2 := by
        have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hspos
        simpa using hh
      have htwice : 2*(b+12)≤2^s2*(b+12) :=
        Nat.mul_le_mul_right (b+12) hpow
      omega
  have hpost2Right : d=c2+4 :=
    upper_tail_zero_right _ _ _ _ _ _ _ htail2 hs2Zero
  have hpost2Cost0 := upper_tail_cost (2*k2-4) (c2+4) (mp+t2+1) b d m s2 htail2
  have hpost2Cost : m=mp+t2+1 := by omega
  have hpost2Mass := upper_tail_mass (2*k2-4) (c2+4) (mp+t2+1) b d m s2 htail2
  have hpost2Left : b=2*k2-4 := by omega
  have hfinalRight : d=2*P+2*m+2*n+7 := by omega
  have hC2 : c2+3=2*P+2*m+2*n+6 := by omega
  have hcostPrefix := source_counted_cost_linear_in_resets n bp dp mp 1 hn hpreOne
  have hcostPrefixBound : mp≤3*n+4 := by omega
  have ht2le : t2≤2 := by
    have hbpHalf : 2*(bp/2)=bp := by omega
    have hS2Upper : dp+bp/2+3≤14*P := by omega
    have hC2Lower : 2*P≤c2+3 := by omega
    by_cases ht2le : t2≤2
    · exact ht2le
    · have ht3 : 3≤t2 := by omega
    have hpow : 8≤2^t2 := by
      have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ht3
      simpa using hh
    have hmul : 16*P≤2^t2*(c2+3) := by
      have hh := Nat.mul_le_mul_right (c2+3) hpow
      omega
    omega
  have hmBound : m≤3*n+7 := by omega
  have hpowrel2 : 2^(t2+1)=2*2^t2 := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hmulPow : 2^(t2+1)*(c2+3)=2*(2^t2*(c2+3)) := by
    rw [hpowrel2]
    omega
  have hB1wall : bp+4*mp+4*n+20+2^(t2+1)*(c2+3)=28*P := by
    have hbpHalf : 2*(bp/2)=bp := by omega
    omega
  have hbpLarge : 11*P≤bp := by
    by_cases ht2eq : t2=1
    · have hpow : 2^(t2+1)=4 := by simp [ht2eq]
      rw [hpow] at hB1wall
      omega
    · have ht2eq2 : t2=2 := by omega
      have hpow : 2^(t2+1)=8 := by simp [ht2eq2]
      rw [hpow] at hB1wall
      omega

  obtain ⟨B,D,R,r,u,j,c1,s1,hupperPre,hB,hB4,hD,hInv1,hj,hc1,hu,hupperPost⟩ :=
    (cone_shape K 3 bp dp mp 1 hpreOne).2 rfl
  have hpre1Dy := upper_tail_dyadic K 3 0 B D R r hupperPre
  have hpre1Mass := upper_tail_mass K 3 0 B D R r hupperPre
  have hpre1Cost0 := upper_tail_cost K 3 0 B D R r hupperPre
  have hRr : R=r := by omega
  have hpre1MassExact : B+D+2*r+2*n+13=14*P := by
    dsimp [K] at hpre1Mass
    omega
  have hrootEq : 2^r*(B+12)+2*n+4=14*P := by
    dsimp [K] at hpre1Dy
    omega
  have hInv1 := (inverseAt_iff_power_mass B D u j c1 (by omega) hB4 hD).mp hInv1
  have hfirstLeftBound : 2*j+8≤14*P := by omega
  have hpost1Dy := upper_tail_dyadic (2*j-4) (c1+4) (R+u+1) bp dp mp s1 hupperPost
  have hpost1Pow : 2^s1*(bp+12)=2*j+8 := by omega
  have hs1Zero : s1=0 := by
    by_cases hs : s1=0
    · exact hs
    · have hspos : 1≤s1 := by omega
      have hpow : 2≤2^s1 := by
        have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hspos
        simpa using hh
      have htwice : 2*(bp+12)≤2^s1*(bp+12) :=
        Nat.mul_le_mul_right (bp+12) hpow
      omega
  have hpost1Right : dp=c1+4 :=
    upper_tail_zero_right _ _ _ _ _ _ _ hupperPost hs1Zero
  have hpost1Cost0 := upper_tail_cost (2*j-4) (c1+4) (R+u+1) bp dp mp s1 hupperPost
  have hpost1Cost : mp=R+u+1 := by omega
  have hrmp : r≤mp := by omega
  have hBeven : 2*(B/2)=B := by omega
  have hL : D+B/2+3=2^u*(c1+3) := hInv1.1
  have hC1Eq : c1+3+14*P=2^(t2+1)*(c2+3)+2*n+2*mp+6 := by
    have hbpHalf : 2*(bp/2)=bp := by omega
    omega
  have hC1pos : 4≤c1+3 := by omega
  by_cases ht2eq : t2=1
  · have hpow : 2^(t2+1)=4 := by simp [ht2eq]
    rw [hpow] at hC1Eq
    have hC1small : c1+3+6*P≤40*n+86 := by omega
    omega
  · have ht2eq2 : t2=2 := by omega
    have hpow : 2^(t2+1)=8 := by simp [ht2eq2]
    rw [hpow] at hC1Eq
    have hC1Exact : c1+3+14*P=16*P+18*mp+18*n+102 := by omega
    have hC1Lower : 2*P+18*n+102≤c1+3 := by omega
    have hC1Upper : c1+3≤2*P+72*n+174 := by omega
    by_cases hr0 : r=0
    · have hLdouble : 2*(D+B/2+3)+2*n+4=14*P := by omega
      have hgapLow : 4*(c1+3)<2*(D+B/2+3) := by omega
      have hgapHigh : 2*(D+B/2+3)<8*(c1+3) := by omega
      by_cases hu1 : u=1
      · rw [hu1] at hL
        omega
      · have hu2 : 2≤u := by omega
        have hpowU : 4≤2^u := by
          have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hu2
          simpa using hh
        have hmul : 4*(c1+3)≤2^u*(c1+3) := Nat.mul_le_mul_right (c1+3) hpowU
        omega
    · have hrpos : 1≤r := by omega
      have hpowr : 2≤2^r := by
        have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hrpos
        simpa using hh
      have hmulB : 2*(B+12)≤2^r*(B+12) := Nat.mul_le_mul_right (B+12) hpowr
      have hBbound : 2*(B+12)+2*n+4≤14*P := by omega
      have hLlow : 42*P≤4*(D+B/2+3)+30*n+44 := by omega
      have hgapLow : 16*(c1+3)<4*(D+B/2+3) := by omega
      have hLupper : D+B/2+3<14*P := by omega
      have hgapHigh : D+B/2+3<8*(c1+3) := by omega
      by_cases hu2 : u≤2
      · have hpowU : 2^u≤4 := by
          have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hu2
          simpa using hh
        have hmul : 2^u*(c1+3)≤4*(c1+3) := Nat.mul_le_mul_right (c1+3) hpowU
        omega
      · have hu3 : 3≤u := by omega
        have hpowU : 8≤2^u := by
          have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hu3
          simpa using hh
        have hmul : 8*(c1+3)≤2^u*(c1+3) := Nat.mul_le_mul_right (c1+3) hpowU
        omega

#print axioms BB6.Agent43DepthResetFloor.source_no_two_reset_shifted_wall

/-- The depth dichotomy and the shifted-wall exclusion raise the universal
    original-source right-five reset floor from three to four. -/
theorem source_right_five_four_reset_floor_shifted_wall
    (n b m z : Nat) (hn : 14≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z) : 4≤z := by
  by_cases hfour : 4≤z
  · exact hfour
  · have hzThree : z=3 := by
      have hz3 := source_right_five_needs_three_resets n b m z hn h
      omega
    have hP200 : 200*n≤2^n := two_hundred_mul_le_pow n hn
    have hsmall : (2*n+3)*z<3*2^n := by rw [hzThree]; omega
    rcases source_right_five_depth_reset_dichotomy n b m z hn h with hlarge | hprefix
    · omega
    · rcases hprefix with ⟨bp,dp,mp,zp,k,hpre,hzEq,hzp,hip,hb,hkm,hbpExact,hwall,hdpExact,hmEq,hcost⟩
      have hzp2 : zp=2 := by omega
      have hpre2 : CountCone (14*2^n-2*n-16) 3 bp dp mp 2 := by
        simpa [hzp2] using hpre
      exact source_no_two_reset_shifted_wall n bp dp mp hn hpre2 hwall

#print axioms BB6.Agent43DepthResetFloor.source_right_five_four_reset_floor_shifted_wall

end BB6.Agent43DepthResetFloor
