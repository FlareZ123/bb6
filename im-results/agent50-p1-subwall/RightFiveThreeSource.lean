import RightFiveResetFloor
import RightFiveTwoArithmetic

namespace BB6.Agent50RightFiveThree

open BB6.Agent28 BB6.Agent1UpperTail BB6.Agent1Quarter
open BB6.Agent50ExceptionalDepth BB6.Agent50RightFive
open BB6.Agent50RightFiveTwo

/-- Exact mass conservation along arbitrarily many genuine t=0 inverse steps. -/
theorem upper_tail_mass (b0 d0 m0 b d m r : Nat)
    (h : UpperTail b0 d0 m0 b d m r) :
    b+d+2*m = b0+d0+2*m0 := by
  induction h with
  | root => rfl
  | step b d m r k c hprev hb hb4 hd hi hk hc ih =>
    have hmass := (inverseAt_iff_power_mass b d 0 k c (by omega) hb4 hd).mp hi
    omega

/-- All original-source exceptional right-five inverse histories for n>=14
have at least three positive-depth resets. This is an exact CountCone
statement, without asserting any authentic blank-start halt/nonhalt verdict. -/
theorem source_right_five_needs_three_resets
    (n b m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z) :
    3 ≤ z := by
  have hz2 : 2 ≤ z := source_right_five_needs_two_resets n b m z hn h
  by_cases hthree : 3 ≤ z
  · exact hthree
  · exfalso
    have hz : z=2 := by omega
    obtain ⟨bp,dp,mp,zp,t,k,hpre,hzEq,hip,hb,hkm,hbpPow,hdpPow,
      hcost,henergy,henergyB,hmCost,hdpMin,hexact,hup,hlow,htLow,htUpper⟩ :=
      source_exceptional_last_reset_depth_window n b 5 m z hn (by omega) h rfl
    have hzp : zp=1 := by omega
    have hprefix : CountCone (14*2^n-2*n-16) 3 bp dp mp 1 := by
      simpa only [hzp] using hpre
    have hcostPrefix : mp ≤ 3*n+4 := by
      have he := BB6.Agent43CountedEnergy.source_counted_cost_linear_in_resets
        n bp dp mp 1 hn hprefix
      omega
    have hhundred : 100*n ≤ 2^n := hundred_mul_le_pow n hn
    have hprefixOdd : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
      counted_to_odd_cone _ _ _ _ _ _ hprefix
    have hmass := odd_cone_mass (14*2^n-2*n-16) 3 bp dp mp hprefixOdd
    have hmassExact : bp+dp+2*mp+2*n+13=14*2^n := by omega
    have hbpBound : bp ≤ 14*2^n := by omega
    have hlast : bp+2^(t+3)+4*mp+4*n+20=28*2^n := by omega
    have htEq : t=n+1 := by
      by_cases htle : t≤n
      · have htPow : 2^(t+3) ≤ 2^(n+3) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have hpowN : 2^(n+3)=8*2^n := by
          rw [Nat.pow_add]
          omega
        omega
      · omega
    have hpowN1 : 2^(t+3)=16*2^n := by
      rw [htEq,show n+1+3=n+4 by omega, Nat.pow_add]
      omega
    have hbpEq : bp+4*mp+4*n+20=12*2^n := by omega
    have hbpLarge : 11*2^n ≤ bp := by omega

    obtain ⟨B,D,R,r,u,j,c,s,hupperPre,hB,hB4,hD,hInv,hj,hc,hu,hupperPost⟩ :=
      (cone_shape _ _ bp dp mp 1 hprefix).2 rfl
    have hpreDy := upper_tail_dyadic
      (14*2^n-2*n-16) 3 0 B D R r hupperPre
    have hpreMass := upper_tail_mass
      (14*2^n-2*n-16) 3 0 B D R r hupperPre
    have hpreMassExact : B+D+2*R+2*n+13=14*2^n := by omega
    have hInvFacts := (inverseAt_iff_power_mass B D u j c (by omega) hB4 hD).mp hInv
    have hcOdd : c%2=1 := hc
    have hfirstLeftBound : 2*j+8 ≤ 14*2^n := by omega
    have hpostDy := upper_tail_dyadic
      (2*j-4) (c+4) (R+u+1) bp dp mp s hupperPost
    have hpostPow : 2^s*(bp+12)=2*j+8 := by omega
    have hsZero : s=0 := by
      by_cases hs : s=0
      · exact hs
      · have hspos : 1≤s := by omega
        have hpow : 2 ≤ 2^s := by
          have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hspos
          simpa using hh
        have htwice : 2*(bp+12) ≤ 2^s*(bp+12) :=
          Nat.mul_le_mul_right (bp+12) hpow
        omega
    have hpostRight : dp=c+4 :=
      upper_tail_zero_right _ _ _ _ _ _ _ hupperPost hsZero
    have hpostCost : mp=R+u+1 := by omega
    have hrootCost : R=r := by omega
    have hrmp : r ≤ mp := by omega
    have hrootEq : 2^r*(B+12)+2*n+4=14*2^n := by omega
    have hdpExact : dp=2*2^n+2*mp+2*n+7 := by
      rw [htEq, show n+1+3=n+4 by omega,Nat.pow_add] at hdpPow
      omega
    have hcExact : c+3=2*2^n+2*mp+2*n+6 := by omega
    have hBeven : 2*(B/2)=B := by omega
    have hpowerExact :
        2*(2^u*(c+3))+B+4*r+4*n+20=28*2^n := by
      omega
    exact no_two_reset_last_prefix n r u B mp (c+3) hn hrmp
      hcostPrefix hu hrootEq hpowerExact hcExact

#print axioms BB6.Agent50RightFiveThree.upper_tail_mass
#print axioms BB6.Agent50RightFiveThree.source_right_five_needs_three_resets

end BB6.Agent50RightFiveThree
