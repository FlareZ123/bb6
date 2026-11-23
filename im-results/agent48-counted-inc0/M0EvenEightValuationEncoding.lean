import M0EvenEightValuationSuffix
import CountedReset
import S1Encoder
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48M0EvenEightValuationEncoding

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48M0EvenEightValuationSuffix
open BB6ChampionArithmetic

/-- Factor q as oddPart * 2^t, with the exact residual BinDec length. -/
theorem factor8q (L q : Nat) (hL : 4 ≤ L)
    (hq : 0 < q) (hbound : 8*q < 2^L) :
    ∃ u t len, q = (2*u+1)*2^t ∧
      L = len+1+(t+3) ∧ u < 2^len := by
  have hpow : 2^L = 8 * 2^(L-3) := by
    calc
      2^L = 2^((L-3)+3) := by congr 1 <;> omega
      _ = 2^(L-3) * 2^3 := Nat.pow_add 2 (L-3) 3
      _ = 8 * 2^(L-3) := by
        rw [show (2:Nat)^3 = 8 by decide, Nat.mul_comm]
  have hlt : 8*q < 8*2^(L-3) := by simpa [hpow] using hbound
  have hqBound : q < 2^(L-3) := by omega
  obtain ⟨u,t,len,hfactor,hlen,hu⟩ :=
    exists_odd_factor_bounded (L-3) q hq hqBound
  refine ⟨u,t,len,hfactor,?_,hu⟩
  omega

private theorem factor8q_num (u t : Nat) (q : Nat)
    (hfactor : q = (2*u+1)*2^t) :
    8*q = (2*u+1)*2^(t+3) := by
  have hpow3 : 2^(t+3) = 8*2^t := by
    calc
      2^(t+3) = 2^t * 2^3 := Nat.pow_add 2 t 3
      _ = 8*2^t := by
        rw [show (2:Nat)^3 = 8 by decide, Nat.mul_comm]
  calc
    8*q = 8*((2*u+1)*2^t) := by rw [hfactor]
    _ = (2*u+1)*(8*2^t) := by
      calc
        8*((2*u+1)*2^t) = (8*(2*u+1))*2^t := by rw [← Nat.mul_assoc]
        _ = ((2*u+1)*8)*2^t := by rw [Nat.mul_comm 8 (2*u+1)]
        _ = (2*u+1)*(8*2^t) := by rw [Nat.mul_assoc]
    _ = (2*u+1)*2^(t+3) := by rw [← hpow3]

/-- The full source left word exposes the first 3+t d1 blocks for every q>0. -/
theorem s1LeftFacing_8q_all (L q a : Nat)
    (hL : 4 ≤ L) (hq : 0 < q) (hbound : 8*q < 2^L) :
    ∃ u t len, q = (2*u+1)*2^t ∧
      L = len+1+(t+3) ∧ u < 2^len ∧
      s1LeftFacing L (8*q) 0 a 0 =
        d1pow a ++ markerWord 0 ++ d0 ++ d1pow (t+3) ++
          d0 ++ binDec len u ++ lh := by
  obtain ⟨u,t,len,hfactor,hlen,hu⟩ := factor8q L q hL hq hbound
  have hnum := factor8q_num u t q hfactor
  have hlen' : L = len+1+(t+3) := hlen
  have hbin : binDec L (8*q) =
      d1pow (t+3) ++ d0 ++ binDec len u := by
    rw [hlen',hnum]
    exact binDec_carryPrefix len u (t+3) hu
  refine ⟨u,t,len,hfactor,hlen,hu,?_⟩
  unfold s1LeftFacing
  rw [binDec_zero, hbin]
  simp [List.append_assoc]

/-- The generalized q4 left-facing word expands to d0^(4+t), then d1,
with the same residual BinDec tail. -/
theorem q4LeftFacingAll_expanded (L q a : Nat)
    (hL : 4 ≤ L) (hq : 0 < q) (hbound : 8*q < 2^L) :
    ∃ u t len, q = (2*u+1)*2^t ∧
      L = len+1+(t+3) ∧ u < 2^len ∧
      m0EvenEightQ4LeftFacingAll L q a =
        [true] ++ d1pow (a-1) ++ markerWord 2 ++
          d0pow (t+4) ++ d1 ++ binDec len u ++ lh := by
  obtain ⟨u,t,len,hfactor,hlen,hu⟩ := factor8q L q hL hq hbound
  have hnum := factor8q_num u t q hfactor
  have hbin : binDec L (8*q-1) =
      d0pow (t+3) ++ d1 ++ binDec len u := by
    rw [hlen,hnum]
    exact binDec_sub_one_carryPrefix len u (t+3) hu
  refine ⟨u,t,len,hfactor,hlen,hu,?_⟩
  unfold m0EvenEightQ4LeftFacingAll
  rw [hbin]
  have hlenD : t+4 = (t+3)+1 := by omega
  rw [hlenD]
  simp [d0pow,List.append_assoc]


/-- The first 14 cells after the unary counter are valuation-independent:
marker 0, d0, then the first three d1 blocks. -/
theorem sourceLeftFixedPrefix14 (t : Nat) (tail : List Bool) :
    (markerWord 0 ++ d0 ++ d1pow (3+t) ++ tail).take 14 =
      markerWord 0 ++ d0 ++ d1pow 3 := by
  have hsplit : d1pow (3+t) = d1pow 3 ++ d1pow t := by
    simpa [Nat.add_comm] using BB6Coverage.Agent8Q4Suffix.d1pow_add_right t 3
  have hlen : 9 ≤ (d1pow (3+t)).length := by
    simp [d1pow_length]
    omega
  simp [markerWord,d0,List.take_append,hsplit,d1pow_length,hlen]

/-- The encoder's odd-factor exponent is exactly the valuation used by reset cost. -/
theorem v2_8q_all (L q : Nat) (hL : 4 ≤ L)
    (hq : 0 < q) (hbound : 8*q < 2^L) :
    ∃ t, v2 (8*q) = t+3 := by
  obtain ⟨u,t,len,hfactor,hlen,hu⟩ := factor8q L q hL hq hbound
  have hnum := factor8q_num u t q hfactor
  refine ⟨t,?_⟩
  rw [hnum]
  exact v2_odd_factor u (t+3)


/-- The generic reset-prefix cost specializes to the exact generalized
q4-prefix-plus-suffix length for n=8*q. -/
theorem resetPrefixCost_8q (L q a b : Nat)
    (hL : 4 ≤ L) (hq : 0 < q) (hbound : 8*q < 2^L) :
    ∃ t, resetPrefixCost 0 (8*q) a b =
      99 + 12*a + 12*t + 3*b := by
  obtain ⟨t,ht⟩ := v2_8q_all L q hL hq hbound
  refine ⟨t,?_⟩
  unfold resetPrefixCost
  rw [ht]
  omega

#print axioms factor8q
#print axioms s1LeftFacing_8q_all
#print axioms q4LeftFacingAll_expanded
#print axioms v2_8q_all
#print axioms resetPrefixCost_8q
#print axioms sourceLeftFixedPrefix14

end BB6Coverage.Agent48M0EvenEightValuationEncoding
