import MaskedDigitWeight
namespace BB6.Agent45ReverseBlock

/-- The jth bit of the digit index, repeated across a 2^L-bit word. -/
def indexMask : Nat → Nat → Nat
| 0, _ => 0
| L+1, j =>
  if j=L then (2^(2^L)-1) <<< 2^L
  else let M := indexMask L j; M ||| (M <<< 2^L)

theorem indexMask_bit (L j i : Nat) :
    (indexMask L j).testBit i = (decide (i<2^L) && i.testBit j) := by
  induction L generalizing i j with
  | zero =>
    by_cases hi : i<1
    · have : i=0 := by omega
      subst i; simp [indexMask]
    · simp [indexMask,hi]
  | succ L ih =>
    have hpos := Nat.two_pow_pos L
    by_cases hj : j=L
    · subst j
      rw [indexMask,if_pos rfl,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,Nat.pow_succ]
      by_cases h1 : i<2^L
      · have h0 := Nat.testBit_lt_two_pow h1
        simp [h1,h0,Nat.not_le_of_gt h1]
      · by_cases h2 : i<2^L*2
        · have hd : i/2^L=1 := by
            apply Nat.div_eq_of_lt_le <;> omega
          have hb : i.testBit L=true := by simp [Nat.testBit_eq_decide_div_mod_eq,hd]
          simp [h1,h2,hb,show i-2^L<2^L by omega,show 2^L≤i by omega]
        · simp [h2,show ¬i-2^L<2^L by omega]
    · rw [indexMask,if_neg hj,Nat.testBit_or,Nat.testBit_shiftLeft,ih,ih,Nat.pow_succ]
      by_cases h1 : i<2^L
      · simp [h1,show i<2^L*2 by omega,Nat.not_le_of_gt h1]
      · by_cases h2 : i<2^L*2
        · have h3 : i-2^L<2^L := by omega
          have he : (i-2^L).testBit j=i.testBit j := by
            by_cases h4 : j<L
            · have heq : i=2^L+(i-2^L) := by omega
              have h := Nat.testBit_two_pow_add_gt h4 (i-2^L)
              rw [←heq] at h
              exact h.symm
            · have hj' : L+1≤j := by omega
              have hp : 2^(L+1)≤2^j := Nat.pow_le_pow_right (by decide) hj'
              have hi' : i<2^(L+1) := by simpa [Nat.pow_succ] using h2
              rw [Nat.testBit_lt_two_pow (show i-2^L<2^j by omega),Nat.testBit_lt_two_pow (show i<2^j by omega)]
          simp [h1,h2,h3,he,show 2^L≤i by omega]
        · simp [h1,h2,show ¬i-2^L<2^L by omega]

/-- Compute weighted digit sum in logarithmically many big-integer masks.
    L is the logarithmic word capacity, j counts the index planes, o is offset. -/
def sumWeight (L : Nat) : Nat → Nat → Nat → Nat
| 0, _, _ => 0
| j+1, o, B => sumWeight L j o B + 2^j*(B &&& (indexMask L j >>> o))

private theorem mod_split (a j : Nat) : a % 2^(j+1) = a % 2^j + 2^j*(a/2^j%2) := by
  rw [Nat.pow_succ]
  exact Nat.mod_mul

private theorem one_mask (L j o : Nat) (ho : o<2^L) :
    1 &&& (indexMask L j >>> o) = o/2^j%2 := by
  rw [Nat.one_and_eq_mod_two]
  have h := indexMask_bit L j o
  have hbit : (indexMask L j >>> o).testBit 0 = o.testBit j := by simpa [ho] using h
  rw [Nat.testBit_zero,Nat.testBit_eq_decide_div_mod_eq] at hbit
  have h1 : (indexMask L j >>> o)%2<2 := Nat.mod_lt _ (by decide)
  have h2 : o/2^j%2<2 := Nat.mod_lt _ (by decide)
  by_cases he : (indexMask L j >>> o)%2=1
  · simp [he] at hbit; omega
  · simp [he] at hbit; omega

theorem sum_one (L j o : Nat) (ho : o<2^L) : sumWeight L j o 1 = o%2^j := by
  induction j with
  | zero => simp [sumWeight,Nat.mod_one]
  | succ j ih => rw [sumWeight,ih,one_mask _ _ _ ho,mod_split]

theorem sum_step (L j o B : Nat) :
    sumWeight L j o B = 2*sumWeight L j (o+1) (B/2) + sumWeight L j o 1*(B%2) := by
  induction j with
  | zero => simp [sumWeight,Nat.mod_one]
  | succ j ih =>
    rw [sumWeight,sumWeight,sumWeight,ih,mask_and_split B,mask_shr_div,mask_and_split 1]
    simp only [Nat.reduceDiv, Nat.zero_and, Nat.mul_zero, Nat.zero_add, Nat.one_mod, Nat.reduceMod, Nat.one_mul]
    rw [Nat.mul_add,Nat.add_mul,Nat.mul_add]
    ac_rfl

/-- Arbitrary-length digit-weight evaluator. No enumeration of the full word
    and no numerical assumptions on its individual bits are required. -/
theorem all_weight_corr (L o k B : Nat) (hk : o+k≤2^L) (hB : B<2^k) :
    sumWeight L L o B+corr k B=(o+k)*B := by
  induction k generalizing o B with
  | zero =>
    have : B=0 := by simpa using hB
    subst B
    have hz : ∀ j, sumWeight L j o 0=0 := by intro j; induction j <;> simp_all [sumWeight]
    simp [hz,corr]
  | succ k ih =>
    have hh : B/2<2^k := by rw [Nat.pow_succ] at hB; omega
    have he := ih (o+1) (B/2) (by omega) hh
    rw [sum_step,sum_one _ _ _ (by omega),Nat.mod_eq_of_lt (show o<2^L by omega),corr]
    have hb := Nat.div_add_mod B 2
    calc
      _ = 2*(sumWeight L L (o+1) (B/2)+corr k (B/2)) + (o+k+1)*(B%2) := by simp [Nat.add_mul]; omega
      _ = _ := by rw [he]; rw [show o+1+k=o+(k+1) by omega]; rw [show o+k+1=o+(k+1) by omega]; rw [←Nat.mul_assoc, Nat.mul_comm 2 (o+(k+1)), Nat.mul_assoc, ←Nat.mul_add, hb]

#print axioms indexMask_bit
#print axioms all_weight_corr
end BB6.Agent45ReverseBlock
