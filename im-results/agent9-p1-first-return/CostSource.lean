import SourceFirstReturn
import ShadowCost

namespace BB6.Agent9FirstReturn
open BB6.Agent1Quarter BB6P1Unit

/-- The exact cost of the source inverse history is k-1, where k is the
length of the deterministic moving-modulus first return. -/
theorem gap_return_at_cost {Q m : Nat} (h : Gap Q m 2) :
    ∃ q, q+(m+1)=Q ∧ run q 1 (m+1)=1 := by
  have hm : 0<m := by cases h <;> omega
  have hb := (gap_bounds h).2 hm
  let q := Q-m-1
  have hq : 5≤q := by dsimp [q]; omega
  have hclock : q+(m+1)=Q := by dsimp [q]; omega
  have hsub : q+1=Q-m := by omega
  obtain ⟨hp,_⟩ := gap_reverse h
  have he := path_run hp (by omega)
  exact ⟨q,hclock,by rw [seed_shift q m hq,hsub,he]⟩

/-- For every actual critical source history to right-five, the dyadic
shadow budget must have escaped. -/
theorem source_right_five_shadow_escape (n b m : Nat) (hn : 14≤n)
    (h : OddCone (14*2^n-2*n-16) 3 b 5 m) :
    2^((m+1)-(n+2))*(m+1)>2^n := by
  let Q := 7*2^n-n-3
  have hroot : (14*2^n-2*n-16)+10=2*Q := by
    have hdom := two_mul_le_pow n (by omega)
    dsimp [Q]; omega
  obtain ⟨v,hv,_,hg⟩ := gap_of_oddcone _ Q b 5 m hroot h
  have hv2 : v=2 := by omega
  subst v
  obtain ⟨q,hq,hret⟩ := gap_return_at_cost hg
  apply Nat.lt_of_not_ge
  intro hb
  exact no_return_shadow n q (m+1) hn hq (by omega) hb hret

/-- Uniform source-level cost lower bound: m > 2n+1-ceil(log2(2n)),
expressed with any certified dyadic upper exponent a. -/
theorem source_right_five_cost_before_two_n (n b m a : Nat) (hn : 14≤n)
    (ha : 2≤a) (han : a≤n) (hpow : 2*n≤2^a)
    (h : OddCone (14*2^n-2*n-16) 3 b 5 m) : 2*n+1<m+a := by
  apply Nat.lt_of_not_ge
  intro hc
  have hle := Nat.pow_le_pow_right (show 0<2 by decide)
    (show (m+1)-(n+2)≤n-a by omega)
  have hb := Nat.mul_le_mul hle (show m+1≤2^a by omega)
  rw [← Nat.pow_add,show n-a+a=n by omega] at hb
  have hg := source_right_five_shadow_escape n b m hn h
  omega

/-- Explicit logarithmic form, with no auxiliary exponent hypothesis. -/
theorem source_right_five_cost_log (n b m : Nat) (hn : 14≤n)
    (h : OddCone (14*2^n-2*n-16) 3 b 5 m) :
    2*n < m + Nat.log2 (2*n-1) := by
  let a := Nat.log2 (2*n-1)+1
  have hnz : 2*n-1 ≠ 0 := by omega
  have hpow : 2*n≤2^a := by
    have hh := (Nat.log2_lt hnz).mp (show Nat.log2 (2*n-1)<a by dsimp [a]; omega)
    omega
  have ha : 2≤a := by
    by_cases hh : 2≤a
    · exact hh
    · have he : a=1 := by dsimp [a] at *; omega
      rw [he] at hpow
      omega
  have han : a≤n := by
    have hh := two_mul_le_pow n (by omega)
    have hl := (Nat.log2_lt hnz).mpr (show 2*n-1<2^n by omega)
    dsimp [a]; omega
  have hcost := source_right_five_cost_before_two_n n b m a hn ha han hpow h
  dsimp [a] at hcost
  omega

#print axioms gap_return_at_cost
#print axioms source_right_five_shadow_escape
#print axioms source_right_five_cost_before_two_n
#print axioms source_right_five_cost_log
end BB6.Agent9FirstReturn
