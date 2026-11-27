import BirthCover
import StrictPlaneGaps

namespace BB6.Agent43StrictWord
open BB6.Agent9BatchCarry (Interior Edge Walk)
open BB6.Agent9FoldedProbe
open BB6.Agent43StrictPlane

/-- Chronological wrap word, with its first bit least significant.
    The word is truncated to k bits; no fitted clock assumption. -/
def weight (q : Nat) : Nat → Nat → Nat
  | 0,_ => 0
  | k+1,B => q*(B%2)+2*weight (q+1) k (B/2)

/-- A strict start and exact weighted endpoint equation suffice for
    every intermediate guard, even for arbitrarily long words. -/
theorem walk_of_word (q c k z B : Nat) (hc : Interior q c)
    (he : c+weight q k B=2^k*z) : Walk q c k z := by
  induction k generalizing q c B with
  | zero =>
    simp [weight] at he
    subst z
    exact Walk.nil q c hc
  | succ k ih =>
    let b := B%2
    let a := (c+q*b)/2
    have hb : b≤1 := by dsimp [b]; omega
    have hpow : 2^(k+1)*z=2*(2^k*z) := by rw [Nat.pow_succ]; ac_rfl
    rw [weight,hpow] at he
    have ha : 2*a=c+q*b := by dsimp [a,b]; omega
    have hedge : 2*a=c ∨ 2*a=c+q := by
      rcases (show b=0 ∨ b=1 by omega) with h|h <;> simp [h] at ha
      · exact Or.inl ha
      · exact Or.inr ha
    have hai : Interior (q+1) a := by
      unfold Interior at hc ⊢
      rcases hedge with h|h <;> omega
    have ht : a+weight (q+1) k (B/2)=2^k*z := by dsimp [b] at ha; omega
    exact Walk.cons q c a k z ⟨hc,hai,hedge⟩ (ih (q+1) a (B/2) hai ht)

/-- Every source walk has a finite wrap word of the exact length. -/
theorem word_of_walk {q c k z : Nat} (h : Walk q c k z) :
    ∃ B<2^k, c+weight q k B=2^k*z := by
  induction h with
  | nil q c hi => exact ⟨0,by simp,by simp [weight]⟩
  | cons q c a k z he ht ih =>
    obtain ⟨B,hB,hEq⟩ := ih
    have hp : 2^(k+1)*z=2*(2^k*z) := by rw [Nat.pow_succ]; ac_rfl
    rcases he.2.2 with h0|h1
    · refine ⟨2*B,by rw [Nat.pow_succ]; omega,?_⟩
      have hd : (2*B)/2=B := by omega
      have hm : (2*B)%2=0 := by omega
      rw [weight,hd,hm,hp]
      simp only [Nat.mul_zero,Nat.zero_add]
      omega
    · refine ⟨2*B+1,by rw [Nat.pow_succ]; omega,?_⟩
      have hd : (2*B+1)/2=B := by omega
      have hm : (2*B+1)%2=1 := by omega
      rw [weight,hd,hm,hp]
      simp only [Nat.mul_one]
      omega

/-- Adjacent words have separated endpoint intervals. This proof uses
    only the elementary carry recurrence, not a quotient approximation. -/
theorem weight_adjacent (q k B : Nat) (hB : B+1<2^k) :
    weight q k B+q≤weight q k (B+1) := by
  induction k generalizing q B with
  | zero => simp at hB
  | succ k ih =>
    by_cases h : B%2=0
    · have h1 : (B+1)%2=1 := by omega
      have h2 : (B+1)/2=B/2 := by omega
      simp [weight,h,h1,h2]
      omega
    · have h0 : B%2=1 := by omega
      have h1 : (B+1)%2=0 := by omega
      have h2 : (B+1)/2=B/2+1 := by omega
      have h3 : B/2+1<2^k := by rw [Nat.pow_succ] at hB; omega
      have hi := ih (q+1) (B/2) h3
      simp only [weight,h0,h1,h2,Nat.mul_zero,Nat.zero_add,Nat.mul_one]
      omega

/-- All nonadjacent intervals are separated as well. -/
theorem weight_separate (q k B D : Nat) (hD : D<2^k) (hBD : B<D) :
    weight q k B+q≤weight q k D := by
  induction D with
  | zero => omega
  | succ D ih =>
    have h := weight_adjacent q k D hD
    by_cases hb : B=D
    · simpa [hb] using h
    · have hl := ih (by omega) (by omega)
      omega

/-- Concatenate arbitrary word lengths without reconstructing a whole
    huge word's weight through one-bit recursion. -/
theorem weight_append (q k j B C : Nat) (hb : B<2^k) :
    weight q (k+j) (B+2^k*C)=weight q k B+2^k*weight (q+k) j C := by
  induction k generalizing q B with
  | zero =>
    have he : B=0 := by simpa using hb
    simp [he,weight]
  | succ k ih =>
    have hd : (B+2^(k+1)*C)/2=B/2+2^k*C := by
      rw [Nat.pow_succ]
      have h : 2^k*2*C=2*(2^k*C) := by ac_rfl
      rw [h]
      omega
    have hm : (B+2^(k+1)*C)%2=B%2 := by
      rw [Nat.pow_succ]
      have h : 2^k*2*C=2*(2^k*C) := by ac_rfl
      rw [h]
      omega
    have hb' : B/2<2^k := by rw [Nat.pow_succ] at hb; omega
    rw [show k+1+j=k+j+1 by omega,weight,hd,hm,ih (q+1) (B/2) hb',weight]
    rw [Nat.pow_succ, show q+1+k=q+(k+1) by omega]
    rw [Nat.mul_add]
    ac_rfl

/-- Exact membership in a selected word's terminal interval, without
    a restriction on 2^k relative to the clock. -/
theorem strict_walk_iff_interval (q k z : Nat) (hq : 3≤q) :
    (∃ c, Walk q c k z) ↔ ∃ B<2^k,
      first (2^k) (weight q k B)≤z ∧ z≤last (2^k) q (weight q k B) := by
  constructor
  · rintro ⟨c,hw⟩
    obtain ⟨B,hB,he⟩ := word_of_walk hw
    have hc := walk_start hw
    exact ⟨B,hB,(strict_interval_iff _ _ _ _ (Nat.two_pow_pos _) hq).1 ⟨c,hc.1,hc.2,by omega⟩⟩
  · rintro ⟨B,hB,hi⟩
    obtain ⟨c,hc,hcq,he⟩ := (strict_interval_iff _ _ _ _ (Nat.two_pow_pos _) hq).2 hi
    exact ⟨c,walk_of_word q c k z B ⟨hc,hcq⟩ (by omega)⟩

/-- Canonical folding introduces no extra terminal words: complement
    lifts every folded witness to the requested canonical endpoint. -/
theorem folded_walk_iff_interval (q k z : Nat) (hq : 3≤q) (hz : Canon (q+k) z) :
    (∃ c, FoldedWalk q c k z) ↔ ∃ B<2^k,
      first (2^k) (weight q k B)≤z ∧ z≤last (2^k) q (weight q k B) := by
  rw [←strict_walk_iff_interval q k z hq]
  constructor
  · rintro ⟨a,hw⟩
    obtain ⟨c,hc,_⟩ := folded_lift_end hw
    exact ⟨c,hc⟩
  · rintro ⟨c,hw⟩
    exact ⟨fold q c,c,z,hw,rfl,hz.2⟩

#print axioms walk_of_word
#print axioms word_of_walk
#print axioms weight_adjacent
#print axioms weight_separate
#print axioms weight_append
#print axioms strict_walk_iff_interval
#print axioms folded_walk_iff_interval
end BB6.Agent43StrictWord
