import S1CountedCarryPrefixBridge
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent24ChampionTime

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent42CarryPrefixBridge
open BB6Coverage.Agent8S1Encoder

set_option maxHeartbeats 1000000

/--
Exact tape effect of the counted even-counter suffix.  The suffix preserves
the entire nonpositive exterior, installs the six-cell local boundary
[0,1,1,1,0,0] on cells 1..6, extends the right unary block through
even_rightStop c + 2, and preserves the old exterior after that block.
Only the one-run premise and the boundary one at cell 6 are needed for this
tape statement; the three zero premises are needed separately for the run
theorem `even_counted_suffix_from_open`.
-/
theorem even_counted_suffix_tape_output (P : Int → Bool) (c : Nat)
    (h6 : P 6 = true)
    (hone : ∀ i : Nat, i < 3*(c+1) → P (7+(i:Int)) = true) :
    (∀ x, x ≤ 0 →
      (frame even_tailArea (evenOpenFinalSweepTape c P) (embed even_tailFinal)).tape x = P x) ∧
    (∀ x, 1 ≤ x → x ≤ 6 →
      (frame even_tailArea (evenOpenFinalSweepTape c P) (embed even_tailFinal)).tape x =
        decide (x ∈ ([2,3,4] : List Int))) ∧
    (∀ x, 7 ≤ x → x ≤ even_rightStop c+2 →
      (frame even_tailArea (evenOpenFinalSweepTape c P) (embed even_tailFinal)).tape x = true) ∧
    (∀ x, even_rightStop c+3 ≤ x →
      (frame even_tailArea (evenOpenFinalSweepTape c P) (embed even_tailFinal)).tape x = P x) := by
  have hon : leftOnes (afterEZero P (even_rightStop c))
      (even_rightStop c) (5+3*c) := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      simp [afterEZero]
    · have hdiff : even_rightStop c-(i:Int) ≠ even_rightStop c := by omega
      have hdiff1 : even_rightStop c-(i:Int) ≠ even_rightStop c+1 := by omega
      have hdiff2 : even_rightStop c-(i:Int) ≠ even_rightStop c+2 := by omega
      simp only [afterEZero,if_neg hdiff,if_neg hdiff1,if_neg hdiff2]
      by_cases h6pos : even_rightStop c-(i:Int) = 6
      · rw [h6pos]
        exact h6
      · have hxgt : 7 ≤ even_rightStop c-(i:Int) := by
          unfold even_rightStop at *
          omega
        have hk : ∃ k : Nat,
            even_rightStop c-(i:Int) = 7+(k:Int) ∧ k < 3*(c+1) := by
          refine ⟨3*(c+1)-i,?_,?_⟩
          · have hiBound : i ≤ 3*(c+1) := by
              unfold even_rightStop at *
              omega
            unfold even_rightStop at *
            omega
          · omega
        obtain ⟨k,heq,hk⟩ := hk
        rw [heq]
        exact hone k hk
  have hright : afterEZero P (even_rightStop c)
      (even_rightStop c+1) = false := by
    have hne : even_rightStop c+1 ≠ even_rightStop c := by omega
    simp [afterEZero,hne]
  have hcount : 5+3*c = (4+3*c)+1 := by omega
  have hclosed := even_swept_closed (4+3*c)
    (afterEZero P (even_rightStop c)) (even_rightStop c)
    (by simpa [hcount] using hon) hright
  have h6coord : even_rightStop c-((4+3*c):Int) = 6 := by
    unfold even_rightStop
    omega
  have hU : evenOpenFinalSweepTape c P =
      (fun x => if x = 6 then false else
        if x = even_rightStop c+1 then true else afterEZero P (even_rightStop c) x) := by
    unfold evenOpenFinalSweepTape
    rw [hcount]
    rw [hclosed]
    funext x
    simp [h6coord]
  constructor
  · intro x hx
    have harea : even_tailArea x = false := by
      simp [even_tailArea]
      omega
    have h6neq : x ≠ 6 := by omega
    have hstop : x ≠ even_rightStop c := by omega
    have hstop1 : x ≠ even_rightStop c+1 := by omega
    have hstop2 : x ≠ even_rightStop c+2 := by omega
    have hB : afterEZero P (even_rightStop c) x = P x := by
      simp [afterEZero,hstop,hstop1,hstop2]
    rw [hU]
    simp [frame,harea,h6neq,hstop1,hB]
  constructor
  · intro x hx1 hx6
    have harea : even_tailArea x = true := by
      simp [even_tailArea]
      omega
    simp [frame,harea,embed,even_tailFinal]
  constructor
  · intro x hx7 hxupper
    have harea : even_tailArea x = false := by
      simp [even_tailArea]
      omega
    have h6neq : x ≠ 6 := by omega
    rw [hU]
    simp only [frame,harea]
    by_cases hstop1 : x = even_rightStop c+1
    · have hne : even_rightStop c+1 ≠ 6 := by omega
      simp [hstop1,hne]
    · have hB : afterEZero P (even_rightStop c) x = true := by
        by_cases hstop : x = even_rightStop c
        · simp [afterEZero,hstop]
        · by_cases hstop2 : x = even_rightStop c+2
          · simp [afterEZero,hstop2]
          · have hxlt : x < even_rightStop c := by omega
            let i : Nat := (x-7).toNat
            have hpos : 0 ≤ x-7 := by omega
            have hcast : (i:Int) = x-7 := by
              simp [i,Int.toNat_of_nonneg hpos]
            have hi : i < 3*(c+1) := by omega
            have heq : x = 7+(i:Int) := by omega
            rw [heq]
            have hstop0 : 7+(i:Int) ≠ even_rightStop c := by omega
            have hstop1' : 7+(i:Int) ≠ even_rightStop c+1 := by omega
            have hstop2' : 7+(i:Int) ≠ even_rightStop c+2 := by omega
            simp [afterEZero,hstop0,hstop1',hstop2']
            exact hone i hi
      simp [hstop1,h6neq,hB]
  · intro x hx
    have harea : even_tailArea x = false := by
      simp [even_tailArea]
      omega
    have h6neq : x ≠ 6 := by omega
    have hstop1 : x ≠ even_rightStop c+1 := by omega
    have hstop : x ≠ even_rightStop c := by omega
    have hstop2 : x ≠ even_rightStop c+2 := by omega
    have hB : afterEZero P (even_rightStop c) x = P x := by
      simp [afterEZero,hstop,hstop1,hstop2]
    rw [hU]
    simp [frame,harea,h6neq,hstop1,hB]


/-- Splitting a nearest-first physical side at a finite prefix. -/
theorem sideBit_append (xs ys : List Bool) (i : Nat) :
    sideBit (xs ++ ys) i =
      if i < xs.length then sideBit xs i else sideBit ys (i-xs.length) := by
  induction xs generalizing i with
  | nil =>
      simp [sideBit]
  | cons a xs ih =>
      cases i with
      | zero =>
          simp [sideBit]
      | succ i =>
          simp [sideBit,ih]

/-- Every cell in a repeated 111 block is one. -/
theorem sideBit_d1pow_true (n i : Nat) (hi : i < 3*n) :
    sideBit (d1pow n) i = true := by
  induction n generalizing i with
  | zero =>
      omega
  | succ n ih =>
      by_cases h0 : i < 3
      · have hcases : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hcases with h | h | h <;> subst i <;> simp [d1pow,d1,sideBit]
      · have h3 : i = (i-3)+3 := by omega
        have hlt : i-3 < 3*n := by omega
        have hrec := ih (i-3) hlt
        rw [h3]
        change sideBit (d1 ++ d1pow n) ((i-3)+3) = true
        simp [d1,sideBit]
        exact hrec

/-- The zero-padded tail of a repeated 111 block is blank. -/
theorem sideBit_d1pow_false (n i : Nat) (hi : 3*n ≤ i) :
    sideBit (d1pow n) i = false := by
  induction n generalizing i with
  | zero =>
      simp [d1pow,sideBit]
  | succ n ih =>
      have h0 : ¬ i < 3 := by omega
      have h3 : i = (i-3)+3 := by omega
      have hlt : 3*n ≤ i-3 := by omega
      rw [h3]
      change sideBit (d1 ++ d1pow n) ((i-3)+3) = false
      simp [d1,sideBit]
      exact ih (i-3) hlt

/-- The old S1 right side is blank beyond its six-cell guard and unary word. -/
theorem s1Config_right_far_zero (L n m a z b : Nat) (h : Int) (i : Nat)
    (hi : 9+3*b ≤ i) :
    (s1Config L n m a z b h).tape (h+1+(i:Int)) = false := by
  rw [s1Config_right_cell]
  change sideBit (s1PhysicalRight b) i = false
  simp only [s1PhysicalRight,s0PhysicalRight,s0RightFacing]
  rw [sideBit_append]
  have hi6 : ¬ i < 6 := by omega
  simp [hi6]
  have hiD : 3*(b+1) ≤ i-6 := by omega
  exact sideBit_d1pow_false (b+1) (i-6) hiD

/-- Prefix preservation transports the source S1 zero-padded right exterior
to the relative tape consumed by the counted suffix. -/
theorem s1Config_prefix_far_zero
    (L n m a z b : Nat) (h : Int) (P : Int → Bool)
    (hpreserve : ∀ x, 6 < x →
      P x = (s1Config L n m a z b h).tape (h+x)) :
    ∀ x, even_rightStop b+3 ≤ x → P x = false := by
  intro x hx
  let i : Nat := (x-1).toNat
  have hpos : 0 ≤ x-1 := by
    unfold even_rightStop at hx
    omega
  have hcast : (i:Int) = x-1 := by
    dsimp [i]
    exact Int.toNat_sub_of_le (by omega)
  have hi : 9+3*b ≤ i := by
    unfold even_rightStop at hx
    omega
  have hpres := hpreserve x (by
    unfold even_rightStop at hx
    omega)
  have hcell := s1Config_right_far_zero L n m a z b h i hi
  have hcoord : h+x = h+1+(i:Int) := by
    rw [hcast]
    omega
  rw [hpres,hcoord]
  exact hcell

/--
The final even suffix has exactly the canonical S1 right-facing word for
counter b+1.  The prefix's preserved far exterior supplies the only
nonlocal premise needed to prove the zero-padded tail.
-/
theorem even_counted_suffix_matches_s1_right_of_prefix
    (L n m a zIn zOut b : Nat) (h : Int) (P : Int → Bool)
    (h6 : P 6 = true)
    (hone : ∀ i : Nat, i < 3*(b+1) → P (7+(i:Int)) = true)
    (hpreserve : ∀ x, 6 < x →
      P x = (s1Config L n m a zIn b h).tape (h+x)) :
    ∀ i : Nat,
      (frame even_tailArea (evenOpenFinalSweepTape b P) (embed even_tailFinal)).tape
        (1+(i:Int)) =
      (s1Config L n m a zOut (b+1) h).tape (h+1+(i:Int)) := by
  have hfar := s1Config_prefix_far_zero L n m a zIn b h P hpreserve
  have hright := even_counted_suffix_rightFacing P b h6 hone hfar
  intro i
  rw [s1Config_right_cell]
  simpa [s1PhysicalRight,s0PhysicalRight] using hright i

/--
Canonical glue interface for the counted even return.  The caller supplies
the remaining nonpositive tape identity from the prefix proof; the suffix
theorem above proves the entire positive half and the exact right counter
growth without any further machine-specific assumptions.
-/
theorem even_counted_suffix_canonical_of_left
    (L n m a zIn zOut b : Nat) (h : Int) (P : Int → Bool)
    (h6 : P 6 = true)
    (hone : ∀ i : Nat, i < 3*(b+1) → P (7+(i:Int)) = true)
    (hpreserve : ∀ x, 6 < x →
      P x = (s1Config L n m a zIn b h).tape (h+x))
    (hleft : ∀ x, x ≤ 0 →
      P x = (s1Config L n m a zOut (b+1) h).tape (h+x)) :
    ∀ x,
      (frame even_tailArea (evenOpenFinalSweepTape b P) (embed even_tailFinal)).tape x =
        (s1Config L n m a zOut (b+1) h).tape (h+x) := by
  have hright := even_counted_suffix_matches_s1_right_of_prefix
    L n m a zIn zOut b h P h6 hone hpreserve
  intro x
  by_cases hx : x ≤ 0
  · have hQ := (even_counted_suffix_tape_output P b h6 hone).1 x hx
    rw [hQ,hleft x hx]
  · have hpos : 1 ≤ x := by omega
    let i : Nat := (x-1).toNat
    have hcast : (i:Int) = x-1 := by
      dsimp [i]
      exact Int.toNat_sub_of_le (by omega)
    have heq : x = 1+(i:Int) := by omega
    rw [heq]
    rw [hright i]
    have hcoord : h+1+(i:Int) = h+(1+(i:Int)) := by omega
    rw [hcoord]

#print axioms sideBit_append
#print axioms sideBit_d1pow_true
#print axioms sideBit_d1pow_false
#print axioms s1Config_right_far_zero
#print axioms s1Config_prefix_far_zero
#print axioms even_counted_suffix_matches_s1_right_of_prefix
#print axioms even_counted_suffix_canonical_of_left

#print axioms even_counted_suffix_tape_output

end BB6Coverage.Agent24ChampionTime
