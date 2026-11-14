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

/-- The exact positive-facing word after the counted even suffix.  The
six-cell guard is followed by the enlarged all-one block; beyond that block
the source prefix's blank exterior is preserved. -/
theorem even_counted_suffix_rightFacing (P : Int → Bool) (b : Nat)
    (h6 : P 6 = true)
    (hone : ∀ i : Nat, i < 3*(b+1) → P (7+(i:Int)) = true)
    (hfar : ∀ x, even_rightStop b+3 ≤ x → P x = false) :
    ∀ i : Nat,
      (frame even_tailArea (evenOpenFinalSweepTape b P)
        (embed even_tailFinal)).tape (1+(i:Int)) =
        sideBit (s1PhysicalRight (b+1)) i := by
  have hout := even_counted_suffix_tape_output P b h6 hone
  intro i
  rw [s1PhysicalRight_source, sideBit_append]
  have hlen :
      ([false,true,true,true,false,false] : List Bool).length = 6 := by
    decide
  rw [hlen]
  by_cases hi6 : i < 6
  · simp only [if_pos hi6]
    have hx1 : 1 ≤ 1+(i:Int) := by omega
    have hx6 : 1+(i:Int) ≤ 6 := by omega
    have hlocal := hout.2.1 (1+(i:Int)) hx1 hx6
    rw [hlocal]
    have hguard :
        decide (1+(i:Int) ∈ ([2,3,4] : List Int)) =
          sideBit ([false,true,true,true,false,false] : List Bool) i := by
      have hcases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
      rcases hcases with h | h | h | h | h | h <;> subst i <;> decide
    exact hguard
  · by_cases hiEnd : i < 6+3*(b+2)
    · simp only [if_neg hi6]
      have hx7 : 7 ≤ 1+(i:Int) := by omega
      have hxUpper : 1+(i:Int) ≤ even_rightStop b+2 := by
        unfold even_rightStop
        omega
      have hones := hout.2.2.1 (1+(i:Int)) hx7 hxUpper
      have hiD : i-6 < 3*(b+2) := by omega
      rw [hones]
      exact (sideBit_d1pow_true (b+2) (i-6) hiD).symm
    · simp only [if_neg hi6]
      have hx : even_rightStop b+3 ≤ 1+(i:Int) := by
        unfold even_rightStop
        omega
      have hfalse := hfar (1+(i:Int)) hx
      have htail := hout.2.2.2 (1+(i:Int)) hx
      rw [htail, hfalse]
      have hiD : 3*(b+2) ≤ i-6 := by omega
      exact (sideBit_d1pow_false (b+2) (i-6) hiD).symm

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


/-- The S0 right-facing word is blank after its six-cell guard and unary block. -/
theorem s0Config_right_far_zero (l : List Bool) (a z b : Nat)
    (h : Int) (i : Nat) (hi : 9+3*b ≤ i) :
    (s0Config l a z b h).tape (h+1+(i:Int)) = false := by
  rw [s0Config_right_cell]
  change sideBit (s0RightFacing b) i = false
  simp only [s0RightFacing]
  rw [sideBit_append]
  have hi6 : ¬ i < 6 := by omega
  simp [hi6]
  have hiD : 3*(b+1) ≤ i-6 := by omega
  exact sideBit_d1pow_false (b+1) (i-6) hiD

/-- Every cell from the old S0 unary counter's right boundary onward is blank. -/
theorem s0Config_right_zero_after_counter
    (l : List Bool) (a z b : Nat) (h : Int) (k : Nat) :
    (s0Config l a z b h).tape
      (h+even_rightStop b+(k:Int)) = false := by
  have hcell := s0Config_right_far_zero l a z b h (9+3*b+k) (by omega)
  have hcoord : h+even_rightStop b+(k:Int) =
      h+1+((9+3*b+k):Int) := by
    unfold even_rightStop
    omega
  rw [hcoord]
  exact hcell

/-- Prefix preservation transports the S0 zero-padded right exterior to P. -/
theorem s0Config_prefix_far_zero
    (l : List Bool) (a z b : Nat) (h : Int) (P : Int → Bool)
    (hpreserve : ∀ x, 6 < x →
      P x = (s0Config l a z b h).tape (h+x)) :
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
  have hcell := s0Config_right_far_zero l a z b h i hi
  have hcoord : h+x = h+1+(i:Int) := by
    rw [hcast]
    omega
  rw [hpres,hcoord]
  exact hcell

/-- Match the complete positive half of the even suffix to an arbitrary S0
configuration with the updated right counter. -/
theorem even_counted_suffix_matches_s0_right_of_prefix
    (l : List Bool) (a zIn zOut b : Nat) (h : Int) (P : Int → Bool)
    (h6 : P 6 = true)
    (hone : ∀ i : Nat, i < 3*(b+1) → P (7+(i:Int)) = true)
    (hpreserve : ∀ x, 6 < x →
      P x = (s0Config l a zIn b h).tape (h+x)) :
    ∀ i : Nat,
      (frame even_tailArea (evenOpenFinalSweepTape b P) (embed even_tailFinal)).tape
        (1+(i:Int)) =
      (s0Config l a zOut (b+1) h).tape (h+1+(i:Int)) := by
  have hfar := s0Config_prefix_far_zero l a zIn b h P hpreserve
  have hright := even_counted_suffix_rightFacing P b h6 hone hfar
  intro i
  rw [s0Config_right_cell]
  simpa [s1PhysicalRight,s0PhysicalRight] using hright i

/--
Canonical S0 tape glue for the even counted suffix.  The caller supplies the
prefix's nonpositive-cell identity; the positive half is established from
the source S0 right encoding and prefix preservation.
-/
theorem even_counted_suffix_canonical_s0_of_left
    (l : List Bool) (a zIn zOut b : Nat) (h : Int) (P : Int → Bool)
    (h6 : P 6 = true)
    (hone : ∀ i : Nat, i < 3*(b+1) → P (7+(i:Int)) = true)
    (hpreserve : ∀ x, 6 < x →
      P x = (s0Config l a zIn b h).tape (h+x))
    (hleft : ∀ x, x ≤ 0 →
      P x = (s0Config l a zOut (b+1) h).tape (h+x)) :
    ∀ x,
      (frame even_tailArea (evenOpenFinalSweepTape b P) (embed even_tailFinal)).tape x =
        (s0Config l a zOut (b+1) h).tape (h+x) := by
  have hright := even_counted_suffix_matches_s0_right_of_prefix
    l a zIn zOut b h P h6 hone hpreserve
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

/--
Full S0 single-decrement composition interface.  A caller supplies the
15+12r-step prefix run, its open even-suffix boundary, preservation of the
old right exterior, and the prefix's left-output identity.  The suffix then
completes the 33+12b steps and the complete output is the canonical S0
configuration with counter zOut and right counter b+1.
-/
theorem s0Config_counted_decrement_of_prefix
    (l : List Bool) (a zIn zOut b r : Nat) (h : Int) (Tpre : Int → Bool)
    (hprefix : run tm2 (15+12*r) (s0Config l a zIn b h) =
      some ⟨(4 : Fin 6),h+7,Tpre⟩)
    (h1 : Tpre (h+1) = true) (h2 : Tpre (h+2) = true)
    (h3 : Tpre (h+3) = true) (h4 : Tpre (h+4) = true)
    (h5 : Tpre (h+5) = false) (h6 : Tpre (h+6) = true)
    (hone : ∀ i : Nat, i < 3*(b+1) → Tpre (h+7+(i:Int)) = true)
    (hpreserve : ∀ x, 6 < x →
      Tpre (h+x) = (s0Config l a zIn b h).tape (h+x))
    (hleft : ∀ x, x ≤ 0 →
      Tpre (h+x) = (s0Config l a zOut (b+1) h).tape (h+x)) :
    run tm2 (48+12*r+12*b) (s0Config l a zIn b h) =
      some (s0Config l a zOut (b+1) h) := by
  let P : Int → Bool := fun x => Tpre (h+x)
  have hP1 : P 1 = true := by simpa [P] using h1
  have hP2 : P 2 = true := by simpa [P] using h2
  have hP3 : P 3 = true := by simpa [P] using h3
  have hP4 : P 4 = true := by simpa [P] using h4
  have hP5 : P 5 = false := by simpa [P] using h5
  have hP6 : P 6 = true := by simpa [P] using h6
  have honeP : ∀ i : Nat, i < 3*(b+1) → P (7+(i:Int)) = true := by
    intro i hi
    simpa [P,Int.add_assoc] using hone i hi
  have hpreserveP : ∀ x, 6 < x →
      P x = (s0Config l a zIn b h).tape (h+x) := by
    intro x hx
    simpa [P] using hpreserve x hx
  have hleftP : ∀ x, x ≤ 0 →
      P x = (s0Config l a zOut (b+1) h).tape (h+x) := by
    intro x hx
    simpa [P] using hleft x hx
  have hzero0 : P (even_rightStop b) = false := by
    have hfar : 6 < even_rightStop b := by
      unfold even_rightStop
      omega
    have hkeep := hpreserve (even_rightStop b) hfar
    have hsource := s0Config_right_zero_after_counter l a zIn b h 0
    have hvalue : Tpre (h+even_rightStop b) = false := by
      rw [hkeep]
      simpa [even_rightStop,Int.add_assoc] using hsource
    simpa [P] using hvalue
  have hzero1 : P (even_rightStop b+1) = false := by
    have hfar : 6 < even_rightStop b+1 := by
      unfold even_rightStop
      omega
    have hkeep := hpreserve (even_rightStop b+1) hfar
    have hsource := s0Config_right_zero_after_counter l a zIn b h 1
    have hvalue : Tpre (h+(even_rightStop b+1)) = false := by
      rw [hkeep]
      simpa [even_rightStop,Int.add_assoc] using hsource
    simpa [P] using hvalue
  have hzero2 : P (even_rightStop b+2) = false := by
    have hfar : 6 < even_rightStop b+2 := by
      unfold even_rightStop
      omega
    have hkeep := hpreserve (even_rightStop b+2) hfar
    have hsource := s0Config_right_zero_after_counter l a zIn b h 2
    have hvalue : Tpre (h+(even_rightStop b+2)) = false := by
      rw [hkeep]
      simpa [even_rightStop,Int.add_assoc] using hsource
    simpa [P] using hvalue
  have hsuffix := even_counted_suffix_from_open P b
    hP1 hP2 hP3 hP4 hP5 hP6 honeP hzero0 hzero1 hzero2
  have hstart : shiftConfig h ⟨(4 : Fin 6),7,P⟩ =
      ⟨(4 : Fin 6),h+7,Tpre⟩ := by
    change (⟨(4 : Fin 6),7+h,fun x => P (x-h)⟩ : Config) =
      ⟨(4 : Fin 6),h+7,Tpre⟩
    have hhead : (7:Int)+h = h+7 := by omega
    rw [hhead]
    congr 1
    funext x
    dsimp [P]
    congr 1
    omega
  let Tpost : Int → Bool := fun x =>
    (frame even_tailArea (evenOpenFinalSweepTape b P)
      (embed even_tailFinal)).tape (x-h)
  have hshift := shift_run h tm2 ⟨(4 : Fin 6),7,P⟩ (33+12*b)
  rw [hsuffix] at hshift
  simp only [Option.map] at hshift
  rw [hstart] at hshift
  have hshift' : run tm2 (33+12*b) ⟨(4 : Fin 6),h+7,Tpre⟩ =
      some ⟨(3 : Fin 6),h,Tpost⟩ := by
    simpa [shiftConfig,Tpost,frame,embed,even_tailFinal] using hshift
  have hfull := run_compose tm2 (15+12*r) (33+12*b)
    (s0Config l a zIn b h) ⟨(4 : Fin 6),h+7,Tpre⟩
    ⟨(3 : Fin 6),h,Tpost⟩ hprefix hshift'
  have hcanonical := even_counted_suffix_canonical_s0_of_left
    l a zIn zOut b h P hP6 honeP hpreserveP hleftP
  have hTpost : Tpost = (s0Config l a zOut (b+1) h).tape := by
    funext x
    dsimp [Tpost]
    have hv := hcanonical (x-h)
    have hcoord : h+(x-h)=x := by omega
    simpa [hcoord] using hv
  have hout : (⟨(3 : Fin 6),h,Tpost⟩ : Config) =
      s0Config l a zOut (b+1) h := by
    simp [s0Config,hTpost]
  have hcost : (15+12*r)+(33+12*b) = 48+12*r+12*b := by omega
  rw [hcost] at hfull
  simpa [hout] using hfull

#print axioms s0Config_right_far_zero
#print axioms s0Config_right_zero_after_counter
#print axioms s0Config_prefix_far_zero
#print axioms even_counted_suffix_canonical_s0_of_left
#print axioms s0Config_counted_decrement_of_prefix

#print axioms even_counted_suffix_tape_output

end BB6Coverage.Agent24ChampionTime
