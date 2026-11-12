import S1Encoder
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent2EvenLeftEncoding

open BB6Coverage
open BB6Coverage.Agent8S1Encoder

set_option maxHeartbeats 3000000

private theorem sideBit_append_before (xs ys : List Bool) (i : Nat)
    (hi : i < xs.length) :
    sideBit (xs ++ ys) i = sideBit xs i := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i < xs.length := by
            simp only [List.length_cons] at hi
            omega
          simpa [sideBit] using ih i hi'

private theorem sideBit_append_after (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by
            simp only [List.length_cons] at hi
            omega
          simpa [sideBit] using ih i hi'

private theorem d0pow_length (r : Nat) : (d0pow r).length = 3*r := by
  induction r with
  | zero => simp [d0pow]
  | succ r ih => simp [d0pow,d0,ih]; omega

private theorem d1pow_length (r : Nat) : (d1pow r).length = 3*r := by
  induction r with
  | zero => simp [d1pow]
  | succ r ih => simp [d1pow,d1,ih]; omega

private theorem sideBit_d0pow_inside (r i : Nat) (hi : i < 3*r) :
    sideBit (d0pow r) i = decide (i%3=2) := by
  induction r generalizing i with
  | zero => omega
  | succ r ih =>
      by_cases hi3 : i < 3
      · change sideBit (d0 ++ d0pow r) i = decide (i%3=2)
        have hhead := sideBit_append_before d0 (d0pow r) i (by simp [d0]; omega)
        rw [hhead]
        have hcases : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hcases with h0 | h1 | h2 <;> subst i <;>
          simp [d0,sideBit]
      · have htail : sideBit (d0pow (r+1)) i = sideBit (d0pow r) (i-3) := by
          rw [d0pow]
          exact sideBit_append_after d0 (d0pow r) i (by simp [d0]; omega)
        have hi' : i-3 < 3*r := by omega
        rw [htail,ih (i-3) hi']
        have hmod : (i-3)%3=i%3 := by omega
        simp [hmod]

/-- The left output formula used by the counted carry-prefix proof. -/
def carryLeftOutputBit (r : Nat) (T : Int → Bool) (x : Int) : Bool :=
  if x < -3*(r:Int)-2 then T x
  else if x ≤ -3*(r:Int) then true
  else decide (x % 3 = 1)

/-- The carry output changes d1^r d0 into d0^r d1 and leaves the
remaining left suffix unchanged. This is a tape-word identity, independent
of the run proof that produces the output formula. -/
theorem carryLeftOutputBit_matches_word
    (r : Nat) (T : Int → Bool) (rest : List Bool)
    (hinput : ∀ i : Nat,
      T (-(i:Int)) = sideBit (d1pow r ++ d0 ++ rest) i) :
    ∀ i : Nat,
      carryLeftOutputBit r T (-(i:Int)) =
        sideBit ((d0pow r ++ d1) ++ rest) i := by
  intro i
  by_cases hlow : i < 3*r
  · have hmod : (-(i:Int))%3=1 ↔ i%3=2 := by omega
    have hside0 : sideBit (d0pow r ++ (d1 ++ rest)) i = sideBit (d0pow r) i :=
      sideBit_append_before (d0pow r) (d1++rest) i (by rw [d0pow_length]; omega)
    have hside : sideBit ((d0pow r ++ d1) ++ rest) i = sideBit (d0pow r) i := by
      simpa [List.append_assoc] using hside0
    have hformula : carryLeftOutputBit r T (-(i:Int)) =
        decide ((-(i:Int))%3=1) := by
      have hfar : ¬ (-(i:Int)) < -3*(r:Int)-2 := by omega
      have hterm : ¬ (-(i:Int)) ≤ -3*(r:Int) := by omega
      simp [carryLeftOutputBit,hfar,hterm]
    have hmodBool : decide ((-(i:Int))%3=1) = decide (i%3=2) := by
      simp [hmod]
    calc
      carryLeftOutputBit r T (-(i:Int)) = decide ((-(i:Int))%3=1) := hformula
      _ = decide (i%3=2) := hmodBool
      _ = sideBit (d0pow r) i := (sideBit_d0pow_inside r i hlow).symm
      _ = sideBit ((d0pow r ++ d1) ++ rest) i := hside.symm
  · by_cases hmid : i ≤ 3*r+2
    · have hlow' : 3*r ≤ i := by omega
      have htarget : sideBit (d0pow r ++ (d1 ++ rest)) i = true := by
        have htail : sideBit (d0pow r ++ (d1++rest)) i = sideBit (d1++rest) (i-3*r) := by
          rw [sideBit_append_after (d0pow r) (d1++rest) i (by rw [d0pow_length]; omega)]
          rw [d0pow_length]
        have hbit : sideBit d1 (i-3*r) = true := by
          have hcases : i-3*r=0 ∨ i-3*r=1 ∨ i-3*r=2 := by omega
          rcases hcases with h0 | h1 | h2
          · simp [h0,d1,sideBit]
          · simp [h1,d1,sideBit]
          · simp [h2,d1,sideBit]
        have happend : sideBit (d1 ++ rest) (i-3*r) = sideBit d1 (i-3*r) :=
          sideBit_append_before d1 rest (i-3*r) (by simp [d1]; omega)
        calc
          sideBit (d0pow r ++ (d1++rest)) i = sideBit (d1++rest) (i-3*r) := htail
          _ = sideBit d1 (i-3*r) := happend
          _ = true := hbit
      have hxlo : -(i:Int) ≥ -3*(r:Int)-2 := by omega
      have hxhi : -(i:Int) ≤ -3*(r:Int) := by omega
      have htarget' : sideBit (d0pow r ++ d1 ++ rest) i = true := by
        simpa [List.append_assoc] using htarget
      rw [htarget']
      simp [carryLeftOutputBit,hxlo,hxhi]
    · have htail : 3*r+3 ≤ i := by omega
      have hfar : (-(i:Int)) < -3*(r:Int)-2 := by omega
      have hsource : sideBit (d1pow r ++ d0 ++ rest) i =
          sideBit rest (i-(3*r+3)) := by
        have hlen : (d1pow r ++ d0).length = 3*r+3 := by
          simp [d1pow_length,d0]
        have ht := sideBit_append_after (d1pow r ++ d0) rest i (by rw [hlen]; omega)
        simpa [hlen] using ht
      have htarget : sideBit (d0pow r ++ d1 ++ rest) i =
          sideBit rest (i-(3*r+3)) := by
        have hlen : (d0pow r ++ d1).length = 3*r+3 := by
          simp [d0pow_length,d1]
        have ht := sideBit_append_after (d0pow r ++ d1) rest i (by rw [hlen]; omega)
        simpa [hlen] using ht
      have hformula : carryLeftOutputBit r T (-(i:Int)) = T (-(i:Int)) := by
        simp [carryLeftOutputBit,hfar]
      calc
        carryLeftOutputBit r T (-(i:Int)) = T (-(i:Int)) := hformula
        _ = sideBit (d1pow r ++ d0 ++ rest) i := hinput i
        _ = sideBit rest (i-(3*r+3)) := hsource
        _ = sideBit (d0pow r ++ d1 ++ rest) i := htarget.symm

/-- The source S1 left encoding after the carry output is precisely the
encoding of z-1. This is the missing interface between the explicit
carry-left tape formula and the S1 successor configuration. -/
theorem carryLeftOutputBit_s1Decrement
    (L n m len q r b : Nat) (h : Int) (hq : q < 2^len) :
    ∀ x : Int, x ≤ 0 →
      carryLeftOutputBit r
        (fun y => (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+y)) x =
      (s1Config L n m (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape (h+x) := by
  let P : Int → Bool :=
    fun y => (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+y)
  let rest : List Bool :=
    binDec len q ++ markerWord m ++ d0 ++ binDec L n ++ lh
  have hsrcList :
      s1LeftFacing L n m (len+1+r) ((2*q+1)*2^r) =
        (d1pow r ++ d0) ++ rest := by
    unfold s1LeftFacing rest
    rw [binDec_carryPrefix len q r hq]
    simp [List.append_assoc]
  have htgtList :
      s1LeftFacing L n m (len+1+r) (((2*q+1)*2^r)-1) =
        (d0pow r ++ d1) ++ rest := by
    unfold s1LeftFacing rest
    rw [binDec_sub_one_carryPrefix len q r hq]
    simp [List.append_assoc]
  have hinput : ∀ i : Nat,
      P (-(i:Int)) = sideBit (d1pow r ++ d0 ++ rest) i := by
    intro i
    have hcell := s1Config_left_cell L n m (len+1+r) ((2*q+1)*2^r) b h i
    rw [hsrcList] at hcell
    simpa [P] using hcell
  intro x hx
  let i : Nat := (-x).toNat
  have hi : (i:Int) = -x := by
    dsimp [i]
    exact Int.toNat_of_nonneg (by omega)
  have hneg : -(i:Int) = x := by omega
  have hcoord : h-(i:Int) = h+x := by omega
  have hword := carryLeftOutputBit_matches_word r P rest hinput i
  have hword' :
      carryLeftOutputBit r P x = sideBit ((d0pow r ++ d1) ++ rest) i := by
    simpa [hneg] using hword
  have hcell := s1Config_left_cell L n m (len+1+r)
    (((2*q+1)*2^r)-1) (b+1) h i
  rw [htgtList,hcoord] at hcell
  have htarget :
      (s1Config L n m (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape (h+x) =
        sideBit ((d0pow r ++ d1) ++ rest) i := by
    simpa [List.append_assoc] using hcell
  exact hword'.trans htarget.symm

#print axioms carryLeftOutputBit_matches_word
#print axioms carryLeftOutputBit_s1Decrement

end BB6Coverage.Agent2EvenLeftEncoding
