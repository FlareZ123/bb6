import CountedSuffixOutput
import CountedCarryLeftOutput
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent24ChampionTime

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent3CarryLeftOutput

set_option maxHeartbeats 2000000

/-- The head-facing repeated 100 block has exactly three cells per copy. -/
theorem d0pow_length (n : Nat) : (d0pow n).length = 3*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [d0pow,d0,ih]

/-- Exact zero-padded lookup in the head-facing repeated 100 stream. -/
theorem sideBit_d0pow_formula (n i : Nat) :
    sideBit (d0pow n) i = decide (i < 3*n ∧ i%3=2) := by
  induction n generalizing i with
  | zero =>
      simp [d0pow,sideBit]
  | succ n ih =>
      by_cases h : i < 3
      · have hc : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hc with h0 | h1 | h2
        · subst i
          simp [d0pow,d0,sideBit]
        · subst i
          simp [d0pow,d0,sideBit]
        · subst i
          simp [d0pow,d0,sideBit]
      · have h3 : i = (i-3)+3 := by omega
        rw [h3]
        change sideBit (d0 ++ d0pow n) ((i-3)+3) =
          decide (((i-3)+3 < 3*(n+1)) ∧ ((i-3)+3)%3=2)
        simp [d0,sideBit,ih]
        omega

/-- The exact S1 source output after decrementing a positive counter has
the canonical left-bit formula used by the counted carry finish. This is
a source-encoding theorem: the prefix d1^r ++ d0 is replaced by
d0^r ++ d1, with the entire arbitrary encoded tail unchanged. -/
theorem s1Config_decrement_leftOutput
    (L n m len q r b : Nat) (h : Int) (hq : q < 2^len) :
    ∀ x : Int, x ≤ 0 →
      carryLeftOutputBit r
        (fun y => (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+y)) x =
      (s1Config L n m (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape (h+x) := by
  intro x hx
  obtain ⟨i, rfl⟩ : ∃ i : Nat, x = -(i:Int) := by omega
  have hin :
      (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h-(i:Int)) =
        sideBit
          (d1pow r ++ d0 ++ binDec len q ++
            markerWord m ++ d0 ++ binDec L n ++ lh) i :=
    s1Config_left_carryCells L n m len q r b h i hq
  have hout :
      (s1Config L n m (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape
          (h-(i:Int)) =
        sideBit
          (d0pow r ++ d1 ++ binDec len q ++
            markerWord m ++ d0 ++ binDec L n ++ lh) i := by
    rw [s1Config_left_cell]
    simp only [s1LeftFacing]
    rw [binDec_sub_one_carryPrefix len q r hq]
  have hcoord : h + (-(i:Int)) = h-(i:Int) := by omega
  by_cases hfar : 3*r+3 ≤ i
  · have hinTail :
        sideBit
          (d1pow r ++ d0 ++ binDec len q ++
            markerWord m ++ d0 ++ binDec L n ++ lh) i =
        sideBit (binDec len q ++ markerWord m ++ d0 ++ binDec L n ++ lh)
          (i-(3*r+3)) := by
      rw [sideBit_append]
      simp only [d1pow_length]
      have hnot1 : ¬ i < 3*r := by omega
      simp [hnot1]
      rw [sideBit_append]
      have hnot2 : ¬ i-3*r < 3 := by omega
      simp [hnot2]
      omega
    have houtTail :
        sideBit
          (d0pow r ++ d1 ++ binDec len q ++
            markerWord m ++ d0 ++ binDec L n ++ lh) i =
        sideBit (binDec len q ++ markerWord m ++ d0 ++ binDec L n ++ lh)
          (i-(3*r+3)) := by
      rw [sideBit_append]
      simp only [d0pow_length]
      have hnot1 : ¬ i < 3*r := by omega
      simp [hnot1]
      rw [sideBit_append]
      have hnot2 : ¬ i-3*r < 3 := by omega
      simp [hnot2]
      omega
    have hsame :
        (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape
            (h-(i:Int)) =
        (s1Config L n m (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape
            (h-(i:Int)) := by
      calc
        _ = sideBit
            (d1pow r ++ d0 ++ binDec len q ++
              markerWord m ++ d0 ++ binDec L n ++ lh) i := hin
        _ = sideBit (binDec len q ++ markerWord m ++ d0 ++ binDec L n ++ lh)
              (i-(3*r+3)) := hinTail
        _ = sideBit
            (d0pow r ++ d1 ++ binDec len q ++
              markerWord m ++ d0 ++ binDec L n ++ lh) i := houtTail.symm
        _ = _ := hout.symm
    have hbit :
        carryLeftOutputBit r
          (fun y => (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+y))
          (-(i:Int)) =
        (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h-(i:Int)) := by
      have hlt : (-(i:Int)) < -3*(r:Int)-2 := by omega
      simp [carryLeftOutputBit,hlt]
      congr 1
      omega
    rw [hbit]
    simpa [hcoord] using hsame
  · have hnear : i < 3*r+3 := by omega
    by_cases hmiddle : 3*r ≤ i
    · have hside :
        sideBit
          (d0pow r ++ d1 ++ binDec len q ++
            markerWord m ++ d0 ++ binDec L n ++ lh) i = true := by
        rw [sideBit_append]
        simp only [d0pow_length]
        have hnot : ¬ i < 3*r := by omega
        simp [hnot]
        rw [sideBit_append]
        have hidx : i-3*r < 3 := by omega
        have hd1 : sideBit d1 (i-3*r) = true := by
          simpa [d1pow] using sideBit_d1pow_true 1 (i-3*r) (by omega)
        simp [d1, hidx, hd1]
      have hbit :
          carryLeftOutputBit r
            (fun y => (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+y))
            (-(i:Int)) = true := by
        have hnotfar : ¬ (-(i:Int)) < -3*(r:Int)-2 := by omega
        have hle : (-(i:Int)) ≤ -3*(r:Int) := by omega
        simp [carryLeftOutputBit,hnotfar,hle]
      rw [hbit]
      rw [hcoord]
      rw [hout,hside]
    · have hsmall : i < 3*r := by omega
      have hside :
        sideBit
          (d0pow r ++ d1 ++ binDec len q ++
            markerWord m ++ d0 ++ binDec L n ++ lh) i =
          decide (i%3=2) := by
        rw [sideBit_append]
        simp only [d0pow_length]
        simp [hsmall,sideBit_d0pow_formula]
      have hbit :
          carryLeftOutputBit r
            (fun y => (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+y))
            (-(i:Int)) = decide (i%3=2) := by
        have hnotfar : ¬ (-(i:Int)) < -3*(r:Int)-2 := by omega
        have hgt : ¬ (-(i:Int)) ≤ -3*(r:Int) := by omega
        have hmod : (-(i:Int)) % 3 = 1 ↔ i%3=2 := by omega
        simp [carryLeftOutputBit,hnotfar,hgt,hmod]
      rw [hbit]
      rw [hcoord]
      rw [hout,hside]

#print axioms d0pow_length
#print axioms sideBit_d0pow_formula
#print axioms s1Config_decrement_leftOutput

end BB6Coverage.Agent24ChampionTime
