import CountedReset
import CountedSweep
import CountedQ4Prefix
import ChampionRootBridge
import S1Encoder
import Lean.Elab.Tactic.Omega

/-!
# Marker-0, n=8q q4 bridge

The next authentic-root row after middle 23 has marker 0 and n=8q, with q
odd. After the 3a-cell counted left sweep, the finite TM2 bridge reads only
[-15,3]. Its input is independent of the high quotient tail: the first four
BinDec blocks of 8q are d1,d1,d1,d0, and the bridge sees only the first two
bits of that final d0 block.
-/

namespace BB6Coverage.Agent48M0EvenEightQ4Bridge

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent6Q4Prefix

/-- The bridge reads only this finite interval relative to its initial head. -/
def m0EvenEightInside (x : Int) : Bool :=
  decide (-15 ≤ x ∧ x ≤ 3)

def m0EvenEightBridgeStart : FConfig :=
  ⟨3, 0, [-13,-12,-11,-10,-9,-8,-7,-6,-5,-4,-1,2,3]⟩

def m0EvenEightBridgeEnd : FConfig :=
  ⟨4, 3, [2,1,-1,-4,-7,-10,-13,-14,-15,3]⟩

/-- Exact 63-step run of the original TM2 table on the finite window. -/
theorem m0EvenEightBridge_exact :
    fRun tm2 63 m0EvenEightBridgeStart =
      some m0EvenEightBridgeEnd := by
  decide

/-- Every pre-transition head remains in the finite bridge window. -/
theorem m0EvenEightBridge_heads :
    (List.range 63).all (fun k =>
      match fRun tm2 k m0EvenEightBridgeStart with
      | none => true
      | some f => m0EvenEightInside f.head) = true := by
  decide

/-- The base n=8 word has the four low blocks d1,d1,d1,d0. -/
private theorem binDec_four_eight :
    binDec 4 8 = d1 ++ d1 ++ d1 ++ d0 := by
  have h1 : binDec 4 8 = d1 ++ binDec 3 4 := by
    simpa using binDec_even 3 4 (by decide)
  have h2 : binDec 3 4 = d1 ++ binDec 2 2 := by
    simpa using binDec_even 2 2 (by decide)
  have h3 : binDec 2 2 = d1 ++ binDec 1 1 := by
    simpa using binDec_even 1 1 (by decide)
  have h4 : binDec 1 1 = d0 ++ binDec 0 0 := by
    simpa using binDec_odd 0 0 (by decide)
  simp [h1,h2,h3,h4,binDec_zero,d1pow]

/-- For odd q, the source counter n=8q begins with d1^3,d0. -/
theorem m0EvenEight_binDec_residue8 (L q : Nat)
    (hL : 4 ≤ L) (hqodd : q % 2 = 1) (hbound : 8*q < 2^L) :
    binDec L (8*q) =
      d1 ++ d1 ++ d1 ++ d0 ++ binDec (L-4) (q/2) := by
  have hpow3 : 2^L = 8 * 2^(L-3) := by
    have hL' : L = (L-3)+3 := by omega
    calc
      2^L = 2^((L-3)+3) :=
        congrArg (fun n : Nat => 2^n) hL'
      _ = 2^(L-3)*2^3 := by rw [Nat.pow_add]
      _ = 8*2^(L-3) := by
        rw [show (2:Nat)^3 = 8 by decide]
        exact Nat.mul_comm _ _
  have hpow2 : 2^(L-1) = 4 * 2^(L-3) := by
    rw [show L-1 = (L-3)+2 by omega, Nat.pow_add]
    rw [show (2:Nat)^2 = 4 by decide, Nat.mul_comm]
  have hpow1 : 2^(L-2) = 2 * 2^(L-3) := by
    rw [show L-2 = (L-3)+1 by omega, Nat.pow_add]
    rw [show (2:Nat)^1 = 2 by decide, Nat.mul_comm]
  have hpow4 : 2^(L-3) = 2 * 2^(L-4) := by
    rw [show L-3 = (L-4)+1 by omega, Nat.pow_succ]
    exact Nat.mul_comm _ _
  have hq : q < 2^(L-3) := by
    rw [hpow3] at hbound
    omega
  have hq1 : 4*q < 2^(L-1) := by rw [hpow2]; omega
  have hq2 : 2*q < 2^(L-2) := by rw [hpow1]; omega
  have hq4 : q/2 < 2^(L-4) := by
    rw [hpow4] at hq
    omega
  have hdiv : q = 2*(q/2)+1 := by omega
  have h1 : binDec L (8*q) =
      d1 ++ binDec (L-1) (4*q) := by
    rw [show L = (L-1)+1 by omega,
      show 8*q = 2*(4*q) by omega]
    exact binDec_even (L-1) (4*q) hq1
  have h2 : binDec (L-1) (4*q) =
      d1 ++ binDec (L-2) (2*q) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*q = 2*(2*q) by omega]
    exact binDec_even (L-2) (2*q) hq2
  have h3 : binDec (L-2) (2*q) =
      d1 ++ binDec (L-3) q := by
    rw [show L-2 = (L-3)+1 by omega,
      show 2*q = 2*q by rfl]
    exact binDec_even (L-3) q hq
  have h4 : binDec (L-3) q =
      d0 ++ binDec (L-4) (q/2) := by
    rw [show L-3 = (L-4)+1 by omega]
    calc
      binDec ((L-4)+1) q =
          binDec ((L-4)+1) (2*(q/2)+1) :=
        congrArg (binDec ((L-4)+1)) hdiv
      _ = d0 ++ binDec (L-4) (q/2) :=
        binDec_odd (L-4) (q/2) hq4
  rw [h1,h2,h3,h4]
  simp [List.append_assoc]

/-- The decremented n=8q-1 word shares the quotient tail. -/
theorem m0EvenEight_binDec_residue7 (L q : Nat)
    (hL : 4 ≤ L) (hqodd : q % 2 = 1) (hbound : 8*q < 2^L) :
    binDec L (8*q-1) =
      d0 ++ d0 ++ d0 ++ d1 ++ binDec (L-4) (q/2) := by
  have hpow3 : 2^L = 8 * 2^(L-3) := by
    have hL' : L = (L-3)+3 := by omega
    calc
      2^L = 2^((L-3)+3) :=
        congrArg (fun n : Nat => 2^n) hL'
      _ = 2^(L-3)*2^3 := by rw [Nat.pow_add]
      _ = 8*2^(L-3) := by
        rw [show (2:Nat)^3 = 8 by decide]
        exact Nat.mul_comm _ _
  have hpow2 : 2^(L-1) = 4 * 2^(L-3) := by
    rw [show L-1 = (L-3)+2 by omega, Nat.pow_add]
    rw [show (2:Nat)^2 = 4 by decide, Nat.mul_comm]
  have hpow1 : 2^(L-2) = 2 * 2^(L-3) := by
    rw [show L-2 = (L-3)+1 by omega, Nat.pow_add]
    rw [show (2:Nat)^1 = 2 by decide, Nat.mul_comm]
  have hpow4 : 2^(L-3) = 2 * 2^(L-4) := by
    rw [show L-3 = (L-4)+1 by omega, Nat.pow_succ]
    exact Nat.mul_comm _ _
  have hq : q < 2^(L-3) := by
    rw [hpow3] at hbound
    omega
  have hq1 : 4*q-1 < 2^(L-1) := by rw [hpow2]; omega
  have hq2 : 2*q-1 < 2^(L-2) := by rw [hpow1]; omega
  have hq4 : q/2 < 2^(L-4) := by
    rw [hpow4] at hq
    omega
  have hdiv : q-1 = 2*(q/2) := by omega
  have h1 : binDec L (8*q-1) =
      d0 ++ binDec (L-1) (4*q-1) := by
    rw [show L = (L-1)+1 by omega,
      show 8*q-1 = 2*(4*q-1)+1 by omega]
    exact binDec_odd (L-1) (4*q-1) hq1
  have h2 : binDec (L-1) (4*q-1) =
      d0 ++ binDec (L-2) (2*q-1) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*q-1 = 2*(2*q-1)+1 by omega]
    exact binDec_odd (L-2) (2*q-1) hq2
  have h3 : binDec (L-2) (2*q-1) =
      d0 ++ binDec (L-3) (q-1) := by
    rw [show L-2 = (L-3)+1 by omega,
      show 2*q-1 = 2*(q-1)+1 by omega]
    exact binDec_odd (L-3) (q-1) (by omega)
  have h4 : binDec (L-3) (q-1) =
      d1 ++ binDec (L-4) (q/2) := by
    rw [show L-3 = (L-4)+1 by omega, hdiv]
    exact binDec_even (L-4) (q/2) hq4
  rw [h1,h2,h3,h4]
  simp [List.append_assoc]

/-- The fixed source-side tail after the 3a-cell sweep of S1(L,8q,0,a,0,b). -/
def m0EvenEightSourceLeftSuffix (L q : Nat) : List Bool :=
  markerWord 0 ++ d0 ++ d1 ++ d1 ++ d1 ++ d0 ++
    binDec (L-4) (q/2) ++ lh

theorem m0EvenEightSourceLeftFacing
    (L q a : Nat) (hL : 4 ≤ L) (hqodd : q % 2 = 1)
    (hbound : 8*q < 2^L) :
    s1LeftFacing L (8*q) 0 a 0 =
      d1pow a ++ m0EvenEightSourceLeftSuffix L q := by
  simp [s1LeftFacing,m0EvenEightSourceLeftSuffix,binDec_zero,
    m0EvenEight_binDec_residue8 L q hL hqodd hbound,
    List.append_assoc]

private theorem m0EvenEight_sideBit_append_prefix
    (xs ys : List Bool) (i : Nat) (hi : i < xs.length) :
    sideBit (xs ++ ys) i = sideBit xs i := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          simp only [List.cons_append, sideBit]
          exact ih i hi

private theorem m0EvenEight_sideBit_d1pow (a i : Nat)
    (hi : i < 3*a) : sideBit (d1pow a) i = true := by
  induction a generalizing i with
  | zero => omega
  | succ a ih =>
      by_cases h : i < 3
      · have hi0 : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hi0 with h0 | h1 | h2 <;> subst i <;>
          simp [d1pow,d1,sideBit]
      · have hi' : i-3 < 3*a := by omega
        have heq : i = (i-3)+3 := by omega
        rw [heq]
        simpa [d1pow,d1,sideBit] using ih (i-3) hi'

private theorem m0EvenEightBaseLeftOnes
    (L q a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hqodd : q % 2 = 1)
    (hbound : 8*q < 2^L) :
    leftOnes (s1Config L (8*q) 0 a 0 b h).tape h (3*a) := by
  intro i hi
  have hcell := s1Config_left_cell L (8*q) 0 a 0 b h i
  have hface := m0EvenEightSourceLeftFacing L q a hL hqodd hbound
  have hprefix : i < (d1pow a).length := by
    rw [d1pow_length]
    exact hi
  have hbit : sideBit (d1pow a ++ m0EvenEightSourceLeftSuffix L q) i = true := by
    rw [m0EvenEight_sideBit_append_prefix _ _ _ hprefix]
    exact m0EvenEight_sideBit_d1pow a i hi
  rw [hface, hbit] at hcell
  exact hcell

private theorem m0EvenEightSweptLeftCell
    (L q a b : Nat) (h : Int) (i : Nat)
    (hL : 4 ≤ L) (hqodd : q % 2 = 1)
    (hbound : 8*q < 2^L) :
    sweptLeft (3*a) (s1Config L (8*q) 0 a 0 b h).tape h
      (h - ((3*a+i : Nat) : Int)) =
      sideBit (m0EvenEightSourceLeftSuffix L q) i := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  have hcell := s1Config_left_cell L (8*q) 0 a 0 b h (3*a+i)
  have hface := m0EvenEightSourceLeftFacing L q a hL hqodd hbound
  have hside := sideBit_d1pow_append a (3*a+i)
    (m0EvenEightSourceLeftSuffix L q) (by omega)
  have hpres := sweptLeft_preserves_left (3*a) T h
    (h - ((3*a+i : Nat) : Int)) (by omega)
  rw [hface, hside] at hcell
  simpa [T] using hpres.trans hcell

private theorem m0EvenEightSourceLeftBridgeBit
    (L q i : Nat) (hL : 4 ≤ L) (hqodd : q % 2 = 1)
    (hbound : 8*q < 2^L) (hi : i ≤ 15) :
    sideBit (m0EvenEightSourceLeftSuffix L q) i =
      decide (-(i : Int) ∈ m0EvenEightBridgeStart.marked) := by
  have hbin := m0EvenEight_binDec_residue8 L q hL hqodd hbound
  have hc :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
      i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hc with h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h <;> subst i <;>
    simp [m0EvenEightSourceLeftSuffix,m0EvenEightBridgeStart,
      markerWord,d0,d1,lh,sideBit]

/-- After the 3a-cell counted left sweep, the entire fixed bridge window
matches for every admissible odd quotient q. -/
theorem m0EvenEightBridge_input_match
    (L q a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hqodd : q % 2 = 1)
    (hbound : 8*q < 2^L) (ha : 0 < a) :
    ∀ y, m0EvenEightInside y = true →
      sweptLeft (3*a) (s1Config L (8*q) 0 a 0 b h).tape h
        (h - ((3*a : Nat) : Int) + y) =
        decide (y ∈ m0EvenEightBridgeStart.marked) := by
  intro y hy
  have hyb : -15 ≤ y ∧ y ≤ 3 := by
    simpa [m0EvenEightInside] using hy
  by_cases hy0 : y ≤ 0
  · let i : Nat := Int.toNat (-y)
    have hiCast : (i : Int) = -y := by
      simp [i]
      omega
    have hi : i ≤ 15 := by omega
    have hcoord :
        h - ((3*a : Nat) : Int) + y =
          h - ((3*a+i : Nat) : Int) := by
      push_cast
      omega
    rw [hcoord]
    rw [m0EvenEightSweptLeftCell L q a b h i hL hqodd hbound]
    rw [m0EvenEightSourceLeftBridgeBit L q i hL hqodd hbound hi]
    simp [hiCast]
  · have hypos : y = 1 ∨ y = 2 ∨ y = 3 := by omega
    rcases hypos with rfl | rfl | rfl
    · have hleft := sweptLeft_leftmost (3*a-1)
        (s1Config L (8*q) 0 a 0 b h).tape h
      have hcount : 3*a-1+1=3*a := by omega
      have hcoord :
          h - ((3*a-1 : Nat) : Int) =
            h - ((3*a : Nat) : Int) + 1 := by omega
      simpa [m0EvenEightBridgeStart,hcount,hcoord] using hleft
    · have hblock := sweptLeft_block (3*a) (3*a-2)
        (s1Config L (8*q) 0 a 0 b h).tape h (by omega)
      have hcoord :
          h - ((3*a-2 : Nat) : Int) =
            h - ((3*a : Nat) : Int) + 2 := by omega
      simpa [m0EvenEightBridgeStart,hcoord] using hblock
    · have hblock := sweptLeft_block (3*a) (3*a-3)
        (s1Config L (8*q) 0 a 0 b h).tape h (by omega)
      have hcoord :
          h - ((3*a-3 : Nat) : Int) =
            h - ((3*a : Nat) : Int) + 3 := by omega
      simpa [m0EvenEightBridgeStart,hcoord] using hblock

#print axioms m0EvenEightBridge_exact
#print axioms m0EvenEightBridge_heads
#print axioms m0EvenEight_binDec_residue8
#print axioms m0EvenEight_binDec_residue7
#print axioms m0EvenEightBridge_input_match

end BB6Coverage.Agent48M0EvenEightQ4Bridge
