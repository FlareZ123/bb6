import CountedReset
import CountedSweep
import CountedQ4Prefix
import ChampionRootBridge
import S1Encoder
import Lean.Elab.Tactic.Omega

/-!
# m=0, n=32*k+14 finite q4 bridge

This is the 39-step finite bridge obtained after the 3a-cell left sweep
for the next root family `S1(L,32*k+14,0,a,0,b,h)`. Its local input
window is [-9,2], and the finite head trace stays entirely inside that
window. The higher-order binary tail is handled by a separate frame lift.
-/

namespace BB6Coverage.Agent49M0EvenFourteenQ4Bridge

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix

def m0EvenFourteenInside (x : Int) : Bool :=
  decide (-9 ≤ x ∧ x ≤ 2)

def m0EvenFourteenBridgeStart : FConfig :=
  ⟨3, 0, [-7,-6,-5,-4,-1,2]⟩

def m0EvenFourteenBridgeEnd : FConfig :=
  ⟨4, 3, [-9,-8,-7,-4,-1,1,2]⟩

/-- Exact 39-step run of the original TM2 table on the finite window. -/
theorem m0EvenFourteenBridge_exact :
    fRun tm2 39 m0EvenFourteenBridgeStart =
      some m0EvenFourteenBridgeEnd := by
  decide

/-- Every pre-transition head remains in the [-9,2] bridge window. -/
theorem m0EvenFourteenBridge_heads :
    (List.range 39).all (fun k =>
      match fRun tm2 k m0EvenFourteenBridgeStart with
      | none => true
      | some f => m0EvenFourteenInside f.head) = true := by
  decide

/-- Five low source blocks for n=14. -/
theorem m0EvenFourteen_binDec_five_fourteen :
    binDec 5 14 = d1 ++ d0 ++ d0 ++ d0 ++ d1 := by
  have h1 : binDec 5 14 = d1 ++ binDec 4 7 := by
    simpa using binDec_even 4 7 (by decide)
  have h2 : binDec 4 7 = d0 ++ binDec 3 3 := by
    simpa using binDec_odd 3 3 (by decide)
  have h3 : binDec 3 3 = d0 ++ binDec 2 1 := by
    simpa using binDec_odd 2 1 (by decide)
  have h4 : binDec 2 1 = d0 ++ binDec 1 0 := by
    simpa using binDec_odd 1 0 (by decide)
  have h5 : binDec 1 0 = d1 ++ binDec 0 0 := by
    simpa using binDec_even 0 0 (by decide)
  simp [h1,h2,h3,h4,h5,binDec_zero,d1pow]

/-- Five low target blocks for n-1=13. -/
theorem m0EvenFourteen_binDec_five_thirteen :
    binDec 5 13 = d0 ++ d1 ++ d0 ++ d0 ++ d1 := by
  have h1 : binDec 5 13 = d0 ++ binDec 4 6 := by
    simpa using binDec_odd 4 6 (by decide)
  have h2 : binDec 4 6 = d1 ++ binDec 3 3 := by
    simpa using binDec_even 3 3 (by decide)
  have h3 : binDec 3 3 = d0 ++ binDec 2 1 := by
    simpa using binDec_odd 2 1 (by decide)
  have h4 : binDec 2 1 = d0 ++ binDec 1 0 := by
    simpa using binDec_odd 1 0 (by decide)
  have h5 : binDec 1 0 = d1 ++ binDec 0 0 := by
    simpa using binDec_even 0 0 (by decide)
  simp [h1,h2,h3,h4,h5,binDec_zero,d1pow]

private theorem m0EvenFourteenSourceLeftAt
    (a b : Nat) (h : Int) (k : Nat) :
    (s1Config 5 14 0 a 0 b h).tape
      (h - ((3*a+k : Nat) : Int)) =
      sideBit
        (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d0 ++ d0 ++ d1 ++ lh) k := by
  have hleft :
      s1LeftFacing 5 14 0 a 0 =
        d1pow a ++ markerWord 0 ++ d0 ++
          d1 ++ d0 ++ d0 ++ d0 ++ d1 ++ lh := by
    simp [s1LeftFacing,binDec_zero,
      m0EvenFourteen_binDec_five_fourteen,List.append_assoc]
  have hcell := s1Config_left_cell 5 14 0 a 0 b h (3*a+k)
  have hside := sideBit_d1pow_append a (3*a+k)
    (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d0 ++ d0 ++ d1 ++ lh)
    (by omega)
  rw [hleft] at hcell
  simp only [List.append_assoc] at hcell hside
  rw [hside] at hcell
  simpa only [List.append_assoc, show 3*a+k-3*a = k by omega] using hcell

private theorem m0EvenFourteenSweptLeftCell
    (a b : Nat) (h : Int) (k : Nat) :
    sweptLeft (3*a) (s1Config 5 14 0 a 0 b h).tape h
      (h - ((3*a : Nat) : Int) - (k : Int)) =
      sideBit
        (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d0 ++ d0 ++ d1 ++ lh) k := by
  have hpres := sweptLeft_preserves_left (3*a)
    (s1Config 5 14 0 a 0 b h).tape h
    (h - ((3*a : Nat) : Int) - (k : Int)) (by omega)
  rw [hpres]
  have hsrc := m0EvenFourteenSourceLeftAt a b h k
  have hcoord :
      h - ((3*a : Nat) : Int) - (k : Int) =
        h - ((3*a+k : Nat) : Int) := by omega
  rw [hcoord]
  exact hsrc

/-- After the counted left sweep of 3a cells, the complete fixed
[-9,2] input window is the 39-step bridge above. -/
theorem m0EvenFourteenBridge_input_match
    (a b : Nat) (h : Int) (ha : 0 < a) :
    ∀ y, m0EvenFourteenInside y = true →
      (sweptLeft (3*a) (s1Config 5 14 0 a 0 b h).tape h)
        (h - ((3*a : Nat) : Int) + y) =
          decide (y ∈ m0EvenFourteenBridgeStart.marked) := by
  intro y hy
  have hyb : -9 ≤ y ∧ y ≤ 2 := by
    simpa [m0EvenFourteenInside] using hy
  by_cases hy0 : y ≤ 0
  · let k : Nat := Int.toNat (-y)
    have hkcast : (k : Int) = -y := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord :
        h - ((3*a : Nat) : Int) + y =
          h - ((3*a : Nat) : Int) - (k : Int) := by omega
    rw [hcoord]
    have hleft := m0EvenFourteenSweptLeftCell a b h k
    have hbits :
        sideBit
          (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d0 ++ d0 ++ d1 ++ lh) k =
        decide (y ∈ m0EvenFourteenBridgeStart.marked) := by
      have hyCases : y = -9 ∨ y = -8 ∨ y = -7 ∨ y = -6 ∨
          y = -5 ∨ y = -4 ∨ y = -3 ∨ y = -2 ∨ y = -1 ∨ y = 0 := by omega
      rcases hyCases with h9 | h8 | h7 | h6 | h5 | h4 | h3 | h2 | h1 | h0
      all_goals subst y
      all_goals simp [k,m0EvenFourteenBridgeStart,markerWord,d0,d1,lh,sideBit]
    exact hleft.trans hbits
  · have hypos : 1 ≤ y := by omega
    have hyCases : y = 1 ∨ y = 2 := by omega
    rcases hyCases with h1 | h2
    · subst y
      have hleft := sweptLeft_leftmost (3*a-1)
        (s1Config 5 14 0 a 0 b h).tape h
      have hcoord :
          h - ((3*a : Nat) : Int) + 1 =
            h - ((3*a-1 : Nat) : Int) := by omega
      rw [hcoord]
      have hN : 3*a-1+1 = 3*a := by omega
      simpa [m0EvenFourteenBridgeStart,hN] using hleft
    · subst y
      have hblock := sweptLeft_block (3*a) (3*a-2)
        (s1Config 5 14 0 a 0 b h).tape h (by omega)
      have hcoord :
          h - ((3*a : Nat) : Int) + 2 =
            h - ((3*a-2 : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m0EvenFourteenBridgeStart] using hblock

#print axioms m0EvenFourteenBridge_exact
#print axioms m0EvenFourteenBridge_heads
#print axioms m0EvenFourteen_binDec_five_fourteen
#print axioms m0EvenFourteen_binDec_five_thirteen
#print axioms m0EvenFourteenBridge_input_match

end BB6Coverage.Agent49M0EvenFourteenQ4Bridge