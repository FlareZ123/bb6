import CountedReset
import CountedSweep
import CountedQ4Prefix
import ChampionRootBridge
import S1Encoder
import Lean.Elab.Tactic.Omega

/-!
# Marker-0, n=8q q4 bridge

The finite bridge used by the next authentic-root row after middle 23.
It is entered after the 3a-cell counted left sweep from S1(L,8q,0,a,0,b),
where q is odd. The local source window is [-15,3]. For q=1 the full
base source is L=4,n=8; for arbitrary odd q the bridge input agrees on
this window because BinDec(8q) begins d1^3 ++ d0 and the bridge reads
only the first two cells of that final d0 block.
-/

namespace BB6Coverage.Agent48M0EvenEightQ4Bridge

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent6Q4Prefix

/-- The bridge reads only the finite window [-15,3]. -/
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

/-- The four low blocks of the base counter n=8. -/
theorem m0Even_binDec_four_eight :
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

private theorem m0EvenEightSourceLeftAt
    (a b : Nat) (h : Int) (k : Nat) :
    (s1Config 4 8 0 a 0 b h).tape
      (h - ((3*a+k : Nat) : Int)) =
      sideBit (markerWord 0 ++ d0 ++ d1 ++ d1 ++ d1 ++ d0 ++ lh) k := by
  have hleft :
      s1LeftFacing 4 8 0 a 0 =
        d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d1 ++ d1 ++ d0 ++ lh := by
    simp [s1LeftFacing,m0Even_binDec_four_eight,List.append_assoc]
  have hcell := s1Config_left_cell 4 8 0 a 0 b h (3*a+k)
  have hside := sideBit_d1pow_append a (3*a+k)
    (markerWord 0 ++ d0 ++ d1 ++ d1 ++ d1 ++ d0 ++ lh) (by omega)
  rw [hleft] at hcell
  simp only [List.append_assoc] at hcell hside
  rw [hside] at hcell
  simpa only [List.append_assoc,
    show 3*a+k-3*a = k by omega] using hcell

private theorem m0EvenEightSweptLeftCell
    (a b : Nat) (h : Int) (k : Nat) :
    sweptLeft (3*a) (s1Config 4 8 0 a 0 b h).tape h
      (h - ((3*a : Nat) : Int) - (k : Int)) =
      sideBit (markerWord 0 ++ d0 ++ d1 ++ d1 ++ d1 ++ d0 ++ lh) k := by
  have hpres := sweptLeft_preserves_left (3*a)
    (s1Config 4 8 0 a 0 b h).tape h
    (h - ((3*a : Nat) : Int) - (k : Int)) (by omega)
  rw [hpres]
  have hsrc := m0EvenEightSourceLeftAt a b h k
  have hcoord :
      h - ((3*a : Nat) : Int) - (k : Int) =
        h - ((3*a+k : Nat) : Int) := by omega
  rw [hcoord]
  exact hsrc

/-- After the 3a-cell counted left sweep, the complete fixed [-15,3]
input window is the 63-step bridge above. -/
theorem m0EvenEightBridge_input_match
    (a b : Nat) (h : Int) (ha : 0 < a) :
    ∀ y, m0EvenEightInside y = true →
      (sweptLeft (3*a) (s1Config 4 8 0 a 0 b h).tape h)
        (h - ((3*a : Nat) : Int) + y) =
          decide (y ∈ m0EvenEightBridgeStart.marked) := by
  intro y hy
  have hyb : -15 ≤ y ∧ y ≤ 3 := by
    simpa [m0EvenEightInside] using hy
  by_cases hy0 : y ≤ 0
  · let k : Nat := Int.toNat (-y)
    have hkcast : (k : Int) = -y := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord :
        h - ((3*a : Nat) : Int) + y =
          h - ((3*a : Nat) : Int) - (k : Int) := by omega
    rw [hcoord]
    have hleft := m0EvenEightSweptLeftCell a b h k
    have hbits :
        sideBit (markerWord 0 ++ d0 ++ d1 ++ d1 ++ d1 ++ d0 ++ lh) k =
          decide (y ∈ m0EvenEightBridgeStart.marked) := by
      have hyCases :
          y = -15 ∨ y = -14 ∨ y = -13 ∨ y = -12 ∨ y = -11 ∨
          y = -10 ∨ y = -9 ∨ y = -8 ∨ y = -7 ∨ y = -6 ∨
          y = -5 ∨ y = -4 ∨ y = -3 ∨ y = -2 ∨ y = -1 ∨
          y = 0 := by omega
      rcases hyCases with h15 | h14 | h13 | h12 | h11 | h10 |
          h9 | h8 | h7 | h6 | h5 | h4 | h3 | h2 | h1 | h0
      all_goals subst y
      all_goals simp [k,m0EvenEightBridgeStart,markerWord,d0,d1,lh,sideBit]
    exact hleft.trans hbits
  · have hypos : 1 ≤ y := by omega
    have hyCases : y = 1 ∨ y = 2 ∨ y = 3 := by omega
    rcases hyCases with h1 | h2 | h3
    · subst y
      have hleft := sweptLeft_leftmost (3*a-1)
        (s1Config 4 8 0 a 0 b h).tape h
      have hcoord :
          h - ((3*a : Nat) : Int) + 1 =
            h - ((3*a-1 : Nat) : Int) := by omega
      rw [hcoord]
      have hN : 3*a-1+1 = 3*a := by omega
      simpa [m0EvenEightBridgeStart,hN] using hleft
    · subst y
      have hblock := sweptLeft_block (3*a) (3*a-2)
        (s1Config 4 8 0 a 0 b h).tape h (by omega)
      have hcoord :
          h - ((3*a : Nat) : Int) + 2 =
            h - ((3*a-2 : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m0EvenEightBridgeStart] using hblock
    · subst y
      by_cases ha1 : a = 1
      · subst a
        have hhead := sweptLeft_head 1
          (s1Config 4 8 0 1 0 b h).tape h
        have hcoord : h - ((3 : Nat) : Int) + 3 = h := by omega
        rw [hcoord]
        simpa [m0EvenEightBridgeStart] using hhead
      · have ha2 : 2 ≤ a := by omega
        have hblock := sweptLeft_block (3*a) (3*a-3)
          (s1Config 4 8 0 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a : Nat) : Int) + 3 =
              h - ((3*a-3 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m0EvenEightBridgeStart] using hblock

#print axioms m0EvenEightBridge_exact
#print axioms m0EvenEightBridge_heads
#print axioms m0Even_binDec_four_eight
#print axioms m0EvenEightBridge_input_match

end BB6Coverage.Agent48M0EvenEightQ4Bridge
