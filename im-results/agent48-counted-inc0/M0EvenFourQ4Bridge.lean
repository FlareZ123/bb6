import CountedReset
import CountedSweep
import CountedQ4Prefix
import ChampionRootBridge
import S1Encoder
import Lean.Elab.Tactic.Omega

/-!
# m=0, n=4 even q4 bridge

The 51-step finite bridge for the next TM63 reset row. It is entered
after the 3a-cell counted left sweep from S1(L,8k+4,0,a,0,b,h).
The finite certificate and its head-confinement proof are independent
of the higher-order binary tail; input matching is proved below.
-/

namespace BB6Coverage.Agent48M0EvenFourQ4Bridge

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent6Q4Prefix

/-- The bridge reads only the 16-cell window [-12,3]. -/
def m0EvenFourInside (x : Int) : Bool :=
  decide (-12 ≤ x ∧ x ≤ 3)

def m0EvenFourBridgeStart : FConfig :=
  ⟨3, 0, [-10,-9,-8,-7,-6,-5,-4,-1,2,3]⟩

def m0EvenFourBridgeEnd : FConfig :=
  ⟨4, 3, [-12,-11,-10,-7,-4,-1,1,2,3]⟩

/-- Exact 51-step run of the original TM2 table on the finite window. -/
theorem m0EvenFourBridge_exact :
    fRun tm2 51 m0EvenFourBridgeStart =
      some m0EvenFourBridgeEnd := by
  decide

/-- Every pre-transition head remains in the finite bridge window. -/
theorem m0EvenFourBridge_heads :
    (List.range 51).all (fun k =>
      match fRun tm2 k m0EvenFourBridgeStart with
      | none => true
      | some f => m0EvenFourInside f.head) = true := by
  decide

/-- The low three blocks of the source counter n=4. -/
theorem m0Even_binDec_three_four :
    binDec 3 4 = d1 ++ d1 ++ d0 := by
  have h1 : binDec 3 4 = d1 ++ binDec 2 2 := by
    simpa using binDec_even 2 2 (by decide)
  have h2 : binDec 2 2 = d1 ++ binDec 1 1 := by
    simpa using binDec_even 1 1 (by decide)
  have h3 : binDec 1 1 = d0 ++ binDec 0 0 := by
    simpa using binDec_odd 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

/-- The low three blocks of the successor counter n-1=3. -/
theorem m0Even_binDec_three_three :
    binDec 3 3 = d0 ++ d0 ++ d1 := by
  have h1 : binDec 3 3 = d0 ++ binDec 2 1 := by
    simpa using binDec_odd 2 1 (by decide)
  have h2 : binDec 2 1 = d0 ++ binDec 1 0 := by
    simpa using binDec_odd 1 0 (by decide)
  have h3 : binDec 1 0 = d1 ++ binDec 0 0 := by
    simpa using binDec_even 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

private theorem m0EvenFourSourceLeftAt (a b : Nat) (h : Int) (k : Nat) :
    (s1Config 3 4 0 a 0 b h).tape
      (h - ((3*a+k : Nat) : Int)) =
      sideBit (markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh) k := by
  have hleft :
      s1LeftFacing 3 4 0 a 0 =
        d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh := by
    simp [s1LeftFacing,binDec_zero,m0Even_binDec_three_four,List.append_assoc]
  have hcell := s1Config_left_cell 3 4 0 a 0 b h (3*a+k)
  have hside := sideBit_d1pow_append a (3*a+k)
    (markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh) (by omega)
  rw [hleft] at hcell
  simp only [List.append_assoc] at hcell hside
  rw [hside] at hcell
  simpa only [List.append_assoc,
    show 3*a+k-3*a = k by omega] using hcell

private theorem m0EvenFourSweptLeftCell (a b : Nat) (h : Int) (k : Nat) :
    sweptLeft (3*a) (s1Config 3 4 0 a 0 b h).tape h
      (h - ((3*a : Nat) : Int) - (k : Int)) =
      sideBit (markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh) k := by
  have hpres := sweptLeft_preserves_left (3*a)
    (s1Config 3 4 0 a 0 b h).tape h
    (h - ((3*a : Nat) : Int) - (k : Int)) (by omega)
  rw [hpres]
  have hsrc := m0EvenFourSourceLeftAt a b h k
  have hcoord :
      h - ((3*a : Nat) : Int) - (k : Int) =
        h - ((3*a+k : Nat) : Int) := by omega
  rw [hcoord]
  exact hsrc

/-- After the counted left sweep of 3a cells, the complete fixed
[-12,3] input window is the 51-step bridge above. -/
theorem m0EvenFourBridge_input_match
    (a b : Nat) (h : Int) (ha : 0 < a) :
    ∀ y, m0EvenFourInside y = true →
      (sweptLeft (3*a) (s1Config 3 4 0 a 0 b h).tape h)
        (h - ((3*a : Nat) : Int) + y) =
          decide (y ∈ m0EvenFourBridgeStart.marked) := by
  intro y hy
  have hyb : -12 ≤ y ∧ y ≤ 3 := by
    simpa [m0EvenFourInside] using hy
  by_cases hy0 : y ≤ 0
  · let k : Nat := Int.toNat (-y)
    have hkcast : (k : Int) = -y := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord :
        h - ((3*a : Nat) : Int) + y =
          h - ((3*a : Nat) : Int) - (k : Int) := by omega
    rw [hcoord]
    have hleft := m0EvenFourSweptLeftCell a b h k
    have hbits :
        sideBit (markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh) k =
          decide (y ∈ m0EvenFourBridgeStart.marked) := by
      have hyCases :
          y = -12 ∨ y = -11 ∨ y = -10 ∨ y = -9 ∨ y = -8 ∨
          y = -7 ∨ y = -6 ∨ y = -5 ∨ y = -4 ∨ y = -3 ∨
          y = -2 ∨ y = -1 ∨ y = 0 := by omega
      rcases hyCases with h12 | h11 | h10 | h9 | h8 | h7 | h6 |
          h5 | h4 | h3 | h2 | h1 | h0
      all_goals subst y
      all_goals simp [k,m0EvenFourBridgeStart,markerWord,d0,d1,lh,sideBit]
    exact hleft.trans hbits
  · have hypos : 1 ≤ y := by omega
    have hyCases : y = 1 ∨ y = 2 ∨ y = 3 := by omega
    rcases hyCases with h1 | h2 | h3
    · subst y
      have hleft := sweptLeft_leftmost (3*a-1)
        (s1Config 3 4 0 a 0 b h).tape h
      have hcoord :
          h - ((3*a : Nat) : Int) + 1 =
            h - ((3*a-1 : Nat) : Int) := by omega
      rw [hcoord]
      have hN : 3*a-1+1 = 3*a := by omega
      simpa [m0EvenFourBridgeStart,hN] using hleft
    · subst y
      have hblock := sweptLeft_block (3*a) (3*a-2)
        (s1Config 3 4 0 a 0 b h).tape h (by omega)
      have hcoord :
          h - ((3*a : Nat) : Int) + 2 =
            h - ((3*a-2 : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m0EvenFourBridgeStart] using hblock
    · subst y
      by_cases ha1 : a = 1
      · subst a
        have hhead := sweptLeft_head 1
          (s1Config 3 4 0 1 0 b h).tape h
        have hcoord : h - ((3 : Nat) : Int) + 3 = h := by omega
        rw [hcoord]
        simpa [m0EvenFourBridgeStart] using hhead
      · have ha2 : 2 ≤ a := by omega
        have hblock := sweptLeft_block (3*a) (3*a-3)
          (s1Config 3 4 0 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a : Nat) : Int) + 3 =
              h - ((3*a-3 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m0EvenFourBridgeStart] using hblock

#print axioms m0EvenFourBridge_exact
#print axioms m0EvenFourBridge_heads
#print axioms m0EvenFourBridge_input_match

end BB6Coverage.Agent48M0EvenFourQ4Bridge
