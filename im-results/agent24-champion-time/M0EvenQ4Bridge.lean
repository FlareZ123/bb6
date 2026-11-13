/-!
# m=0,n=2 even q4 bridge

A fixed 39-step local bridge for the next S1 reset stage.  It is entered
after the counted left sweep of 3a cells and is parameterized by the
source left/right counters through the input-frame theorem below.
-/

import CountedReset
import ChampionRootBridge
import S1Encoder
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent24M0EvenQ4Bridge

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset

def m0EvenQ4Inside (x : Int) : Bool := decide (-9 ≤ x ∧ x ≤ 3)

def m0EvenQ4BridgeStart : FConfig :=
  ⟨3, 0, [-7,-6,-5,-4,-1,2,3]⟩

def m0EvenQ4BridgeEnd : FConfig :=
  ⟨4, 3, [-9,-8,-7,-4,-1,1,2,3]⟩

theorem m0EvenQ4Bridge_exact :
    fRun tm2 39 m0EvenQ4BridgeStart = some m0EvenQ4BridgeEnd := by
  decide

theorem m0EvenQ4Bridge_heads :
    (List.range 39).all (fun k =>
      match fRun tm2 k m0EvenQ4BridgeStart with
      | none => true
      | some f => m0EvenQ4Inside f.head) = true := by
  decide

private theorem binDec_three_two :
    binDec 3 2 = d1 ++ d0 ++ d1 := by
  have h1 : binDec 3 2 = d1 ++ binDec 2 1 := by
    simpa using binDec_even 2 1 (by decide)
  have h2 : binDec 2 1 = d0 ++ binDec 1 0 := by
    simpa using binDec_odd 1 0 (by decide)
  have h3 : binDec 1 0 = d1 ++ binDec 0 0 := by
    simpa using binDec_even 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

private theorem binDec_three_one :
    binDec 3 1 = d0 ++ d1 ++ d1 := by
  have h1 : binDec 3 1 = d0 ++ binDec 2 0 := by
    simpa using binDec_odd 2 0 (by decide)
  have h2 : binDec 2 0 = d1 ++ binDec 1 0 := by
    simpa using binDec_even 1 0 (by decide)
  have h3 : binDec 1 0 = d1 ++ binDec 0 0 := by
    simpa using binDec_even 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

private theorem m0EvenSourceLeftAt (a b : Nat) (h : Int) (k : Nat) :
    (s1Config 3 2 0 a 0 b h).tape
      (h - ((3*a+k : Nat) : Int)) =
      sideBit (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh) k := by
  have hleft :
      s1LeftFacing 3 2 0 a 0 =
        d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh := by
    simp [s1LeftFacing,binDec_zero,binDec_three_two,List.append_assoc]
  have hcell := s1Config_left_cell 3 2 0 a 0 b h (3*a+k)
  have hside := sideBit_d1pow_append a (3*a+k)
    (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh) (by omega)
  rw [hleft] at hcell
  simp only [List.append_assoc] at hcell hside
  rw [hside] at hcell
  simpa only [List.append_assoc,
    show 3*a+k-3*a = k by omega] using hcell

private theorem m0EvenSweptLeftCell (a b : Nat) (h : Int) (k : Nat) :
    sweptLeft (3*a) (s1Config 3 2 0 a 0 b h).tape h
      (h - ((3*a : Nat) : Int) - (k : Int)) =
      sideBit (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh) k := by
  have hpres := sweptLeft_preserves_left (3*a)
    (s1Config 3 2 0 a 0 b h).tape h
    (h - ((3*a : Nat) : Int) - (k : Int)) (by omega)
  rw [hpres]
  have hsrc := m0EvenSourceLeftAt a b h k
  have hcoord :
      h - ((3*a : Nat) : Int) - (k : Int) =
        h - ((3*a+k : Nat) : Int) := by omega
  rw [hcoord]
  exact hsrc

/-- After the counted left sweep of 3a cells, the complete fixed
[-9,3] input window is the 39-step bridge above. -/
theorem m0EvenQ4Bridge_input_match (a b : Nat) (h : Int) (ha : 0 < a) :
    ∀ y, m0EvenQ4Inside y = true →
      (sweptLeft (3*a) (s1Config 3 2 0 a 0 b h).tape h)
        (h - ((3*a : Nat) : Int) + y) =
          decide (y ∈ m0EvenQ4BridgeStart.marked) := by
  intro y hy
  have hyb : -9 ≤ y ∧ y ≤ 3 := by
    simpa [m0EvenQ4Inside] using hy
  by_cases hy0 : y ≤ 0
  · let k : Nat := Int.toNat (-y)
    have hkcast : (k : Int) = -y := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord :
        h - ((3*a : Nat) : Int) + y =
          h - ((3*a : Nat) : Int) - (k : Int) := by omega
    rw [hcoord]
    have hleft := m0EvenSweptLeftCell a b h k
    have hbits :
        sideBit (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh) k =
          decide (y ∈ m0EvenQ4BridgeStart.marked) := by
      have hyCases : y = -9 ∨ y = -8 ∨ y = -7 ∨ y = -6 ∨ y = -5 ∨
          y = -4 ∨ y = -3 ∨ y = -2 ∨ y = -1 ∨ y = 0 := by omega
      rcases hyCases with h9 | h8 | h7 | h6 | h5 | h4 | h3 | h2 | h1 | h0
      all_goals subst y
      all_goals simp [k,m0EvenQ4BridgeStart,markerWord,d0,d1,lh,sideBit]
    exact hleft.trans hbits
  · have hypos : 1 ≤ y := by omega
    have hyCases : y = 1 ∨ y = 2 ∨ y = 3 := by omega
    rcases hyCases with h1 | h2 | h3
    · subst y
      have hleft := sweptLeft_leftmost (3*a-1)
        (s1Config 3 2 0 a 0 b h).tape h
      have hcoord :
          h - ((3*a : Nat) : Int) + 1 =
            h - ((3*a-1 : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m0EvenQ4BridgeStart] using hleft
    · subst y
      have hblock := sweptLeft_block (3*a) (3*a-2)
        (s1Config 3 2 0 a 0 b h).tape h (by omega)
      have hcoord :
          h - ((3*a : Nat) : Int) + 2 =
            h - ((3*a-2 : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m0EvenQ4BridgeStart] using hblock
    · subst y
      by_cases ha1 : a = 1
      · subst a
        have hhead := sweptLeft_head 1
          (s1Config 3 2 0 1 0 b h).tape h
        have hcoord : h - ((3 : Nat) : Int) + 3 = h := by omega
        rw [hcoord]
        simpa [m0EvenQ4BridgeStart] using hhead
      · have ha2 : 2 ≤ a := by omega
        have hblock := sweptLeft_block (3*a) (3*a-3)
          (s1Config 3 2 0 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a : Nat) : Int) + 3 =
              h - ((3*a-3 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m0EvenQ4BridgeStart] using hblock

#print axioms m0EvenQ4Bridge_exact
#print axioms m0EvenQ4Bridge_heads
#print axioms m0EvenQ4Bridge_input_match

end BB6Coverage.Agent24M0EvenQ4Bridge
