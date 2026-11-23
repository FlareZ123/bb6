import CountedReset
import CountedSweep
import CountedQ4Prefix
import ChampionRootBridge
import S1Encoder
import Lean.Elab.Tactic.Omega

/-!
# m=0, n=6 even q4 bridge

The 39-step finite bridge for the residue-six source row.  It is
entered after the 3a-cell counted left sweep from
S1(L,8*k+6,0,a,0,b,h).  The finite certificate is independent of the
higher-order binary tail; the input-window match is proved below.
-/

namespace BB6Coverage.Agent42M0EvenSixQ4Bridge

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent6Q4Prefix

/-- The bridge reads only the 14-cell window [-10,3]. -/
def m0EvenSixInside (x : Int) : Bool :=
  decide (-10 ≤ x ∧ x ≤ 3)

def m0EvenSixBridgeStart : FConfig :=
  ⟨3, 0, [-10,-7,-6,-5,-4,-1,2,3]⟩

/-- Exact list order produced by `fMove`: newly written cells are
prepended. Its marked-cell set is the sorted endpoint
`{-10,-9,-8,-7,-4,-1,1,2,3}`; `embed` observes membership, not order. -/
def m0EvenSixBridgeEnd : FConfig :=
  ⟨4, 3, [2,1,-1,-4,-7,-8,-9,-10,3]⟩

/-- Exact 39-step run of the original TM2 table on the finite window. -/
theorem m0EvenSixBridge_exact :
    fRun tm2 39 m0EvenSixBridgeStart =
      some m0EvenSixBridgeEnd := by
  decide

/-- Every pre-transition head remains in the finite bridge window. -/
theorem m0EvenSixBridge_heads :
    (List.range 39).all (fun k =>
      match fRun tm2 k m0EvenSixBridgeStart with
      | none => true
      | some f => m0EvenSixInside f.head) = true := by
  decide

/-- Low three blocks of the source counter n=6. -/
theorem m0Even_binDec_three_six :
    binDec 3 6 = d1 ++ d0 ++ d0 := by
  have h1 : binDec 3 6 = d1 ++ binDec 2 3 := by
    simpa using binDec_even 2 3 (by decide)
  have h2 : binDec 2 3 = d0 ++ binDec 1 1 := by
    simpa using binDec_odd 1 1 (by decide)
  have h3 : binDec 1 1 = d0 ++ binDec 0 0 := by
    simpa using binDec_odd 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

/-- Low three blocks of the successor counter n-1=5. -/
theorem m0Even_binDec_three_five :
    binDec 3 5 = d0 ++ d1 ++ d0 := by
  have h1 : binDec 3 5 = d0 ++ binDec 2 2 := by
    simpa using binDec_odd 2 2 (by decide)
  have h2 : binDec 2 2 = d1 ++ binDec 1 1 := by
    simpa using binDec_even 1 1 (by decide)
  have h3 : binDec 1 1 = d0 ++ binDec 0 0 := by
    simpa using binDec_odd 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

private theorem m0EvenSixSourceLeftAt
    (a b : Nat) (h : Int) (k : Nat) :
    (s1Config 3 6 0 a 0 b h).tape
      (h - ((3*a+k : Nat) : Int)) =
      sideBit (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d0 ++ lh) k := by
  have hleft :
      s1LeftFacing 3 6 0 a 0 =
        d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d0 ++ d0 ++ lh := by
    simp [s1LeftFacing,binDec_zero,m0Even_binDec_three_six,List.append_assoc]
  have hcell := s1Config_left_cell 3 6 0 a 0 b h (3*a+k)
  have hside := sideBit_d1pow_append a (3*a+k)
    (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d0 ++ lh) (by omega)
  rw [hleft] at hcell
  simp only [List.append_assoc] at hcell hside
  rw [hside] at hcell
  simpa only [List.append_assoc,
    show 3*a+k-3*a = k by omega] using hcell

private theorem m0EvenSixSweptLeftCell
    (a b : Nat) (h : Int) (k : Nat) :
    sweptLeft (3*a) (s1Config 3 6 0 a 0 b h).tape h
      (h - ((3*a : Nat) : Int) - (k : Int)) =
      sideBit (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d0 ++ lh) k := by
  have hpres := sweptLeft_preserves_left (3*a)
    (s1Config 3 6 0 a 0 b h).tape h
    (h - ((3*a : Nat) : Int) - (k : Int)) (by omega)
  rw [hpres]
  have hsrc := m0EvenSixSourceLeftAt a b h k
  have hcoord :
      h - ((3*a : Nat) : Int) - (k : Int) =
        h - ((3*a+k : Nat) : Int) := by omega
  rw [hcoord]
  exact hsrc

/-- After the counted left sweep, the complete fixed [-10,3] input
window is exactly the 39-step bridge above. -/
theorem m0EvenSixBridge_input_match
    (a b : Nat) (h : Int) (ha : 0 < a) :
    ∀ y, m0EvenSixInside y = true →
      (sweptLeft (3*a) (s1Config 3 6 0 a 0 b h).tape h)
        (h - ((3*a : Nat) : Int) + y) =
          decide (y ∈ m0EvenSixBridgeStart.marked) := by
  intro y hy
  have hyb : -10 ≤ y ∧ y ≤ 3 := by
    simpa [m0EvenSixInside] using hy
  by_cases hy0 : y ≤ 0
  · let k : Nat := Int.toNat (-y)
    have hkcast : (k : Int) = -y := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord :
        h - ((3*a : Nat) : Int) + y =
          h - ((3*a : Nat) : Int) - (k : Int) := by omega
    rw [hcoord]
    have hleft := m0EvenSixSweptLeftCell a b h k
    have hbits :
        sideBit (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d0 ++ lh) k =
          decide (y ∈ m0EvenSixBridgeStart.marked) := by
      have hyCases :
          y = -10 ∨ y = -9 ∨ y = -8 ∨ y = -7 ∨ y = -6 ∨
          y = -5 ∨ y = -4 ∨ y = -3 ∨ y = -2 ∨ y = -1 ∨
          y = 0 := by omega
      rcases hyCases with h10 | h9 | h8 | h7 | h6 | h5 |
          h4 | h3 | h2 | h1 | h0
      all_goals subst y
      all_goals simp [k,m0EvenSixBridgeStart,markerWord,d0,d1,lh,sideBit]
    exact hleft.trans hbits
  · have hypos : 1 ≤ y := by omega
    have hyCases : y = 1 ∨ y = 2 ∨ y = 3 := by omega
    rcases hyCases with h1 | h2 | h3
    · subst y
      have hleft := sweptLeft_leftmost (3*a-1)
        (s1Config 3 6 0 a 0 b h).tape h
      have hcoord :
          h - ((3*a : Nat) : Int) + 1 =
            h - ((3*a-1 : Nat) : Int) := by omega
      rw [hcoord]
      have hN : 3*a-1+1 = 3*a := by omega
      simpa [m0EvenSixBridgeStart,hN] using hleft
    · subst y
      have hblock := sweptLeft_block (3*a) (3*a-2)
        (s1Config 3 6 0 a 0 b h).tape h (by omega)
      have hcoord :
          h - ((3*a : Nat) : Int) + 2 =
            h - ((3*a-2 : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m0EvenSixBridgeStart] using hblock
    · subst y
      by_cases ha1 : a = 1
      · subst a
        have hhead := sweptLeft_head 1
          (s1Config 3 6 0 1 0 b h).tape h
        have hcoord : h - ((3 : Nat) : Int) + 3 = h := by omega
        rw [hcoord]
        simpa [m0EvenSixBridgeStart] using hhead
      · have ha2 : 2 ≤ a := by omega
        have hblock := sweptLeft_block (3*a) (3*a-3)
          (s1Config 3 6 0 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a : Nat) : Int) + 3 =
              h - ((3*a-3 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m0EvenSixBridgeStart] using hblock

#print axioms m0EvenSixBridge_exact
#print axioms m0EvenSixBridge_heads
#print axioms m0EvenSixBridge_input_match

end BB6Coverage.Agent42M0EvenSixQ4Bridge
