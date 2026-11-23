import Q4RightEndpoint
import Lean.Elab.Tactic.Omega

/-!
# The m=2,n=6 even q4 reset branch

This module establishes the m=2,n=6 even reset kernel, the next source row after the root-specific m=0,n=16r+7 successor.
The new finite kernel is a 38-step bridge, following the standard
(3*a+2)-block counted left sweep and preceding the 3*a E-state scan.
The resulting q4 cut is at state E/head h and feeds the generic full-tape
q4 suffix endpoint. This file stops at the reset-prefix source theorem; the
independent counted-drain composition remains a separate reusable step.
-/

namespace BB6Coverage.Agent48M2EvenSixQ4

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24Q4Endpoint
open BB6ChampionArithmetic

private theorem binDec_three_six :
    binDec 3 6 = d1 ++ d0 ++ d0 := by
  decide

private theorem binDec_three_five :
    binDec 3 5 = d0 ++ d1 ++ d0 := by
  decide

private def m2EvenSixSourceLeftSuffix : List Bool :=
  markerWord 2 ++ (d0 ++ (binDec 3 6 ++ lh))

private def m2EvenSixQ4LeftSuffix : List Bool :=
  markerWord 1 ++ (d0 ++ (binDec 3 5 ++ lh))

/-- The left-facing q4 word at the state-E cut. -/
def m2EvenSixQ4LeftFacing (a : Nat) : List Bool :=
  [true] ++ (d1pow a ++ m2EvenSixQ4LeftSuffix)

/-- The base q4 cut word is the canonical q4 left-facing word. -/
theorem m2EvenSixQ4LeftFacing_eq_q4LeftFacing (a : Nat) :
    m2EvenSixQ4LeftFacing a = Agent8Q4Suffix.q4LeftFacing 3 5 a := by
  simp [m2EvenSixQ4LeftFacing,m2EvenSixQ4LeftSuffix,
    Agent8Q4Suffix.q4LeftFacing,List.append_assoc]

/-- The finite bridge sees the even-n=6 boundary, not the odd-n boundary
used by Agent 6's 26-step m=2 bridge. -/
def m2EvenSixQ4Inside (x : Int) : Bool :=
  decide (-9 ≤ x ∧ x ≤ 2)

def m2EvenSixQ4BridgeStart : FConfig :=
  ⟨3,0,[-7,-6,-5,-4,-1,2]⟩

def m2EvenSixQ4BridgeEnd : FConfig :=
  ⟨4,2,[1,-1,-4,-7,-8,-9,2]⟩

theorem m2EvenSixQ4Bridge_exact :
    fRun tm2 38 m2EvenSixQ4BridgeStart =
      some m2EvenSixQ4BridgeEnd := by
  decide

theorem m2EvenSixQ4Bridge_heads :
    (List.range 38).all (fun k =>
      match fRun tm2 k m2EvenSixQ4BridgeStart with
      | none => true
      | some f => m2EvenSixQ4Inside f.head) = true := by
  decide

/-- The post-sweep source suffix, indexed from the new D head. -/
private theorem m2EvenSixSourceLeftAt (a b : Nat) (h : Int) (k : Nat) :
    (s1Config 3 6 2 a 0 b h).tape
        (h-((3*a+2+k : Nat) : Int)) =
      sideBit m2EvenSixSourceLeftSuffix (2+k) := by
  have hface : s1LeftFacing 3 6 2 a 0 =
      d1pow a ++ m2EvenSixSourceLeftSuffix := by
    simp [s1LeftFacing,binDec_zero,m2EvenSixSourceLeftSuffix,
      List.append_assoc]
  have hcell := s1Config_left_cell 3 6 2 a 0 b h (3*a+2+k)
  rw [hface] at hcell
  have hside := sideBit_d1pow_append a (3*a+2+k)
    m2EvenSixSourceLeftSuffix (by omega)
  rw [hside] at hcell
  have hidx : 3*a+2+k-3*a = 2+k := by omega
  simpa [hidx] using hcell

private theorem m2EvenSixSweptLeftCell (a b : Nat) (h : Int) (k : Nat) :
    sweptLeft (3*a+2) (s1Config 3 6 2 a 0 b h).tape h
        (h-((3*a+2+k : Nat) : Int)) =
      sideBit m2EvenSixSourceLeftSuffix (2+k) := by
  let T := (s1Config 3 6 2 a 0 b h).tape
  have hpres := sweptLeft_preserves_left (3*a+2) T h
    (h-((3*a+2+k : Nat) : Int)) (by omega)
  have hcoord :
      h-((3*a+2+k : Nat) : Int) =
        h-((3*a+2 : Nat) : Int)-(k:Int) := by omega
  have hsrc := m2EvenSixSourceLeftAt a b h k
  have hcombined := hpres.trans hsrc
  simpa only [hcoord] using hcombined

/-- Exact input match for the 38-step bridge after sweeping the 3*a+2
leading one-blocks. -/
theorem m2EvenSixQ4Bridge_input_match (a b : Nat) (h : Int) :
    ∀ y, m2EvenSixQ4Inside y = true →
      (sweptLeft (3*a+2) (s1Config 3 6 2 a 0 b h).tape h)
        (h-((3*a+2 : Nat) : Int)+y) =
          decide (y ∈ m2EvenSixQ4BridgeStart.marked) := by
  intro y hy
  have hyb : -9 ≤ y ∧ y ≤ 2 := by
    simpa [m2EvenSixQ4Inside] using hy
  by_cases hy0 : y ≤ 0
  · let k : Nat := Int.toNat (-y)
    have hkcast : (k:Int) = -y := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord :
        h-((3*a+2 : Nat) : Int)+y =
          h-((3*a+2 : Nat) : Int)-(k:Int) := by omega
    rw [hcoord]
    have hleft := m2EvenSixSweptLeftCell a b h k
    have hbits :
        sideBit m2EvenSixSourceLeftSuffix (2+k) =
          decide (y ∈ m2EvenSixQ4BridgeStart.marked) := by
      have hyCases :
          y = -9 ∨ y = -8 ∨ y = -7 ∨ y = -6 ∨ y = -5 ∨
          y = -4 ∨ y = -3 ∨ y = -2 ∨ y = -1 ∨ y = 0 := by omega
      rcases hyCases with h9 | h8 | h7 | h6 | h5 |
          h4 | h3 | h2 | h1 | h0
      all_goals subst y
      all_goals simp [k,m2EvenSixSourceLeftSuffix,markerWord,d0,d1,lh,
        binDec_three_six,sideBit,m2EvenSixQ4BridgeStart]
    have hcoord' : h-((3*a+2+k:Nat):Int) =
        h-((3*a+2:Nat):Int)-(k:Int) := by omega
    rw [hcoord'] at hleft
    exact hleft.trans hbits
  · have hyCases : y = 1 ∨ y = 2 := by omega
    rcases hyCases with h1 | h2
    · subst y
      have hleft := sweptLeft_leftmost (3*a+1)
        (s1Config 3 6 2 a 0 b h).tape h
      have hcoord :
          h-((3*a+2 : Nat) : Int)+1 =
            h-((3*a+1 : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m2EvenSixQ4BridgeStart] using hleft
    · subst y
      have hleft := sweptLeft_block (3*a+2) (3*a)
        (s1Config 3 6 2 a 0 b h).tape h (by omega)
      have hcoord :
          h-((3*a+2 : Nat) : Int)+2 =
            h-((3*a : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m2EvenSixQ4BridgeStart] using hleft

/-- Explicit tape at the m=2,n=4 even q4 cut. -/
def m2EvenSixQ4CutTape (a b : Nat) (h : Int) : Int → Bool :=
  let T := (s1Config 3 6 2 a 0 b h).tape
  let N := 3*a+2
  let T1 := sweptLeft N T h
  (frameAt T1 (h-(N:Int)) m2EvenSixQ4Inside m2EvenSixQ4BridgeEnd).tape

private theorem m2EvenSixQ4CutTape_eq_swept
    (a b : Nat) (h x : Int)
    (hout : m2EvenSixQ4Inside
      (x-(h-((3*a+2 : Nat) : Int))) = false) :
    m2EvenSixQ4CutTape a b h x =
      sweptLeft (3*a+2) (s1Config 3 6 2 a 0 b h).tape h x := by
  let T := (s1Config 3 6 2 a 0 b h).tape
  let N := 3*a+2
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_outside T1 (h-(N:Int))
    m2EvenSixQ4Inside m2EvenSixQ4BridgeEnd x hout
  simpa [m2EvenSixQ4CutTape,T,N,T1] using hf

private theorem m2EvenSixQ4CutTape_eq_end_inside
    (a b : Nat) (h x : Int)
    (hin : m2EvenSixQ4Inside
      (x-(h-((3*a+2 : Nat) : Int))) = true) :
    m2EvenSixQ4CutTape a b h x =
      decide ((x-(h-((3*a+2 : Nat) : Int))) ∈
        m2EvenSixQ4BridgeEnd.marked) := by
  let T := (s1Config 3 6 2 a 0 b h).tape
  let N := 3*a+2
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_inside T1 (h-(N:Int))
    m2EvenSixQ4Inside m2EvenSixQ4BridgeEnd x hin
  simpa [m2EvenSixQ4CutTape,T,N,T1] using hf

/-- The target q4 left stream has 3*a+2 leading ones. -/
theorem m2EvenSixQ4LeftFacingPrefixTrue (a i : Nat)
    (hi : i ≤ 3*a+1) :
    sideBit (m2EvenSixQ4LeftFacing a) i = true := by
  by_cases hi0 : i = 0
  · subst i
    simp [m2EvenSixQ4LeftFacing,sideBit]
  · have hpos : 1 ≤ i := by omega
    have hface : m2EvenSixQ4LeftFacing a =
        [true] ++ (d1pow a ++ m2EvenSixQ4LeftSuffix) := by
      simp [m2EvenSixQ4LeftFacing,m2EvenSixQ4LeftSuffix,List.append_assoc]
    have hside :
        sideBit (m2EvenSixQ4LeftFacing a) i =
          sideBit (d1pow a ++ m2EvenSixQ4LeftSuffix) (i-1) := by
      rw [hface]
      exact sideBit_append_right [true]
        (d1pow a ++ m2EvenSixQ4LeftSuffix) i (by simp; omega)
    by_cases hlt : i-1 < 3*a
    · have hfirst := sideBit_append_left (d1pow a)
        m2EvenSixQ4LeftSuffix (i-1) (by rw [d1pow_length]; omega)
      rw [hfirst] at hside
      rw [hside]
      exact sideBit_d1pow_true a (i-1) hlt
    · have heq : i-1 = 3*a := by omega
      have hlast := sideBit_append_right (d1pow a)
        m2EvenSixQ4LeftSuffix (3*a) (by rw [d1pow_length]; omega)
      rw [heq,hlast] at hside
      rw [hside]
      have hlen : (d1pow a).length = 3*a := by simp [d1pow_length]
      rw [hlen]
      simp [m2EvenSixQ4LeftSuffix,markerWord,sideBit]

/-- The 10-cell boundary written by the 38-step bridge is exactly the
marker-1/digit/BinDec boundary of the next S1 state. -/
theorem m2EvenSixQ4LeftFacingBridgeBit (a j : Nat)
    (hj : j ≤ 9) :
    sideBit (m2EvenSixQ4LeftFacing a) (3*a+2+j) =
      decide ((-(j:Int)) ∈ m2EvenSixQ4BridgeEnd.marked) := by
  have hface : m2EvenSixQ4LeftFacing a =
      [true] ++ (d1pow a ++ m2EvenSixQ4LeftSuffix) := by
    simp [m2EvenSixQ4LeftFacing,m2EvenSixQ4LeftSuffix,List.append_assoc]
  have hfirst :
      sideBit (m2EvenSixQ4LeftFacing a) (3*a+2+j) =
        sideBit (d1pow a ++ m2EvenSixQ4LeftSuffix) (3*a+1+j) := by
    rw [hface]
    have happ := sideBit_append_right [true]
      (d1pow a ++ m2EvenSixQ4LeftSuffix) (3*a+2+j) (by simp; omega)
    have hidx : 3*a+2+j-1 = 3*a+1+j := by omega
    simpa [hidx] using happ
  have hsecond :
      sideBit (d1pow a ++ m2EvenSixQ4LeftSuffix) (3*a+1+j) =
        sideBit m2EvenSixQ4LeftSuffix (j+1) := by
    have happ := sideBit_append_right (d1pow a)
      m2EvenSixQ4LeftSuffix (3*a+1+j) (by rw [d1pow_length]; omega)
    have hidx : 3*a+1+j-3*a = j+1 := by omega
    rw [d1pow_length] at happ
    simpa [hidx] using happ
  have hbits :
      sideBit m2EvenSixQ4LeftSuffix (j+1) =
        decide ((-(j:Int)) ∈ m2EvenSixQ4BridgeEnd.marked) := by
    have hjCases :
        j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨
        j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
    rcases hjCases with h0 | h1 | h2 | h3 | h4 |
        h5 | h6 | h7 | h8 | h9
    all_goals subst j
    all_goals simp [m2EvenSixQ4LeftSuffix,markerWord,d0,d1,lh,
      binDec_three_five,sideBit,m2EvenSixQ4BridgeEnd]
  calc
    sideBit (m2EvenSixQ4LeftFacing a) (3*a+2+j) =
        sideBit (d1pow a ++ m2EvenSixQ4LeftSuffix) (3*a+1+j) :=
      hfirst
    _ = sideBit m2EvenSixQ4LeftSuffix (j+1) := hsecond
    _ = decide ((-(j:Int)) ∈ m2EvenSixQ4BridgeEnd.marked) := hbits

/-- The source and target left streams share the same final one and lh
tail from index 3*a+12 onward. -/
private theorem m2EvenSixQ4LeftFacingTail (a i : Nat)
    (hi : 3*a+12 ≤ i) :
    sideBit (s1LeftFacing 3 6 2 a 0) i =
      sideBit (m2EvenSixQ4LeftFacing a) i := by
  let shared : List Bool := [true] ++ d0 ++ lh
  let sourcePrefix : List Bool :=
    d1pow a ++ markerWord 2 ++ d0 ++ d1 ++ [false,false]
  let targetPrefix : List Bool :=
    [true] ++ d1pow a ++ markerWord 1 ++ d0 ++ d0 ++ [true,true]
  have hsrc : s1LeftFacing 3 6 2 a 0 = sourcePrefix ++ shared := by
    simp [s1LeftFacing,binDec_zero,sourcePrefix,shared,
      binDec_three_six,d0,d1,List.append_assoc]
  have htgt : m2EvenSixQ4LeftFacing a = targetPrefix ++ shared := by
    simp [m2EvenSixQ4LeftFacing,m2EvenSixQ4LeftSuffix,targetPrefix,shared,
      binDec_three_five,d0,d1,List.append_assoc]
  have hlenS : sourcePrefix.length = 3*a+12 := by
    simp [sourcePrefix,d1pow_length,markerWord,d0,d1] <;> omega
  have hlenT : targetPrefix.length = 3*a+12 := by
    simp [targetPrefix,d1pow_length,markerWord,d0,d1] <;> omega
  rw [hsrc,htgt]
  rw [sideBit_append_right sourcePrefix shared i (by rw [hlenS]; omega)]
  rw [sideBit_append_right targetPrefix shared i (by rw [hlenT]; omega)]
  rw [hlenS,hlenT]

/-- The head cell at the q4 cut is one. -/
private theorem m2EvenSixQ4CutTape_head (a b : Nat) (h : Int)
    (ha : 0 < a) :
    m2EvenSixQ4CutTape a b h h = true := by
  let T := (s1Config 3 6 2 a 0 b h).tape
  let N := 3*a+2
  have hrel : h-(h-(N:Int)) = (N:Int) := by omega
  have hout : m2EvenSixQ4Inside (h-(h-(N:Int))) = false := by
    simp [m2EvenSixQ4Inside,hrel,N]
    omega
  have hcut := m2EvenSixQ4CutTape_eq_swept a b h h hout
  have hs : sweptLeft N T h h = true := by
    simpa [N] using sweptLeft_head (3*a) T h
  exact hcut.trans (by simpa [T] using hs)

/-- The right stream at the q4 cut is the standard q4 right word. -/
private theorem m2EvenSixQ4CutTape_rightFacing (a b : Nat) (h : Int)
    (ha : 0 < a) :
    ∀ i : Nat,
      m2EvenSixQ4CutTape a b h (h+1+(i:Int)) =
        sideBit (q4RightFacing b) i := by
  intro i
  cases i with
  | zero =>
      let T := (s1Config 3 6 2 a 0 b h).tape
      let N := 3*a+2
      have hrel : (h+1)-(h-(N:Int)) = (N:Int)+1 := by omega
      have hout : m2EvenSixQ4Inside ((h+1)-(h-(N:Int))) = false := by
        simp [m2EvenSixQ4Inside,hrel,N]
        omega
      have hcut := m2EvenSixQ4CutTape_eq_swept a b h (h+1) hout
      have hplus : sweptLeft N T h (h+1) = true := by
        simpa [N] using sweptLeft_plus1 (3*a+1) T h
      have hactual : m2EvenSixQ4CutTape a b h (h+1) = true :=
        hcut.trans (by simpa [T] using hplus)
      simpa [q4RightFacing,sideBit] using hactual
  | succ i =>
      let T := (s1Config 3 6 2 a 0 b h).tape
      let N := 3*a+2
      let x : Int := h+1+((i+1:Int))
      have hrel : x-(h-(N:Int)) = (N:Int)+2+(i:Int) := by
        dsimp [x]
        omega
      have hout : m2EvenSixQ4Inside (x-(h-(N:Int))) = false := by
        simp [m2EvenSixQ4Inside,hrel,N]
        omega
      have hcut := m2EvenSixQ4CutTape_eq_swept a b h x hout
      have hpres : sweptLeft N T h x = T x := by
        exact sweptLeft_preserves_right N T h x (by dsimp [x]; omega)
      have hsource : T x = sideBit (s0RightFacing b) (i+1) := by
        have hc := s1Config_right_cell 3 6 2 a 0 b h (i+1)
        simpa [T,x,s1PhysicalRight,s0PhysicalRight] using hc
      calc
        m2EvenSixQ4CutTape a b h (h+1+((i+1:Int))) =
            sweptLeft N T h x := hcut
        _ = T x := hpres
        _ = sideBit (s0RightFacing b) (i+1) := hsource
        _ = sideBit (q4RightFacing b) (i+1) :=
          (q4RightFacing_succ b i).symm

/-- The complete left stream at the q4 cut. -/
private theorem m2EvenSixQ4CutTape_leftFacing (a b : Nat) (h : Int)
    (ha : 0 < a)
    (hhead : m2EvenSixQ4CutTape a b h h = true) :
    ∀ i : Nat,
      m2EvenSixQ4CutTape a b h (h-(i:Int)) =
        sideBit (m2EvenSixQ4LeftFacing a) i := by
  intro i
  by_cases hi0 : i = 0
  · subst i
    simpa [sideBit,m2EvenSixQ4LeftFacing] using hhead
  · have hpos : 1 ≤ i := by omega
    by_cases hpre : i ≤ 3*a+1
    · have htarget := m2EvenSixQ4LeftFacingPrefixTrue a i hpre
      by_cases htop : i = 3*a ∨ i = 3*a+1
      · rcases htop with hi3 | hi4
        · subst i
          have hrel : (h-((3*a:Int)))-(h-((3*a+2:Int))) = 2 := by omega
          have hin : m2EvenSixQ4Inside
              ((h-((3*a:Int)))-(h-((3*a+2:Int)))) = true := by
            simp [m2EvenSixQ4Inside,hrel]
          have hcut := m2EvenSixQ4CutTape_eq_end_inside a b h
            (h-((3*a:Int))) hin
          have hmark :
              decide ((h-((3*a:Int)))-(h-((3*a+2:Int))) ∈
                m2EvenSixQ4BridgeEnd.marked) = true := by
            rw [hrel]
            simp [m2EvenSixQ4BridgeEnd]
          have hactual : m2EvenSixQ4CutTape a b h (h-((3*a:Int))) = true :=
            hcut.trans hmark
          exact hactual.trans htarget.symm
        · subst i
          have hrel : (h-((3*a+1:Int)))-(h-((3*a+2:Int))) = 1 := by omega
          have hin : m2EvenSixQ4Inside
              ((h-((3*a+1:Int)))-(h-((3*a+2:Int)))) = true := by
            simp [m2EvenSixQ4Inside,hrel]
          have hcut := m2EvenSixQ4CutTape_eq_end_inside a b h
            (h-((3*a+1:Int))) hin
          have hmark :
              decide ((h-((3*a+1:Int)))-(h-((3*a+2:Int))) ∈
                m2EvenSixQ4BridgeEnd.marked) = true := by
            rw [hrel]
            simp [m2EvenSixQ4BridgeEnd]
          have hactual : m2EvenSixQ4CutTape a b h (h-((3*a+1:Int))) = true :=
            hcut.trans hmark
          exact hactual.trans htarget.symm
      · have hsmall : i ≤ 3*a-1 := by omega
        have hrel :
            (h-(i:Int))-(h-((3*a+2:Int))) =
              ((3*a+2-i : Nat) : Int) := by omega
        have hout : m2EvenSixQ4Inside
            ((h-(i:Int))-(h-((3*a+2:Int)))) = false := by
          simp [m2EvenSixQ4Inside,hrel]
          omega
        have hcut := m2EvenSixQ4CutTape_eq_swept a b h (h-(i:Int)) hout
        have hblock := sweptLeft_block (3*a+2) i
          (s1Config 3 6 2 a 0 b h).tape h (by omega)
        have hactual :
            m2EvenSixQ4CutTape a b h (h-(i:Int)) = true := by
          exact hcut.trans (by simpa using hblock)
        exact hactual.trans htarget.symm
    · by_cases hbridge : i ≤ 3*a+11
      · have hlow : 3*a+2 ≤ i := by omega
        let j : Nat := i-(3*a+2)
        have hj : j ≤ 9 := by dsimp [j]; omega
        have hrel :
            (h-(i:Int))-(h-((3*a+2:Int))) = -(j:Int) := by
          dsimp [j]
          omega
        have hin : m2EvenSixQ4Inside
            ((h-(i:Int))-(h-((3*a+2:Int)))) = true := by
          simp [m2EvenSixQ4Inside,hrel]
          exact_mod_cast hj
        have hcut := m2EvenSixQ4CutTape_eq_end_inside a b h
          (h-(i:Int)) hin
        have htarget :
            sideBit (m2EvenSixQ4LeftFacing a) i =
              decide ((-(j:Int)) ∈ m2EvenSixQ4BridgeEnd.marked) := by
          have hidx : i = 3*a+2+j := by dsimp [j]; omega
          rw [hidx]
          exact m2EvenSixQ4LeftFacingBridgeBit a j hj
        have hmark :
            decide ((h-(i:Int))-(h-((3*a+2:Int))) ∈
              m2EvenSixQ4BridgeEnd.marked) =
              sideBit (m2EvenSixQ4LeftFacing a) i := by
          rw [hrel]
          exact htarget.symm
        exact hcut.trans hmark
      · have htail : 3*a+12 ≤ i := by omega
        have hrel :
            (h-(i:Int))-(h-((3*a+2:Int))) =
              (3*a+2:Int)-(i:Int) := by omega
        have hout : m2EvenSixQ4Inside
            ((h-(i:Int))-(h-((3*a+2:Int)))) = false := by
          simp [m2EvenSixQ4Inside,hrel]
          omega
        have hcut := m2EvenSixQ4CutTape_eq_swept a b h (h-(i:Int)) hout
        have hpres := sweptLeft_preserves_left (3*a+2)
          (s1Config 3 6 2 a 0 b h).tape h (h-(i:Int)) (by omega)
        have hcell := s1Config_left_cell 3 6 2 a 0 b h i
        have htailEq := m2EvenSixQ4LeftFacingTail a i htail
        calc
          m2EvenSixQ4CutTape a b h (h-(i:Int)) =
              sweptLeft (3*a+2) (s1Config 3 6 2 a 0 b h).tape h
                (h-(i:Int)) := hcut
          _ = (s1Config 3 6 2 a 0 b h).tape (h-(i:Int)) := hpres
          _ = sideBit (s1LeftFacing 3 6 2 a 0) i := hcell
          _ = sideBit (m2EvenSixQ4LeftFacing a) i := htailEq

private theorem m2EvenSixQ4RightShape_of_stream (T : Int → Bool)
    (h : Int) (b : Nat)
    (hhead : T h = true)
    (hright : ∀ i : Nat,
      T (h+1+(i:Int)) = sideBit (q4RightFacing b) i) :
    BB6Coverage.Agent8Q4Suffix.q4RightShape T h b := by
  unfold BB6Coverage.Agent8Q4Suffix.q4RightShape
  constructor
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      simpa using hhead
    · have hidx : i-1 < 4 := by omega
      have hq := q4RightFacing_first4 b (i-1) hidx
      have hr := hright (i-1)
      have hcoord : h+(i:Int) = h+1+((i-1:Int)) := by omega
      have hcast : ((i-1 : Nat) : Int) = (i:Int)-1 := by omega
      rw [hcast] at hr
      rw [hcoord]
      calc
        T (h+1+((i-1:Int))) =
            sideBit (q4RightFacing b) (i-1) := hr
        _ = true := hq
  · constructor
    · have hr := hright 4
      rw [q4RightFacing_at4] at hr
      have hcoord : h+1+(4:Int) = h+5 := by omega
      simpa [hcoord] using hr
    · constructor
      · have hr := hright 5
        rw [q4RightFacing_at5] at hr
        have hcoord : h+1+(5:Int) = h+6 := by omega
        simpa [hcoord] using hr
      · constructor
        · intro i hi
          have hq := q4RightFacing_suffix b i hi
          have hr := hright (6+i)
          rw [hq] at hr
          have hcoord : h+1+((6+i:Int)) = h+7+(i:Int) := by omega
          simpa [hcoord] using hr
        · intro i hi
          have hq :
              sideBit (q4RightFacing b) (9+3*b+i) = false := by
            apply sideBit_ge_length
            rw [q4RightFacing_length]
            omega
          have hr := hright (9+3*b+i)
          rw [hq] at hr
          have hcoord :
              h+1+((9+3*b+i:Int)) = h+10+(3*b:Int)+(i:Int) := by
            omega
          simpa [hcoord] using hr

/-- The complete m=2,n=4 even q4 prefix, from source S1 to state E/head h. -/
theorem m2EvenSix_q4_prefix_data (a b : Nat) (h : Int)
    (ha : 0 < a) :
    ∃ Tq,
      run tm2 (44+12*a) (s1Config 3 6 2 a 0 b h) =
        some ⟨4,h,Tq⟩ ∧
      (∀ i : Nat,
        Tq (h-(i:Int)) = sideBit (m2EvenSixQ4LeftFacing a) i) ∧
      BB6Coverage.Agent8Q4Suffix.q4RightShape Tq h b ∧
      (∀ i : Nat,
        Tq (h+1+(i:Int)) = sideBit (q4RightFacing b) i) := by
  let T := (s1Config 3 6 2 a 0 b h).tape
  let N := 3*a+2
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := (frameAt T1 hN m2EvenSixQ4Inside m2EvenSixQ4BridgeEnd).tape
  have hface : s1LeftFacing 3 6 2 a 0 =
      d1pow a ++ m2EvenSixSourceLeftSuffix := by
    simp [s1LeftFacing,binDec_zero,m2EvenSixSourceLeftSuffix,
      List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 6 2 a 0 b h i
    rw [hface] at hcell
    by_cases hi3 : i < 3*a
    · have hside := sideBit_append_left (d1pow a)
        m2EvenSixSourceLeftSuffix i (by rw [d1pow_length]; omega)
      rw [hside] at hcell
      have hbit := sideBit_d1pow_true a i hi3
      exact (hcell.trans hbit)
    · have hiCases : i = 3*a ∨ i = 3*a+1 := by omega
      rcases hiCases with hi0 | hi1
      · subst i
        have hside := sideBit_d1pow_append a (3*a)
          m2EvenSixSourceLeftSuffix (by omega)
        rw [hside] at hcell
        simpa [m2EvenSixSourceLeftSuffix,markerWord,sideBit] using hcell
      · subst i
        have hside := sideBit_d1pow_append a (3*a+1)
          m2EvenSixSourceLeftSuffix (by omega)
        rw [hside] at hcell
        simpa [m2EvenSixSourceLeftSuffix,markerWord,sideBit] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 6 2 a 0 b h 0
    simpa [T,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hc
  have hSweep :
      run tm2 (3*N) ⟨3,h,T⟩ =
        some ⟨3,h-(N:Int),T1⟩ := by
    simpa [T1] using counted_left_sweep N T h hOn hright
  have hmatch := m2EvenSixQ4Bridge_input_match a b h
  have hBridge :
      run tm2 38 ⟨3,hN,T1⟩ =
        some ⟨4,hN+2,T2⟩ := by
    have hb := bridgeAt T1 hN m2EvenSixQ4Inside
      m2EvenSixQ4BridgeStart m2EvenSixQ4BridgeEnd 38 rfl
      m2EvenSixQ4Bridge_exact m2EvenSixQ4Bridge_heads hmatch
    have hframe :
        frameAt T1 hN m2EvenSixQ4Inside m2EvenSixQ4BridgeEnd =
          (⟨4,hN+2,T2⟩ : Config) := by
      apply config_ext
      · simp [frameAt_state,m2EvenSixQ4BridgeEnd]
      · simp [frameAt_head,m2EvenSixQ4BridgeEnd]
        omega
      · rfl
    rw [hframe] at hb
    exact hb
  have hlinear : linearRightOnes T2 (hN+2) (3*a) := by
    intro i hi
    let x : Int := hN+2+(i:Int)
    by_cases hi0 : i=0
    · subst i
      have hrel : x-hN = 2 := by dsimp [x]; omega
      have hin : m2EvenSixQ4Inside (x-hN) = true := by
        simp [m2EvenSixQ4Inside,hrel]
      have hframe := frameAt_tape_inside T1 hN
        m2EvenSixQ4Inside m2EvenSixQ4BridgeEnd x hin
      have hmark :
          decide (x-hN ∈ m2EvenSixQ4BridgeEnd.marked) = true := by
        rw [hrel]
        simp [m2EvenSixQ4BridgeEnd]
      simpa [T2,x] using hframe.trans hmark
    · have hrel : x-hN = 2+(i:Int) := by dsimp [x]; omega
      have hout : m2EvenSixQ4Inside (x-hN) = false := by
        simp [m2EvenSixQ4Inside,hrel]
        omega
      have hframe := frameAt_tape_outside T1 hN
        m2EvenSixQ4Inside m2EvenSixQ4BridgeEnd x hout
      have hcoord : x = h-((3*a-i : Nat) : Int) := by
        dsimp [x,hN,N]
        omega
      have hj : (3*a-i)+1 < N := by dsimp [N]; omega
      have hblock := sweptLeft_block N (3*a-i) T h hj
      have hactual : T2 x = true := by
        calc
          T2 x = T1 x := by simpa [T2] using hframe
          _ = true := by rw [hcoord]; exact hblock
      exact hactual
  have hheadScan : hN+2+(3*a:Int) = h := by
    dsimp [hN,N]
    omega
  have hScan :
      run tm2 (3*a) ⟨4,hN+2,T2⟩ =
        some ⟨4,h,T2⟩ := by
    simpa [hheadScan] using E_scan T2 (hN+2) (3*a) hlinear
  have h12 :
      run tm2 (3*N+38) ⟨3,h,T⟩ =
        some ⟨4,hN+2,T2⟩ := by
    rw [run_append,hSweep]
    simp only [Option.bind_some]
    exact hBridge
  have htotal :
      run tm2 (3*N+38+3*a) ⟨3,h,T⟩ =
        some ⟨4,h,T2⟩ := by
    rw [run_append,h12]
    simp only [Option.bind_some]
    exact hScan
  have hcost : 44+12*a = 3*N+38+3*a := by
    dsimp [N]
    omega
  have hprefix' :
      run tm2 (44+12*a) ⟨3,h,T⟩ =
        some ⟨4,h,m2EvenSixQ4CutTape a b h⟩ := by
    rw [← hcost] at htotal
    simpa [T,N,T1,hN,T2,m2EvenSixQ4CutTape] using htotal
  have hhead := m2EvenSixQ4CutTape_head a b h ha
  have hrightT := m2EvenSixQ4CutTape_rightFacing a b h ha
  have hleftT := m2EvenSixQ4CutTape_leftFacing a b h ha hhead
  have hshape := m2EvenSixQ4RightShape_of_stream
    (m2EvenSixQ4CutTape a b h) h b hhead hrightT
  refine ⟨m2EvenSixQ4CutTape a b h, ?_, hleftT, hshape, hrightT⟩
  simpa [T,s1Config,s0Config] using hprefix'

/-- The E scan after the 38-step bridge crosses exactly the remaining
3*a marked cells to the right of its starting point. -/
theorem m2EvenSixQ4CutTape_linearRightOnes
    (a b : Nat) (h : Int) (ha : 0 < a) :
    linearRightOnes (m2EvenSixQ4CutTape a b h)
      (h-(3*a:Int)) (3*a) := by
  have hhead := m2EvenSixQ4CutTape_head a b h ha
  have hleft := m2EvenSixQ4CutTape_leftFacing a b h ha hhead
  intro i hi
  let j := 3*a-i
  have hj1 : 1 ≤ j := by dsimp [j]; omega
  have hj2 : j ≤ 3*a := by dsimp [j]; omega
  have hbit : sideBit (m2EvenSixQ4LeftFacing a) j = true :=
    m2EvenSixQ4LeftFacingPrefixTrue a j (by omega)
  have hcell := hleft j
  have htrue : m2EvenSixQ4CutTape a b h (h-(j:Int)) = true := by
    rw [hbit] at hcell
    exact hcell
  have hcoord : h-(j:Int) = h-(3*a:Int)+(i:Int) := by
    dsimp [j]
    omega
  simpa [hcoord] using htrue

/-- The q4 suffix's target left stream is exactly the m=1,n=3 S1 word. -/
theorem m2EvenSixQ4SuffixTargetLeft (a b : Nat) :
    s1LeftFacing 3 5 1 (a+b+2) (2^b-1) =
      d0pow b ++ d1pow 2 ++ (m2EvenSixQ4LeftFacing a).drop 1 := by
  simpa [m2EvenSixQ4LeftFacing,m2EvenSixQ4LeftSuffix,
    BB6Coverage.Agent8Q4Suffix.q4LeftFacing,List.append_assoc] using
      q4SuffixTargetLeft 3 5 a b

/-- The generic q4 suffix plus this even prefix gives the exact
source-level Rst2 prefix to the canonical m=1,n=3 S1 intermediate. -/
theorem m2EvenSix_q4_reset_prefix_source
    (a b : Nat) (h : Int) (ha : 0 < a) :
    run tm2 (resetPrefixCost 2 6 a b)
      (s1Config 3 6 2 a 0 b h) =
      some (s1Config 3 5 1 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  obtain ⟨Tq,hprefix,hleft,hshape,hright⟩ :=
    m2EvenSix_q4_prefix_data a b h ha
  have htail : ∀ i : Nat, 9+3*b ≤ i →
      Tq (h+1+(i:Int)) = false := by
    intro i hi
    rw [hright i]
    apply sideBit_ge_length
    rw [q4RightFacing_length]
    omega
  have happend := m2EvenSixQ4SuffixTargetLeft a b
  have hsuffix := q4_suffix_run_to_s1Config Tq h b
    3 5 1 (a+b+2) (2^b-1) (m2EvenSixQ4LeftFacing a)
    hshape htail hleft happend
  have hsum :
      resetPrefixCost 2 6 a b = (44+12*a)+(39+3*b) := by
    have hv : v2 6 = 1 := by
      exact v2_of_odd_factorization 6 1 1 (by omega)
    simp [resetPrefixCost,hv]
    omega
  rw [hsum,run_add,hprefix]
  simp only [Option.bind_some]
  exact hsuffix

#print axioms m2EvenSixQ4Bridge_exact
#print axioms m2EvenSixQ4Bridge_input_match
#print axioms m2EvenSix_q4_prefix_data
#print axioms m2EvenSixQ4SuffixTargetLeft
#print axioms m2EvenSix_q4_reset_prefix_source

end BB6Coverage.Agent48M2EvenSixQ4
