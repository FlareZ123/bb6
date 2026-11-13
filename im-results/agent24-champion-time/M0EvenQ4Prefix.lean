import CountedReset
import ChampionRootBridge
import S1Encoder
import CountedQ4Prefix
import Q4Suffix
import M0EvenQ4Bridge
import Lean.Elab.Tactic.Omega

/-!
# Source-level m=0,n=2 even q4 reset prefix

After a 3a-cell counted left sweep, a fixed 39-step bridge and a
3(a-1)-cell E-scan reach q4 at the original head.  This is the next
source stage after the m=1,n=3 odd reset.
-/


namespace BB6Coverage.Agent24M0EvenQ4Prefix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24M0EvenQ4Bridge
open BB6ChampionArithmetic

/-- Explicit tape at the m=0,n=2 even q4 cut. -/
def m0EvenQ4CutTape (a b : Nat) (h : Int) : Int → Bool :=
  let T := (s1Config 3 2 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  (frameAt T1 (h-(N:Int)) m0EvenQ4Inside m0EvenQ4BridgeEnd).tape

/-- The fixed bridge frame agrees with the swept source tape outside
its local [-9,3] window. -/
private theorem m0EvenQ4CutTape_eq_swept
    (a b : Nat) (h x : Int)
    (hout : m0EvenQ4Inside (x-(h-((3*a : Nat) : Int))) = false) :
    m0EvenQ4CutTape a b h x =
      sweptLeft (3*a) (s1Config 3 2 0 a 0 b h).tape h x := by
  let T := (s1Config 3 2 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_outside T1 (h-(N:Int))
    m0EvenQ4Inside m0EvenQ4BridgeEnd x hout
  simpa [m0EvenQ4CutTape,T,N,T1] using hf

private theorem m0EvenQ4CutTape_eq_end_inside
    (a b : Nat) (h x : Int)
    (hin : m0EvenQ4Inside (x-(h-((3*a : Nat) : Int))) = true) :
    m0EvenQ4CutTape a b h x =
      decide ((x-(h-((3*a : Nat) : Int))) ∈ m0EvenQ4BridgeEnd.marked) := by
  let T := (s1Config 3 2 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_inside T1 (h-(N:Int))
    m0EvenQ4Inside m0EvenQ4BridgeEnd x hin
  simpa [m0EvenQ4CutTape,T,N,T1] using hf

private theorem m0EvenQ4CutTape_eq_source_right
    (a b : Nat) (h x : Int) (hx : h+2 ≤ x) :
    m0EvenQ4CutTape a b h x =
      (s1Config 3 2 0 a 0 b h).tape x := by
  let T := (s1Config 3 2 0 a 0 b h).tape
  have hout : m0EvenQ4Inside
      (x-(h-((3*a : Nat) : Int))) = false := by
    simp [m0EvenQ4Inside]
    omega
  have hcut := m0EvenQ4CutTape_eq_swept a b h x hout
  have hpres := sweptLeft_preserves_right (3*a) T h x (by omega)
  simpa [T] using hcut.trans hpres

/-- The q4 cut follows a 3a counted sweep, the fixed 39-step bridge,
and a 3(a-1)-cell E-scan. -/
theorem m0Even_q4_prefix_run (a b : Nat) (h : Int) (ha : 0 < a) :
    run tm2 (36+12*a)
      ⟨3,h,(s1Config 3 2 0 a 0 b h).tape⟩ =
      some ⟨4,h,m0EvenQ4CutTape a b h⟩ := by
  let T := (s1Config 3 2 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := (frameAt T1 hN m0EvenQ4Inside m0EvenQ4BridgeEnd).tape
  have hleftFacing :
      s1LeftFacing 3 2 0 a 0 =
        d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh := by
    simp [s1LeftFacing,binDec_zero,m0Even_binDec_three_two,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 2 0 a 0 b h i
    have hside : sideBit (s1LeftFacing 3 2 0 a 0) i = true := by
      rw [hleftFacing]
      let R : List Bool := markerWord 0 ++ (d0 ++ (d1 ++ (d0 ++ (d1 ++ lh))))
      simp only [List.append_assoc]
      change sideBit (d1pow a ++ R) i = true
      have hiLen : i < (d1pow a).length := by
        simpa [d1pow_length] using hi
      rw [sideBit_append_left (d1pow a) R i hiLen]
      exact sideBit_d1pow_true a i (by simpa [d1pow_length] using hi)
    simpa [T,hside] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 2 0 a 0 b h 0
    simpa [T,s1PhysicalRight_source,sideBit] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch := m0EvenQ4Bridge_input_match a b h ha
  have hBridge := bridgeAt T1 hN m0EvenQ4Inside
    m0EvenQ4BridgeStart m0EvenQ4BridgeEnd 39 rfl
    m0EvenQ4Bridge_exact m0EvenQ4Bridge_heads hmatch
  have hBridge' :
      run tm2 39 ⟨3,hN,T1⟩ = some ⟨4,hN+3,T2⟩ := by
    have hframeConfig :
        frameAt T1 hN m0EvenQ4Inside m0EvenQ4BridgeEnd =
          (⟨4,hN+3,T2⟩ : Config) := by
      apply config_ext
      · simp [frameAt_state,m0EvenQ4BridgeEnd]
      · simp [frameAt_head,m0EvenQ4BridgeEnd] <;> omega
      · rfl
    rw [hframeConfig] at hBridge
    exact hBridge
  have hlinear : linearRightOnes T2 (hN+3) (3*(a-1)) := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      have hin : m0EvenQ4Inside ((hN+3)-hN) = true := by
        simp [m0EvenQ4Inside]
      have hcut := m0EvenQ4CutTape_eq_end_inside a b h (hN+3) hin
      have hmark :
          decide (((hN+3)-hN) ∈ m0EvenQ4BridgeEnd.marked) = true := by
        simp [m0EvenQ4BridgeEnd]
      have htrue : m0EvenQ4CutTape a b h (hN+3) = true :=
        hcut.trans hmark
      simpa [m0EvenQ4CutTape,T,N,T1,hN,T2] using htrue
    · let x : Int := hN+3+(i:Int)
      have hout : m0EvenQ4Inside (x-hN) = false := by
        simp [m0EvenQ4Inside,x]
        omega
      have hframe : T2 x = T1 x := by
        simpa [T2] using
          frameAt_tape_outside T1 hN m0EvenQ4Inside m0EvenQ4BridgeEnd x hout
      let j : Nat := 3*a-3-i
      have hj : j+1 < N := by
        dsimp [j,N] at *
        omega
      have hblock := sweptLeft_block N j T h hj
      have hcoord : x = h-(j:Int) := by
        dsimp [x,j,N,hN]
        omega
      have hT1 : T1 x = true := by
        change sweptLeft N T h x = true
        rw [hcoord]
        exact hblock
      simpa [x,T2] using hframe.trans hT1
  have hScan := E_scan T2 (hN+3) (3*(a-1)) hlinear
  have hhead : hN+3+(3*(a-1):Int) = h := by
    dsimp [hN,N]
    omega
  have hscan :
      run tm2 (3*(a-1)) ⟨4,hN+3,T2⟩ = some ⟨4,h,T2⟩ := by
    simpa [hhead] using hScan
  have htotal : run tm2 (3*N+(39+3*(a-1))) ⟨3,h,T⟩ =
      some ⟨4,h,T2⟩ := by
    rw [run_append,hSweep]
    simp only [Option.bind_some]
    rw [run_append,hBridge']
    simp only [Option.bind_some]
    exact hscan
  have hnum : 36+12*a = 3*N+(39+3*(a-1)) := by
    dsimp [N]
    omega
  simpa [T,N,T1,hN,T2,m0EvenQ4CutTape,hnum] using htotal

private theorem sideBit_false_after_length_local (xs : List Bool) (i : Nat)
    (hi : xs.length ≤ i) : sideBit xs i = false := by
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons a xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by
            simp only [List.length_cons] at hi
            omega
          simpa [sideBit] using ih i hi'

/-- The q4 cut has the standard right guard, unary counter, and blank tail. -/
theorem m0Even_q4_prefix_rightShape (a b : Nat) (h : Int) (ha : 0 < a) :
    BB6Coverage.Agent8Q4Suffix.q4RightShape (m0EvenQ4CutTape a b h) h b := by
  unfold BB6Coverage.Agent8Q4Suffix.q4RightShape
  let T := (s1Config 3 2 0 a 0 b h).tape
  constructor
  · intro i hi
    have hiCases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hiCases with h0 | h1 | h2 | h3 | h4
    all_goals subst i
    · by_cases ha1 : a = 1
      · subst a
        have hin : m0EvenQ4Inside (h-(h-(3:Int))) = true := by
          simp [m0EvenQ4Inside]
        have hcut := m0EvenQ4CutTape_eq_end_inside 1 b h h hin
        have hmark :
            decide ((h-(h-(3:Int))) ∈ m0EvenQ4BridgeEnd.marked) = true := by
          have hc : h-(h-(3:Int)) = 3 := by omega
          rw [hc]
          simp [m0EvenQ4BridgeEnd]
        simpa using hcut.trans hmark
      · have hout : m0EvenQ4Inside
            (h-(h-((3*a : Nat) : Int))) = false := by
          simp [m0EvenQ4Inside]
          omega
        have hcut := m0EvenQ4CutTape_eq_swept a b h h hout
        have hhead : sweptLeft (3*a) T h h = true := by
          have hs := sweptLeft_head (3*a-2) T h
          have hN : 3*a = (3*a-2)+2 := by omega
          rw [← hN] at hs
          exact hs
        have hhead' : sweptLeft (3*a)
            (s1Config 3 2 0 a 0 b h).tape h h = true := by
          simpa [T] using hhead
        exact hcut.trans hhead'
    · have hout : m0EvenQ4Inside
          ((h+1)-(h-((3*a : Nat) : Int))) = false := by
        simp [m0EvenQ4Inside]
        omega
      have hcut := m0EvenQ4CutTape_eq_swept a b h (h+1) hout
      have hplus : sweptLeft (3*a) T h (h+1) = true := by
        simpa [T] using sweptLeft_plus1 (3*a-1) T h
      simpa [T] using hcut.trans hplus
    · have hcut := m0EvenQ4CutTape_eq_source_right a b h (h+2) (by omega)
      have hsrc : T (h+2) = true := by
        have hcoord : h+1+(1:Int) = h+2 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell 3 2 0 a 0 b h 1
      exact hcut.trans hsrc
    · have hcut := m0EvenQ4CutTape_eq_source_right a b h (h+3) (by omega)
      have hsrc : T (h+3) = true := by
        have hcoord : h+1+(2:Int) = h+3 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell 3 2 0 a 0 b h 2
      exact hcut.trans hsrc
    · have hcut := m0EvenQ4CutTape_eq_source_right a b h (h+4) (by omega)
      have hsrc : T (h+4) = true := by
        have hcoord : h+1+(3:Int) = h+4 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell 3 2 0 a 0 b h 3
      exact hcut.trans hsrc
  · constructor
    · have hcut := m0EvenQ4CutTape_eq_source_right a b h (h+5) (by omega)
      have hsrc : T (h+5) = false := by
        have hcoord : h+1+(4:Int) = h+5 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell 3 2 0 a 0 b h 4
      simpa [T] using hcut.trans hsrc
    · constructor
      · have hcut := m0EvenQ4CutTape_eq_source_right a b h (h+6) (by omega)
        have hsrc : T (h+6) = false := by
          have hcoord : h+1+(5:Int) = h+6 := by omega
          simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
            s1Config_right_cell 3 2 0 a 0 b h 5
        simpa [T] using hcut.trans hsrc
      · constructor
        · intro i hi
          have hcut := m0EvenQ4CutTape_eq_source_right a b h (h+7+(i:Int)) (by omega)
          have hsrc : T (h+7+(i:Int)) =
              sideBit (s0RightFacing b) (6+i) := by
            have hcoord : h+1+(6+i:Int) = h+7+(i:Int) := by omega
            simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
              s1Config_right_cell 3 2 0 a 0 b h (6+i)
          have hside :
              sideBit (s0RightFacing b) (6+i) =
                sideBit (d1pow (b+1)) i := by
            rw [s0RightFacing]
            simpa using sideBit_append_right
              [false,true,true,true,false,false] (d1pow (b+1))
              (6+i) (by simp)
          have hones : sideBit (d1pow (b+1)) i = true :=
            sideBit_d1pow_true (b+1) i (by omega)
          have htarget : T (h+7+(i:Int)) = true := by
            rw [hsrc,hside,hones]
          exact hcut.trans htarget
        · intro i hi
          have hcut := m0EvenQ4CutTape_eq_source_right a b h
            (h+10+(3*b:Int)+(i:Int)) (by omega)
          have hsrc : T (h+10+(3*b:Int)+(i:Int)) =
              sideBit (s0RightFacing b) (9+3*b+i) := by
            have hcoord : h+1+((9+3*b+i:Int)) =
                h+10+(3*b:Int)+(i:Int) := by omega
            simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
              s1Config_right_cell 3 2 0 a 0 b h (9+3*b+i)
          have hlen : (s0RightFacing b).length = 9+3*b := by
            simp [s0RightFacing,d1pow_length]
            omega
          have hblank : sideBit (s0RightFacing b) (9+3*b+i) = false :=
            sideBit_false_after_length_local (s0RightFacing b)
              (9+3*b+i) (by omega)
          have htarget : T (h+10+(3*b:Int)+(i:Int)) = false := by
            rw [hsrc,hblank]
          exact hcut.trans htarget

/-- Canonical left-facing stream at the m=0,n=2 even q4 cut. -/
def m0EvenQ4LeftFacing (a : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ binDec 3 1 ++ lh

private theorem sideBit_append_after_local (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) := by
  exact BB6Coverage.Agent6Q4Prefix.sideBit_append_right xs ys i hi

private theorem m0EvenQ4LeftFacingTail (a i : Nat)
    (hi : 3*a+10 ≤ i) :
    sideBit (s1LeftFacing 3 2 0 a 0) i =
      sideBit (m0EvenQ4LeftFacing a) i := by
  let common : List Bool := [true,true,true,true] ++ lh
  let srcPrefix : List Bool :=
    d1pow a ++ markerWord 0 ++ d0 ++ [true,true,true,false,false]
  let tgtPrefix : List Bool :=
    [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ [false,false,true,true,true]
  have hsrc :
      s1LeftFacing 3 2 0 a 0 = srcPrefix ++ common := by
    simp [srcPrefix,common,s1LeftFacing,binDec_zero,
      m0Even_binDec_three_two,d0,d1,List.append_assoc]
  have htgt :
      m0EvenQ4LeftFacing a = tgtPrefix ++ common := by
    simp [tgtPrefix,common,m0EvenQ4LeftFacing,
      m0Even_binDec_three_one,d0,d1,List.append_assoc]
  have hs := sideBit_append_after_local srcPrefix common i (by
    simp [srcPrefix,d1pow_length,markerWord,d0]
    omega)
  have ht := sideBit_append_after_local tgtPrefix common i (by
    simp [tgtPrefix,d1pow_length,markerWord,d0]
    omega)
  have hlenS : srcPrefix.length = 3*a+10 := by
    simp [srcPrefix,d1pow_length,markerWord,d0]
  have hlenT : tgtPrefix.length = 3*a+10 := by
    simp [tgtPrefix,d1pow_length,markerWord,d0]
  rw [hsrc,htgt,hs,ht,hlenS,hlenT]

private theorem m0EvenQ4LeftFacingPrefixTrue (a i : Nat)
    (hi : i < 3*a) :
    sideBit (m0EvenQ4LeftFacing a) i = true := by
  let P : List Bool := [true] ++ d1pow (a-1) ++ [true,true]
  let R : List Bool := [false,true] ++ d0 ++ binDec 3 1 ++ lh
  have hlist : m0EvenQ4LeftFacing a = P ++ R := by
    simp [P,R,m0EvenQ4LeftFacing,markerWord,List.append_assoc]
  have hP : sideBit P i = true := by
    by_cases hi0 : i = 0
    · subst i
      simp [P,sideBit]
    · have hpos : 1 ≤ i := by omega
      rw [show P = [true] ++ (d1pow (a-1) ++ [true,true]) by rfl]
      rw [sideBit_append_after_local [true]
        (d1pow (a-1) ++ [true,true]) i (by simp; omega)]
      let j := i-1
      by_cases hj : j < 3*(a-1)
      · have hlen : (d1pow (a-1)).length = 3*(a-1) := by
          simp [d1pow_length]
        rw [sideBit_append_left (d1pow (a-1)) [true,true] j (by
          simpa [hlen] using hj)]
        exact sideBit_d1pow_true (a-1) j (by omega)
      · have hlen : (d1pow (a-1)).length = 3*(a-1) := by
          simp [d1pow_length]
        rw [sideBit_append_after_local (d1pow (a-1)) [true,true] j (by
          rw [hlen]
          omega)]
        rw [hlen]
        have hjCases : j-3*(a-1) = 0 ∨ j-3*(a-1) = 1 := by omega
        rcases hjCases with hj0 | hj1
        · rw [hj0]
          simp [sideBit]
        · rw [hj1]
          simp [sideBit]
  have hlen : P.length = 3*a := by
    simp [P,d1pow_length]
    omega
  rw [hlist]
  rw [sideBit_append_left P R i (by simpa [hlen] using hi)]
  exact hP

private theorem m0EvenQ4LeftFacingBoundaryBit (a k : Nat)
    (hk1 : 1 ≤ k) (hk9 : k ≤ 9) :
    sideBit (m0EvenQ4LeftFacing a) (3*a+k) =
      decide (-(k:Int) ∈ m0EvenQ4BridgeEnd.marked) := by
  have hlist :
      m0EvenQ4LeftFacing a =
        ([true] ++ d1pow (a-1)) ++
          (markerWord 2 ++ d0 ++ binDec 3 1 ++ lh) := by
    simp [m0EvenQ4LeftFacing,List.append_assoc]
  rw [hlist]
  rw [sideBit_append_after_local ([true] ++ d1pow (a-1))
    (markerWord 2 ++ d0 ++ binDec 3 1 ++ lh)
    (3*a+k) (by simp [d1pow_length]; omega)]
  have hkCases : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨
      k=6 ∨ k=7 ∨ k=8 ∨ k=9 := by omega
  rcases hkCases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  all_goals subst k
  all_goals simp [m0EvenQ4BridgeEnd,markerWord,d0,d1,lh,sideBit]

private theorem m0EvenQ4CutTape_eq_source_left
    (a b : Nat) (h : Int) (i : Nat) (hi : 3*a+10 ≤ i) :
    m0EvenQ4CutTape a b h (h-(i:Int)) =
      sideBit (s1LeftFacing 3 2 0 a 0) i := by
  let T := (s1Config 3 2 0 a 0 b h).tape
  have hout : m0EvenQ4Inside
      ((h-(i:Int))-(h-((3*a : Nat) : Int))) = false := by
    simp [m0EvenQ4Inside]
    omega
  have hcut := m0EvenQ4CutTape_eq_swept a b h (h-(i:Int)) hout
  have hpres := sweptLeft_preserves_left (3*a) T h
    (h-(i:Int)) (by omega)
  have hcell := s1Config_left_cell 3 2 0 a 0 b h i
  simpa [T] using hcut.trans (hpres.trans hcell)

/-- The q4 cut's complete left-facing stream is the canonical next
marker-2 S1 left word. -/
theorem m0Even_q4_prefix_leftFacing (a b : Nat) (h : Int) (ha : 0 < a) :
    ∀ i : Nat, m0EvenQ4CutTape a b h (h-(i:Int)) =
      sideBit (m0EvenQ4LeftFacing a) i := by
  intro i
  by_cases hi0 : i=0
  · subst i
    have hshape := m0Even_q4_prefix_rightShape a b h ha
    have htrue : m0EvenQ4CutTape a b h h = true := by
      simpa using hshape.1 0 (by omega)
    simpa [m0EvenQ4LeftFacing,sideBit] using htrue
  · by_cases hsmall : i < 3*a-3
    · let x : Int := h-(i:Int)
      have hout : m0EvenQ4Inside
          (x-(h-((3*a : Nat):Int))) = false := by
        simp [m0EvenQ4Inside,x]
        omega
      have hcut := m0EvenQ4CutTape_eq_swept a b h x hout
      have hblock := sweptLeft_block (3*a) i
        (s1Config 3 2 0 a 0 b h).tape h (by omega)
      have hblock' :
          sweptLeft (3*a) (s1Config 3 2 0 a 0 b h).tape h x = true := by
        simpa [x] using hblock
      have hval : m0EvenQ4CutTape a b h x = true := hcut.trans hblock'
      have htarget := m0EvenQ4LeftFacingPrefixTrue a i (by omega)
      exact hval.trans htarget.symm
    · by_cases hnear : i = 3*a-3 ∨ i = 3*a-2 ∨ i = 3*a-1
      · rcases hnear with h3 | h2 | h1
        · subst i
          let x : Int := h-((3*a-3:Int))
          have hin : m0EvenQ4Inside (x-(h-((3*a:Nat):Int))) = true := by
            simp [m0EvenQ4Inside,x]
            omega
          have hcut := m0EvenQ4CutTape_eq_end_inside a b h x hin
          have hmark :
              decide ((x-(h-((3*a:Nat):Int))) ∈ m0EvenQ4BridgeEnd.marked) = true := by
            have hc : x-(h-((3*a:Nat):Int)) = 3 := by dsimp [x]; omega
            rw [hc]
            simp [m0EvenQ4BridgeEnd]
          have hval : m0EvenQ4CutTape a b h x = true := hcut.trans hmark
          have htarget := m0EvenQ4LeftFacingPrefixTrue a (3*a-3) (by omega)
          exact hval.trans htarget.symm
        · subst i
          let x : Int := h-((3*a-2:Int))
          have hin : m0EvenQ4Inside (x-(h-((3*a:Nat):Int))) = true := by
            simp [m0EvenQ4Inside,x]
            omega
          have hcut := m0EvenQ4CutTape_eq_end_inside a b h x hin
          have hmark :
              decide ((x-(h-((3*a:Nat):Int))) ∈ m0EvenQ4BridgeEnd.marked) = true := by
            have hc : x-(h-((3*a:Nat):Int)) = 2 := by dsimp [x]; omega
            rw [hc]
            simp [m0EvenQ4BridgeEnd]
          have hval : m0EvenQ4CutTape a b h x = true := hcut.trans hmark
          have htarget := m0EvenQ4LeftFacingPrefixTrue a (3*a-2) (by omega)
          exact hval.trans htarget.symm
        · subst i
          let x : Int := h-((3*a-1:Int))
          have hin : m0EvenQ4Inside (x-(h-((3*a:Nat):Int))) = true := by
            simp [m0EvenQ4Inside,x]
            omega
          have hcut := m0EvenQ4CutTape_eq_end_inside a b h x hin
          have hmark :
              decide ((x-(h-((3*a:Nat):Int))) ∈ m0EvenQ4BridgeEnd.marked) = true := by
            have hc : x-(h-((3*a:Nat):Int)) = 1 := by dsimp [x]; omega
            rw [hc]
            simp [m0EvenQ4BridgeEnd]
          have hval : m0EvenQ4CutTape a b h x = true := hcut.trans hmark
          have htarget := m0EvenQ4LeftFacingPrefixTrue a (3*a-1) (by omega)
          exact hval.trans htarget.symm
      · by_cases hieq : i = 3*a
        · subst i
          let x : Int := h-((3*a:Int))
          have hin : m0EvenQ4Inside (x-(h-((3*a:Nat):Int))) = true := by
            simp [m0EvenQ4Inside,x]
          have hcut := m0EvenQ4CutTape_eq_end_inside a b h x hin
          have hmark :
              decide ((x-(h-((3*a:Nat):Int))) ∈ m0EvenQ4BridgeEnd.marked) = false := by
            have hc : x-(h-((3*a:Nat):Int)) = 0 := by dsimp [x]; omega
            rw [hc]
            simp [m0EvenQ4BridgeEnd]
          have htarget :
              sideBit (m0EvenQ4LeftFacing a) (3*a) = false := by
            have hlist :
                m0EvenQ4LeftFacing a =
                  ([true] ++ d1pow (a-1)) ++
                    (markerWord 2 ++ d0 ++ binDec 3 1 ++ lh) := by
              simp [m0EvenQ4LeftFacing,List.append_assoc]
            rw [hlist]
            rw [sideBit_append_after_local ([true] ++ d1pow (a-1))
              (markerWord 2 ++ d0 ++ binDec 3 1 ++ lh) (3*a)
              (by simp [d1pow_length]; omega)]
            simp [markerWord,sideBit]
          have hval : m0EvenQ4CutTape a b h x = false := hcut.trans hmark
          exact hval.trans htarget.symm
        · by_cases hbound : i ≤ 3*a+9
          · let k : Nat := i-3*a
            have hk1 : 1 ≤ k := by dsimp [k]; omega
            have hk9 : k ≤ 9 := by dsimp [k]; omega
            let x : Int := h-(i:Int)
            have hrel : x-(h-((3*a:Nat):Int)) = -(k:Int) := by
              dsimp [x,k]
              omega
            have hin : m0EvenQ4Inside (-(k:Int)) = true := by
              simp [m0EvenQ4Inside]
              omega
            have hin' : m0EvenQ4Inside
                (x-(h-((3*a:Nat):Int))) = true := by
              rw [hrel]
              exact hin
            have hcut := m0EvenQ4CutTape_eq_end_inside a b h x hin'
            have hi : i=3*a+k := by dsimp [k]; omega
            have htarget := m0EvenQ4LeftFacingBoundaryBit a k hk1 hk9
            have htarget' :
                sideBit (m0EvenQ4LeftFacing a) i =
                  decide (-(k:Int) ∈ m0EvenQ4BridgeEnd.marked) := by
              rw [hi]
              exact htarget
            have hmark' : decide
                ((x-(h-((3*a:Nat):Int))) ∈ m0EvenQ4BridgeEnd.marked) =
                  decide (-(k:Int) ∈ m0EvenQ4BridgeEnd.marked) := by
              rw [hrel]
            have hval :
                m0EvenQ4CutTape a b h x =
                  sideBit (m0EvenQ4LeftFacing a) i := by
              calc
                m0EvenQ4CutTape a b h x =
                    decide ((x-(h-((3*a:Nat):Int)) ∈
                      m0EvenQ4BridgeEnd.marked) := hcut
                _ = decide (-(k:Int) ∈ m0EvenQ4BridgeEnd.marked) := hmark'
                _ = sideBit (m0EvenQ4LeftFacing a) i := htarget'.symm
            exact hval
          · have htail := m0EvenQ4CutTape_eq_source_left a b h i (by omega)
            have hbits := m0EvenQ4LeftFacingTail a i (by omega)
            exact htail.trans hbits

/-- The q4 suffix's d0-sweep reconstructs the next marker-2 left word. -/
theorem m0EvenQ4SuffixTargetLeft (a b : Nat) (ha : 0 < a) :
    s1LeftFacing 3 1 2 (a+b+1) (2^b-1) =
      d0pow b ++ d1pow 2 ++ (m0EvenQ4LeftFacing a).drop 1 := by
  unfold s1LeftFacing m0EvenQ4LeftFacing
  rw [binDec_pow2_sub_one]
  rw [d1pow_add_right 2 (a-1)]
  simp [List.drop,List.append_assoc]
  omega

theorem m0Even_resetPrefixCost_eq (a b : Nat) :
    resetPrefixCost 0 2 a b = 75+12*a+3*b := by
  have hv : BB6ChampionArithmetic.v2 2 = 1 := by
    simpa using v2_of_even 2 (by omega) (by decide)
  simp [resetPrefixCost,hv]
  omega

#print axioms m0Even_q4_prefix_run
#print axioms m0Even_q4_prefix_rightShape
#print axioms m0Even_q4_prefix_leftFacing
#print axioms m0EvenQ4SuffixTargetLeft
#print axioms m0Even_resetPrefixCost_eq

end BB6Coverage.Agent24M0EvenQ4Prefix
