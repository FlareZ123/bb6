import CountedReset
import CountedSweep
import ChampionRootBridge
import S1Encoder
import CountedQ4Prefix
import Q4Suffix
import M0EvenEightQ4Bridge
import Lean.Elab.Tactic.Omega

/-!
# Marker-0, n=8q q4 prefix

The prefix is a 3a-cell counted left sweep (9a TM2 moves), the exact
63-step finite bridge, and a 3(a-1)-cell E-scan. Its total cost is
60+12a and it ends in state 4 at the original head.
-/

namespace BB6Coverage.Agent48M0EvenEightQ4Prefix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent48M0EvenEightQ4Bridge

/-- Explicit tape at the marker-0, n=8q q4 cut. -/
def m0EvenEightQ4CutTape (L q a b : Nat) (h : Int) : Int → Bool :=
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  (frameAt T1 (h-(N:Int)) m0EvenEightInside m0EvenEightBridgeEnd).tape

private theorem m0EvenEightQ4CutTape_eq_swept
    (L q a b : Nat) (h x : Int)
    (hout : m0EvenEightInside
      (x-(h-((3*a : Nat) : Int))) = false) :
    m0EvenEightQ4CutTape L q a b h x =
      sweptLeft (3*a) (s1Config L (8*q) 0 a 0 b h).tape h x := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_outside T1 (h-(N:Int))
    m0EvenEightInside m0EvenEightBridgeEnd x hout
  simpa [m0EvenEightQ4CutTape,T,N,T1] using hf

private theorem m0EvenEightQ4CutTape_eq_end_inside
    (L q a b : Nat) (h x : Int)
    (hin : m0EvenEightInside
      (x-(h-((3*a : Nat) : Int))) = true) :
    m0EvenEightQ4CutTape L q a b h x =
      decide ((x-(h-((3*a : Nat) : Int))) ∈
        m0EvenEightBridgeEnd.marked) := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_inside T1 (h-(N:Int))
    m0EvenEightInside m0EvenEightBridgeEnd x hin
  simpa [m0EvenEightQ4CutTape,T,N,T1] using hf

private theorem m0EvenEightQ4CutTape_eq_source_right
    (L q a b : Nat) (h x : Int)
    (ha : 0 < a) (hx : h+2 ≤ x) :
    m0EvenEightQ4CutTape L q a b h x =
      (s1Config L (8*q) 0 a 0 b h).tape x := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  have hgt : 3 < x-(h-((3*a : Nat) : Int)) := by omega
  have hnot : ¬(-15 ≤ x-(h-((3*a : Nat) : Int)) ∧
      x-(h-((3*a : Nat) : Int)) ≤ 3) := by omega
  have hout : m0EvenEightInside
      (x-(h-((3*a : Nat) : Int))) = false := by
    change decide (-15 ≤ _ ∧ _ ≤ 3) = false
    exact decide_eq_false_iff_not.mpr hnot
  have hcut := m0EvenEightQ4CutTape_eq_swept L q a b h x hout
  have hpres := sweptLeft_preserves_right (3*a) T h x (by omega)
  simpa [T] using hcut.trans hpres

/-- The generalized q4 prefix for every odd quotient q. -/
theorem m0EvenEight_q4_prefix_run
    (L q a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hqodd : q % 2 = 1)
    (hbound : 8*q < 2^L) (ha : 0 < a) :
    run tm2 (60+12*a)
      ⟨3,h,(s1Config L (8*q) 0 a 0 b h).tape⟩ =
      some ⟨4,h,m0EvenEightQ4CutTape L q a b h⟩ := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := (frameAt T1 hN m0EvenEightInside m0EvenEightBridgeEnd).tape
  have hleftFacing :
      s1LeftFacing L (8*q) 0 a 0 =
        d1pow a ++ m0EvenEightSourceLeftSuffix L q := by
    exact m0EvenEightSourceLeftFacing L q a hL hqodd hbound
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell L (8*q) 0 a 0 b h i
    have hside : sideBit (s1LeftFacing L (8*q) 0 a 0) i = true := by
      rw [hleftFacing]
      have hiLen : i < (d1pow a).length := by
        simpa [d1pow_length] using hi
      rw [sideBit_append_left (d1pow a)
        (m0EvenEightSourceLeftSuffix L q) i hiLen]
      exact sideBit_d1pow_true a i
        (by simpa [d1pow_length] using hi)
    simpa [T,hside] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell L (8*q) 0 a 0 b h 0
    simpa [T,s1PhysicalRight_source,sideBit] using hc
  have hSweep :
      run tm2 (3*N) ⟨3,h,T⟩ =
        some ⟨3,hN,T1⟩ := by
    simpa [N,T,T1,hN] using counted_left_sweep N T h hOn hright
  have hmatch := m0EvenEightBridge_input_match
    L q a b h hL hqodd hbound ha
  have hBridge := bridgeAt T1 hN m0EvenEightInside
    m0EvenEightBridgeStart m0EvenEightBridgeEnd 63 rfl
    m0EvenEightBridge_exact m0EvenEightBridge_heads hmatch
  have hBridge' :
      run tm2 63 ⟨3,hN,T1⟩ =
        some ⟨4,hN+3,T2⟩ := by
    have hframeConfig :
        frameAt T1 hN m0EvenEightInside m0EvenEightBridgeEnd =
          (⟨4,hN+3,T2⟩ : Config) := by
      apply config_ext
      · simp [frameAt_state,m0EvenEightBridgeEnd]
      · simp [frameAt_head,m0EvenEightBridgeEnd] <;> omega
      · rfl
    rw [hframeConfig] at hBridge
    exact hBridge
  have hlinear : linearRightOnes T2 (hN+3) (3*(a-1)) := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      have hcoord : (hN+3)-(h-((3*a:Nat):Int)) = 3 := by
        dsimp [hN,N]
        omega
      have hin : m0EvenEightInside
          ((hN+3)-(h-((3*a:Nat):Int))) = true := by
        rw [hcoord]
        decide
      have hcut := m0EvenEightQ4CutTape_eq_end_inside
        L q a b h (hN+3) hin
      have hmark :
          decide (((hN+3)-(h-((3*a:Nat):Int))) ∈
            m0EvenEightBridgeEnd.marked) = true := by
        rw [hcoord]
        simp [m0EvenEightBridgeEnd]
      have htrue : m0EvenEightQ4CutTape L q a b h (hN+3) = true :=
        hcut.trans hmark
      simpa [m0EvenEightQ4CutTape,T,N,T1,hN,T2] using htrue
    · let x : Int := hN+3+(i:Int)
      have hgt : 3 < x-hN := by
        dsimp [x]
        omega
      have hout : m0EvenEightInside (x-hN) = false := by
        simp [m0EvenEightInside,hgt]
      have hframe : T2 x = T1 x := by
        simpa [T2] using
          frameAt_tape_outside T1 hN m0EvenEightInside
            m0EvenEightBridgeEnd x hout
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
  have hhead : hN+3+3*((a-1:Nat):Int) = h := by
    dsimp [hN,N]
    omega
  have hscan :
      run tm2 (3*(a-1)) ⟨4,hN+3,T2⟩ =
        some ⟨4,h,T2⟩ := by
    simpa [hhead] using hScan
  have htotal : run tm2 (3*N+(63+3*(a-1))) ⟨3,h,T⟩ =
      some ⟨4,h,T2⟩ := by
    rw [run_append,hSweep]
    simp only [Option.bind_some]
    rw [run_append,hBridge']
    simp only [Option.bind_some]
    exact hscan
  have hnum : 60+12*a = 3*N+(63+3*(a-1)) := by
    dsimp [N]
    omega
  simpa [m0EvenEightQ4CutTape,T,N,T1,T2,hN,hnum] using htotal


/-- Canonical left-facing stream at the marker-0, n=8q q4 cut. -/
def m0EvenEightQ4LeftFacing (L q a : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++
    d0 ++ d0 ++ d0 ++ d0 ++ d1 ++
    binDec (L-4) (q/2) ++ lh

/-- The q4 suffix's d0 sweep reconstructs marker 2 and n=8q-1. -/
theorem m0EvenEightQ4SuffixTargetLeft
    (L q a b : Nat) (hL : 4 ≤ L) (hqodd : q % 2 = 1)
    (hbound : 8*q < 2^L) (ha : 0 < a) :
    s1LeftFacing L (8*q-1) 2 (a+b+1) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m0EvenEightQ4LeftFacing L q a).drop 1 := by
  unfold s1LeftFacing m0EvenEightQ4LeftFacing
  have hbin : binDec (a+b+1) (2^b-1) =
      d0pow b ++ d1pow (a+1) := by
    have h := binDec_pow2_sub_one (a-1) b
    have hlen : (a-1)+b+2 = a+b+1 := by omega
    have hval : (a-1)+2 = a+1 := by omega
    simpa [hlen,hval] using h
  rw [hbin,m0EvenEight_binDec_residue7 L q hL hqodd hbound]
  have hadd : d1pow (a+1) = d1pow 2 ++ d1pow (a-1) := by
    have h := d1pow_add_right (a-1) 2
    have hval : (a-1)+2 = a+1 := by omega
    simpa [hval] using h
  rw [hadd]
  simp [List.drop,List.append_assoc]

#print axioms m0EvenEightQ4SuffixTargetLeft

#print axioms m0EvenEight_q4_prefix_run

end BB6Coverage.Agent48M0EvenEightQ4Prefix
