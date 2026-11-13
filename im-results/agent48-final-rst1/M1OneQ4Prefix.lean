import M1OddQ4Prefix
import Q4RightEndpoint
import Lean.Elab.Tactic.Omega

/-!
# Source-level final Rst1 (m,n)=(1,1) Q4 prefix

This is the missing arbitrary-(a,b) final reset prefix used by the conditional
TM63 champion witness.  It reuses Agent 24's 29-step finite Q4 bridge, but
embeds it in the source word s1Config L 1 1 a 0 b for arbitrary positive L.
The local bridge only reads relative offsets [-7,4]; the extra two source
cells to the left are deliberately left in the arbitrary exterior.

Intermediate until original-source Lean CI and an axiom audit succeed.
-/

namespace BB6Coverage.Agent48FinalRst1

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent24M1OddQ4Prefix
open BB6ChampionArithmetic

/-- The n=1 source prefix has the same 29-step local bridge, on the smaller
read window actually visited by the bridge. -/
def m1OneQ4Inside (x : Int) : Bool := decide (-7 ≤ x ∧ x ≤ 4)

theorem m1OneQ4Bridge_heads :
    (List.range 29).all (fun k =>
      match fRun tm2 k m1OddQ4BridgeStart with
      | none => true
      | some z => m1OneQ4Inside z.head = true) = true := by
  decide

private theorem m1One_sideBit_false_after_length
    (xs : List Bool) (i : Nat) (hi : xs.length ≤ i) :
    sideBit xs i = false := by
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

private theorem m1One_binDec_one (L : Nat) (hL : 0 < L) :
    binDec L 1 = d0 ++ d1pow (L-1) := by
  have hL' : L = (L-1)+1 := by omega
  rw [hL']
  rw [binDec_odd (L-1) 0 (by simp)]
  rw [binDec_zero]

private theorem m1One_d1pow_succ (L : Nat) (hL : 0 < L) :
    d1pow L = d1 ++ d1pow (L-1) := by
  have hL' : L = (L-1)+1 := by omega
  rw [hL']
  rfl

private theorem m1OneSourceLeftAt
    (L a b : Nat) (h : Int) (hL : 0 < L) (k : Nat) :
    (s1Config L 1 1 a 0 b h).tape
      (h - ((3*a+1+k : Nat) : Int)) =
      sideBit (markerWord 1 ++ d0 ++ d0 ++ d1pow (L-1) ++ lh) (1+k) := by
  have hleft :
      s1LeftFacing L 1 1 a 0 =
        d1pow a ++ markerWord 1 ++ d0 ++ d0 ++ d1pow (L-1) ++ lh := by
    simp [s1LeftFacing, binDec_zero, m1One_binDec_one L hL, List.append_assoc]
  have hcell := s1Config_left_cell L 1 1 a 0 b h (3*a+1+k)
  have hside := sideBit_d1pow_append a (3*a+1+k)
    (markerWord 1 ++ d0 ++ d0 ++ d1pow (L-1) ++ lh) (by omega)
  rw [hleft] at hcell
  simp only [List.append_assoc] at hcell hside
  rw [hside] at hcell
  simpa only [List.append_assoc,
    show 3*a+1+k-3*a = 1+k by omega] using hcell

private theorem m1OneSweptLeftCell
    (L a b : Nat) (h : Int) (hL : 0 < L) (k : Nat) :
    sweptLeft (3*a+1) (s1Config L 1 1 a 0 b h).tape h
      (h - ((3*a+1 : Nat) : Int) - (k : Int)) =
      sideBit (markerWord 1 ++ d0 ++ d0 ++ d1pow (L-1) ++ lh) (1+k) := by
  have hpres := sweptLeft_preserves_left (3*a+1)
    (s1Config L 1 1 a 0 b h).tape h
    (h - ((3*a+1 : Nat) : Int) - (k : Int)) (by omega)
  rw [hpres]
  have hsrc := m1OneSourceLeftAt L a b h hL k
  have hcoord :
      h - ((3*a+1 : Nat) : Int) - (k : Int) =
        h - ((3*a+1+k : Nat) : Int) := by omega
  rw [hcoord]
  exact hsrc

/-- After the counted 3a+1 left sweep, the n=1 source agrees with the
existing bridge on every cell that the 29-step bridge actually reads. -/
theorem m1OneQ4Bridge_input_match
    (L a b : Nat) (h : Int) (hL : 0 < L) :
    ∀ y, m1OneQ4Inside y = true →
      (sweptLeft (3*a+1) (s1Config L 1 1 a 0 b h).tape h)
        (h - ((3*a+1 : Nat) : Int) + y) =
          decide (y ∈ m1OddQ4BridgeStart.marked) := by
  intro y hy
  have hyb : -7 ≤ y ∧ y ≤ 4 := by
    simpa [m1OneQ4Inside] using hy
  by_cases hy0 : y ≤ 0
  · let k : Nat := Int.toNat (-y)
    have hkcast : (k : Int) = -y := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord :
        h - ((3*a+1 : Nat) : Int) + y =
          h - ((3*a+1 : Nat) : Int) - (k : Int) := by omega
    rw [hcoord]
    have hleft := m1OneSweptLeftCell L a b h hL k
    have hbits :
        sideBit (markerWord 1 ++ d0 ++ d0 ++ d1pow (L-1) ++ lh) (1+k) =
          decide (y ∈ m1OddQ4BridgeStart.marked) := by
      have hyCases : y = -7 ∨ y = -6 ∨ y = -5 ∨ y = -4 ∨
          y = -3 ∨ y = -2 ∨ y = -1 ∨ y = 0 := by omega
      rcases hyCases with h7 | h6 | h5 | h4 | h3 | h2 | h1 | h0
      all_goals subst y
      all_goals simp [k, m1OddQ4BridgeStart, markerWord, d0, d1, lh, sideBit]
    exact hleft.trans hbits
  · have hypos : 1 ≤ y := by omega
    have hyCases : y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 := by omega
    rcases hyCases with h1 | h2 | h3 | h4
    all_goals subst y
    · have hleft := sweptLeft_leftmost (3*a)
        (s1Config L 1 1 a 0 b h).tape h
      have hcoord :
          h - ((3*a+1 : Nat) : Int) + 1 =
            h - ((3*a : Nat) : Int) := by omega
      rw [hcoord]
      simpa [m1OddQ4BridgeStart] using hleft
    · by_cases ha : a = 0
      · subst a
        have hplus := sweptLeft_plus1 0
          (s1Config L 1 1 0 0 b h).tape h
        have hcoord : h - ((1 : Nat) : Int) + 2 = h+1 := by omega
        rw [hcoord]
        simpa [m1OddQ4BridgeStart] using hplus
      · have hblock := sweptLeft_block (3*a+1) (3*a+1-2)
          (s1Config L 1 1 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a+1 : Nat) : Int) + 2 =
              h - ((3*a+1-2 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m1OddQ4BridgeStart] using hblock
    · by_cases ha : a = 0
      · subst a
        have hpres := sweptLeft_preserves_right 1
          (s1Config L 1 1 0 0 b h).tape h (h+2) (by omega)
        have hsrc : (s1Config L 1 1 0 0 b h).tape (h+2) = true := by
          have hc := s1Config_right_cell L 1 1 0 0 b h 1
          have hcoord : h+1+1 = h+2 := by omega
          simpa [hcoord,s1PhysicalRight_source,sideBit] using hc
        have hcoord : h - ((1 : Nat) : Int) + 3 = h+2 := by omega
        rw [hcoord, hpres]
        simpa [m1OddQ4BridgeStart] using hsrc
      · have hblock := sweptLeft_block (3*a+1) (3*a+1-3)
          (s1Config L 1 1 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a+1 : Nat) : Int) + 3 =
              h - ((3*a+1-3 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m1OddQ4BridgeStart] using hblock
    · by_cases ha : a = 0
      · subst a
        have hpres := sweptLeft_preserves_right 1
          (s1Config L 1 1 0 0 b h).tape h (h+3) (by omega)
        have hsrc : (s1Config L 1 1 0 0 b h).tape (h+3) = true := by
          have hc := s1Config_right_cell L 1 1 0 0 b h 2
          have hcoord : h+1+2 = h+3 := by omega
          simpa [hcoord,s1PhysicalRight_source,sideBit] using hc
        have hcoord : h - ((1 : Nat) : Int) + 4 = h+3 := by omega
        rw [hcoord, hpres]
        simpa [m1OddQ4BridgeStart] using hsrc
      · have hblock := sweptLeft_block (3*a+1) (3*a+1-4)
          (s1Config L 1 1 a 0 b h).tape h (by omega)
        have hcoord :
            h - ((3*a+1 : Nat) : Int) + 4 =
              h - ((3*a+1-4 : Nat) : Int) := by omega
        rw [hcoord]
        simpa [m1OddQ4BridgeStart] using hblock

/-- Explicit tape at the final m=1,n=1 Q4 cut. -/
def m1OneQ4CutTape (L a b : Nat) (h : Int) : Int → Bool :=
  let T := (s1Config L 1 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  (frameAt T1 (h-(N:Int)) m1OneQ4Inside m1OddQ4BridgeEnd).tape

/-- Exact source run from S1(L,1,1,a,0,b) to the Q4 suffix head. -/
theorem m1One_q4_prefix_run
    (L a b : Nat) (h : Int) (hL : 0 < L) :
    run tm2 (32+12*a)
      ⟨3,h,(s1Config L 1 1 a 0 b h).tape⟩ =
      some ⟨4,h+4,m1OneQ4CutTape L a b h⟩ := by
  let T := (s1Config L 1 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := (frameAt T1 hN m1OneQ4Inside m1OddQ4BridgeEnd).tape
  have hleftFacing :
      s1LeftFacing L 1 1 a 0 =
        d1pow a ++ markerWord 1 ++ d0 ++ d0 ++ d1pow (L-1) ++ lh := by
    simp [s1LeftFacing, binDec_zero, m1One_binDec_one L hL, List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell L 1 1 a 0 b h i
    have hside : sideBit (s1LeftFacing L 1 1 a 0) i = true := by
      rw [hleftFacing]
      let R : List Bool := markerWord 1 ++
        (d0 ++ (d0 ++ (d1pow (L-1) ++ lh)))
      simp only [List.append_assoc]
      change sideBit (d1pow a ++ R) i = true
      by_cases hi3 : i < 3*a
      · have hiLen : i < (d1pow a).length := by
          simpa [d1pow_length] using hi3
        rw [sideBit_append_left (d1pow a) R i hiLen]
        exact sideBit_d1pow_true a i hi3
      · have hieq : i = 3*a := by omega
        subst i
        have hlen : (d1pow a).length = 3*a := by simp [d1pow_length]
        rw [sideBit_append_right (d1pow a) R (3*a) (by simpa [hlen])]
        simp [markerWord, d1pow_length]
    simpa [T,hside] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell L 1 1 a 0 b h 0
    simpa [T,s1PhysicalRight_source,sideBit] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch := m1OneQ4Bridge_input_match L a b h hL
  have hBridge := bridgeAt T1 hN m1OneQ4Inside
    m1OddQ4BridgeStart m1OddQ4BridgeEnd 29 rfl
    m1OddQ4Bridge_exact m1OneQ4Bridge_heads hmatch
  have hBridge' :
      run tm2 29 ⟨3,hN,T1⟩ = some ⟨4,hN+5,T2⟩ := by
    have hframeConfig :
        frameAt T1 hN m1OneQ4Inside m1OddQ4BridgeEnd =
          (⟨4,hN+5,T2⟩ : Config) := by
      apply config_ext
      · simp [frameAt_state,m1OddQ4BridgeEnd]
      · simp [frameAt_head,m1OddQ4BridgeEnd] <;> omega
      · rfl
    rw [hframeConfig] at hBridge
    exact hBridge
  have hlinear : linearRightOnes T2 (hN+5) (3*a) := by
    intro i hi
    let x : Int := hN+5+(i:Int)
    have hout : m1OneQ4Inside (x-hN) = false := by
      simp [m1OneQ4Inside,x]
      omega
    have hframe : T2 x = T1 x := by
      simpa [T2] using
        frameAt_tape_outside T1 hN m1OneQ4Inside
          m1OddQ4BridgeEnd x hout
    have hT1 : T1 x = true := by
      by_cases hx : x ≤ h
      · let j : Nat := 3*a-4-i
        have hj : j+1 < N := by
          dsimp [j,N,x,hN] at *
          omega
        have hblock := sweptLeft_block N j T h hj
        have hcoord : x = h-(j:Int) := by
          dsimp [x,j,N,hN]
          omega
        change sweptLeft N T h x = true
        rw [hcoord]
        exact hblock
      · by_cases hx1 : x = h+1
        · rw [hx1]
          simpa [T1,N] using sweptLeft_plus1 (3*a) T h
        · have hx2 : h+2 ≤ x := by omega
          have hx23 : x = h+2 ∨ x = h+3 := by
            dsimp [x,N,hN] at *
            omega
          have hpres := sweptLeft_preserves_right N T h x (by omega)
          rcases hx23 with hx2' | hx3'
          · rw [hx2'] at hpres ⊢
            change sweptLeft N T h (h+2) = true
            have hsrc : T (h+2) = true := by
              have hcoord : h+1+1 = h+2 := by omega
              simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
                s1Config_right_cell L 1 1 a 0 b h 1
            rw [hpres,hsrc]
          · rw [hx3'] at hpres ⊢
            change sweptLeft N T h (h+3) = true
            have hsrc : T (h+3) = true := by
              have hcoord : h+1+2 = h+3 := by omega
              simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
                s1Config_right_cell L 1 1 a 0 b h 2
            rw [hpres,hsrc]
    simpa [x,T2] using hframe.trans hT1
  have hScan := E_scan T2 (hN+5) (3*a) hlinear
  have hhead : hN+5+(3*a:Int) = h+4 := by
    dsimp [hN,N]
    omega
  have hscan :
      run tm2 (3*a) ⟨4,hN+5,T2⟩ = some ⟨4,h+4,T2⟩ := by
    simpa [hhead] using hScan
  have htotal : run tm2 (3*N+(29+3*a)) ⟨3,h,T⟩ =
      some ⟨4,h+4,T2⟩ := by
    rw [run_append,hSweep]
    simp only [Option.bind_some]
    rw [run_append,hBridge']
    simp only [Option.bind_some]
    exact hscan
  have hnum : 32+12*a = 3*N+(29+3*a) := by
    dsimp [N]
    omega
  simpa [T,N,T1,hN,T2,m1OneQ4CutTape,hnum] using htotal

private theorem m1OneQ4CutTape_eq_swept
    (L a b : Nat) (h x : Int)
    (hout : m1OneQ4Inside (x-(h-((3*a+1 : Nat) : Int))) = false) :
    m1OneQ4CutTape L a b h x =
      sweptLeft (3*a+1) (s1Config L 1 1 a 0 b h).tape h x := by
  let T := (s1Config L 1 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_outside T1 (h-(N:Int))
    m1OneQ4Inside m1OddQ4BridgeEnd x hout
  simpa [m1OneQ4CutTape,T,N,T1] using hf

private theorem m1OneQ4CutTape_eq_end_inside
    (L a b : Nat) (h x : Int)
    (hin : m1OneQ4Inside (x-(h-((3*a+1 : Nat) : Int))) = true) :
    m1OneQ4CutTape L a b h x =
      decide ((x-(h-((3*a+1 : Nat) : Int))) ∈ m1OddQ4BridgeEnd.marked) := by
  let T := (s1Config L 1 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_inside T1 (h-(N:Int))
    m1OneQ4Inside m1OddQ4BridgeEnd x hin
  simpa [m1OneQ4CutTape,T,N,T1] using hf

private theorem m1OneQ4CutTape_eq_source_right
    (L a b : Nat) (h x : Int) (hx : h+5 ≤ x) :
    m1OneQ4CutTape L a b h x =
      (s1Config L 1 1 a 0 b h).tape x := by
  let T := (s1Config L 1 1 a 0 b h).tape
  have hout : m1OneQ4Inside
      (x-(h-((3*a+1 : Nat) : Int))) = false := by
    simp [m1OneQ4Inside]
    omega
  have hcut := m1OneQ4CutTape_eq_swept L a b h x hout
  have hpres := sweptLeft_preserves_right (3*a+1) T h x (by omega)
  simpa [T] using hcut.trans hpres

private theorem m1OneQ4CutTape_eq_source_left
    (L a b : Nat) (h : Int) (i : Nat) (hL : 0 < L)
    (hi : 3*a+9 ≤ i) :
    m1OneQ4CutTape L a b h (h-(i:Int)) =
      (s1Config L 1 1 a 0 b h).tape (h-(i:Int)) := by
  let T := (s1Config L 1 1 a 0 b h).tape
  have hout : m1OneQ4Inside
      ((h-(i:Int))-(h-((3*a+1 : Nat) : Int))) = false := by
    simp [m1OneQ4Inside]
    omega
  have hcut := m1OneQ4CutTape_eq_swept L a b h (h-(i:Int)) hout
  have hpres := sweptLeft_preserves_left (3*a+1) T h
    (h-(i:Int)) (by omega)
  simpa [T] using hcut.trans hpres

/-- The Q4 right-hand shape is inherited from the same source right stream
as the (1,3) branch; the smaller frame changes only the far-left exterior. -/
theorem m1One_q4_prefix_rightShape
    (L a b : Nat) (h : Int) :
    q4RightShape (m1OneQ4CutTape L a b h) h b := by
  unfold q4RightShape
  let T := (s1Config L 1 1 a 0 b h).tape
  constructor
  · intro i hi
    have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hiCases with h0 | h1 | h2 | h3 | h4
    all_goals subst i
    · by_cases ha0 : a = 0
      · subst a
        have hrel : h - (h-(1:Int)) = 1 := by omega
        have hin : m1OneQ4Inside ((h+0)-(h-(1:Int))) = true := by
          simp [m1OneQ4Inside,hrel]
        have hcut := m1OneQ4CutTape_eq_end_inside L 0 b h (h+0) hin
        have hmark :
            decide (((h+0)-(h-(1:Int))) ∈ m1OddQ4BridgeEnd.marked) = true := by
          have hcoord : (h+0)-(h-(1:Int)) = 1 := by omega
          rw [hcoord]
          simp [m1OddQ4BridgeEnd]
        exact hcut.trans hmark
      · by_cases ha1 : a = 1
        · subst a
          have hrel : h - (h-(4:Int)) = 4 := by omega
          have hin : m1OneQ4Inside ((h+0)-(h-(4:Int))) = true := by
            simp [m1OneQ4Inside,hrel]
          have hcut := m1OneQ4CutTape_eq_end_inside L 1 b h (h+0) hin
          have hmark :
              decide (((h+0)-(h-(4:Int))) ∈ m1OddQ4BridgeEnd.marked) = true := by
            have hcoord : (h+0)-(h-(4:Int)) = 4 := by omega
            rw [hcoord]
            simp [m1OddQ4BridgeEnd]
          exact hcut.trans hmark
        · have hout : m1OneQ4Inside
              ((h+0)-(h-((3*a+1 : Nat) : Int))) = false := by
            simp [m1OneQ4Inside]
            omega
          have hcut := m1OneQ4CutTape_eq_swept L a b h (h+0) hout
          have hhead : sweptLeft (3*a+1) T h h = true := by
            have hs := sweptLeft_head (3*a+1-2) T h
            have hN : 3*a+1 = (3*a+1-2)+2 := by omega
            rw [← hN] at hs
            exact hs
          have hhead' : sweptLeft (3*a+1)
              (s1Config L 1 1 a 0 b h).tape h (h+0) = true := by
            simpa [T] using hhead
          exact hcut.trans hhead'
    · by_cases ha0 : a = 0
      · subst a
        have hrel : (h+1) - (h-(1:Int)) = 2 := by omega
        have hin : m1OneQ4Inside ((h+1)-(h-(1:Int))) = true := by
          simp [m1OneQ4Inside,hrel]
        have hcut := m1OneQ4CutTape_eq_end_inside L 0 b h (h+1) hin
        have hmark :
            decide (((h+1)-(h-(1:Int))) ∈ m1OddQ4BridgeEnd.marked) = true := by
          simp [hrel,m1OddQ4BridgeEnd]
        simpa [hrel] using hcut.trans hmark
      · have hout : m1OneQ4Inside
            ((h+1)-(h-((3*a+1 : Nat) : Int))) = false := by
          simp [m1OneQ4Inside]
          omega
        have hcut := m1OneQ4CutTape_eq_swept L a b h (h+1) hout
        have hplus : sweptLeft (3*a+1) T h (h+1) = true := by
          simpa [T] using sweptLeft_plus1 (3*a) T h
        simpa [T] using hcut.trans hplus
    · by_cases ha0 : a = 0
      · subst a
        have hrel : (h+2) - (h-(1:Int)) = 3 := by omega
        have hin : m1OneQ4Inside ((h+2)-(h-(1:Int))) = true := by
          simp [m1OneQ4Inside,hrel]
        have hcut := m1OneQ4CutTape_eq_end_inside L 0 b h (h+2) hin
        have hmark :
            decide (((h+2)-(h-(1:Int))) ∈ m1OddQ4BridgeEnd.marked) = true := by
          simp [hrel,m1OddQ4BridgeEnd]
        simpa [hrel] using hcut.trans hmark
      · have hout : m1OneQ4Inside
            ((h+2)-(h-((3*a+1 : Nat) : Int))) = false := by
          simp [m1OneQ4Inside]
          omega
        have hcut := m1OneQ4CutTape_eq_swept L a b h (h+2) hout
        have hpres := sweptLeft_preserves_right (3*a+1) T h (h+2) (by omega)
        have hsrc : T (h+2) = true := by
          have hcoord : h+1+1 = h+2 := by omega
          simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
            s1Config_right_cell L 1 1 a 0 b h 1
        exact hcut.trans (hpres.trans hsrc)
    · by_cases ha0 : a = 0
      · subst a
        have hrel : (h+3) - (h-(1:Int)) = 4 := by omega
        have hin : m1OneQ4Inside ((h+3)-(h-(1:Int))) = true := by
          simp [m1OneQ4Inside,hrel]
        have hcut := m1OneQ4CutTape_eq_end_inside L 0 b h (h+3) hin
        have hmark :
            decide (((h+3)-(h-(1:Int))) ∈ m1OddQ4BridgeEnd.marked) = true := by
          simp [hrel,m1OddQ4BridgeEnd]
        simpa [hrel] using hcut.trans hmark
      · have hout : m1OneQ4Inside
            ((h+3)-(h-((3*a+1 : Nat) : Int))) = false := by
          simp [m1OneQ4Inside]
          omega
        have hcut := m1OneQ4CutTape_eq_swept L a b h (h+3) hout
        have hpres := sweptLeft_preserves_right (3*a+1) T h (h+3) (by omega)
        have hsrc : T (h+3) = true := by
          have hcoord : h+1+2 = h+3 := by omega
          simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
            s1Config_right_cell L 1 1 a 0 b h 2
        exact hcut.trans (hpres.trans hsrc)
    · have hout : m1OneQ4Inside
          ((h+4)-(h-((3*a+1 : Nat) : Int))) = false := by
        simp [m1OneQ4Inside]
        omega
      have hcut := m1OneQ4CutTape_eq_swept L a b h (h+4) hout
      have hpres := sweptLeft_preserves_right (3*a+1) T h (h+4) (by omega)
      have hsrc : T (h+4) = true := by
        have hcoord : h+1+3 = h+4 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell L 1 1 a 0 b h 3
      exact hcut.trans (hpres.trans hsrc)
  · constructor
    · have hcut := m1OneQ4CutTape_eq_source_right L a b h (h+5) (by omega)
      have hsrc : T (h+5) = false := by
        have hcoord : h+1+4 = h+5 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell L 1 1 a 0 b h 4
      simpa [T] using hcut.trans hsrc
    · constructor
      · have hcut := m1OneQ4CutTape_eq_source_right L a b h (h+6) (by omega)
        have hsrc : T (h+6) = false := by
          have hcoord : h+1+5 = h+6 := by omega
          simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
            s1Config_right_cell L 1 1 a 0 b h 5
        simpa [T] using hcut.trans hsrc
      · constructor
        · intro i hi
          have hcut := m1OneQ4CutTape_eq_source_right L a b h (h+7+(i:Int)) (by omega)
          have hsrc : T (h+7+(i:Int)) =
              sideBit (s0RightFacing b) (6+i) := by
            have hcoord : h+1+(6+i:Int) = h+7+(i:Int) := by omega
            simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
              s1Config_right_cell L 1 1 a 0 b h (6+i)
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
          have hcut := m1OneQ4CutTape_eq_source_right L a b h
            (h+10+(3*b:Int)+(i:Int)) (by omega)
          have hsrc : T (h+10+(3*b:Int)+(i:Int)) =
              sideBit (s0RightFacing b) (9+3*b+i) := by
            have hcoord : h+1+((9+3*b+i:Int)) =
                h+10+(3*b:Int)+(i:Int) := by omega
            simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
              s1Config_right_cell L 1 1 a 0 b h (9+3*b+i)
          have hlen : (s0RightFacing b).length = 9+3*b := by
            simp [s0RightFacing,d1pow_length]
            omega
          have hblank : sideBit (s0RightFacing b) (9+3*b+i) = false :=
            m1One_sideBit_false_after_length (s0RightFacing b)
              (9+3*b+i) (by omega)
          have htarget : T (h+10+(3*b:Int)+(i:Int)) = false := by
            rw [hsrc,hblank]
          exact hcut.trans htarget

theorem m1One_q4_prefix_far_tail
    (L a b : Nat) (h : Int) :
    ∀ i : Nat, 9+3*b ≤ i →
      m1OneQ4CutTape L a b h (h+1+(i:Int)) = false := by
  intro i hi
  have hcut := m1OneQ4CutTape_eq_source_right L a b h
    (h+1+(i:Int)) (by omega)
  have hsrc :
      (s1Config L 1 1 a 0 b h).tape (h+1+(i:Int)) =
        sideBit (s0RightFacing b) i := by
    simpa [s1PhysicalRight_source,sideBit] using
      s1Config_right_cell L 1 1 a 0 b h i
  have hlen : (s0RightFacing b).length = 9+3*b := by
    simp [s0RightFacing,d1pow_length]
    omega
  have hblank : sideBit (s0RightFacing b) i = false :=
    m1One_sideBit_false_after_length (s0RightFacing b) i (by omega)
  calc
    m1OneQ4CutTape L a b h (h+1+(i:Int)) =
        (s1Config L 1 1 a 0 b h).tape (h+1+(i:Int)) := hcut
    _ = sideBit (s0RightFacing b) i := hsrc
    _ = false := hblank

/-- The left-facing source at the Q4 cut, expressed at the original head h. -/
def m1OneQ4LeftFacing (L a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ d1pow L ++ lh

private theorem m1OneQ4LeftFacingTail
    (L a i : Nat) (hL : 0 < L) (hi : 3*a+9 ≤ i) :
    sideBit (s1LeftFacing L 1 1 a 0) i =
      sideBit (m1OneQ4LeftFacing L a) i := by
  let R := d1pow (L-1) ++ lh
  let P := d1pow a ++ markerWord 1 ++ d0 ++ d0
  let Q := [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ d1
  have hsrc :
      s1LeftFacing L 1 1 a 0 = P ++ R := by
    simp [P,R,s1LeftFacing,binDec_zero,m1One_binDec_one L hL,List.append_assoc]
  have htgt :
      m1OneQ4LeftFacing L a = Q ++ R := by
    rw [m1One_d1pow_succ L hL]
    simp [Q,R,m1OneQ4LeftFacing,List.append_assoc]
  have hlenP : P.length = 3*a+9 := by
    simp [P,d1pow_length,markerWord,d0]
  have hlenQ : Q.length = 3*a+9 := by
    simp [Q,d1pow_length,markerWord,d0,d1]
  rw [hsrc,htgt]
  rw [sideBit_append_right P R i (by rw [hlenP]; omega)]
  rw [sideBit_append_right Q R i (by rw [hlenQ]; omega)]
  rw [hlenP,hlenQ]

private theorem m1OneQ4LeftFacingBridgeBit
    (L a k : Nat) (hL : 0 < L) (hk : 1 ≤ k ∧ k ≤ 7) :
    sideBit (m1OneQ4LeftFacing L a) (3*a+1+k) =
      decide ((-(k:Int)) ∈ m1OddQ4BridgeEnd.marked) := by
  have hleft :
      m1OneQ4LeftFacing L a =
        ([true] ++ d1pow a) ++
          (markerWord 0 ++ d0 ++ d1pow L ++ lh) := by
    simp [m1OneQ4LeftFacing,List.append_assoc]
  have hlen : ([true] ++ d1pow a).length = 3*a+1 := by
    simp [d1pow_length]
  rw [hleft]
  rw [sideBit_append_right ([true] ++ d1pow a)
    (markerWord 0 ++ d0 ++ d1pow L ++ lh) (3*a+1+k) (by rw [hlen]; omega)]
  have h0 := sideBit_d1pow_true L 0 (by omega)
  have h1 := sideBit_d1pow_true L 1 (by omega)
  have h2 := sideBit_d1pow_true L 2 (by omega)
  have ht0 : sideBit (d1pow L ++ lh) 0 = true := by
    rw [sideBit_append_left (d1pow L) lh 0 (by simp [d1pow_length]; omega)]
    exact h0
  have ht1 : sideBit (d1pow L ++ lh) 1 = true := by
    rw [sideBit_append_left (d1pow L) lh 1 (by simp [d1pow_length]; omega)]
    exact h1
  have ht2 : sideBit (d1pow L ++ lh) 2 = true := by
    rw [sideBit_append_left (d1pow L) lh 2 (by simp [d1pow_length]; omega)]
    exact h2
  have hkCases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
      k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hkCases with h1k | h2k | h3k | h4k | h5k | h6k | h7k
  all_goals subst k
  all_goals
    simp [markerWord,d0,sideBit,m1OddQ4BridgeEnd,ht0,ht1,ht2]

/-- Exact left-facing tape identity at the Q4 cut. -/
theorem m1One_q4_prefix_leftFacing
    (L a b : Nat) (h : Int) (hL : 0 < L) :
    ∀ i : Nat,
      m1OneQ4CutTape L a b h (h-(i:Int)) =
        sideBit (m1OneQ4LeftFacing L a) i := by
  intro i
  let N := 3*a+1
  let r : Int := (N:Int)-(i:Int)
  by_cases hi : i ≤ 3*a
  · have htarget : sideBit (m1OneQ4LeftFacing L a) i = true := by
      have hprefix :
          sideBit ([true] ++ d1pow a) i = true := by
        cases i with
        | zero => simp [sideBit]
        | succ j =>
            have hj : j < 3*a := by omega
            simpa [sideBit] using sideBit_d1pow_true a j hj
      have hleft :
          m1OneQ4LeftFacing L a =
            ([true] ++ d1pow a) ++
              (markerWord 0 ++ d0 ++ d1pow L ++ lh) := by
        simp [m1OneQ4LeftFacing,List.append_assoc]
      rw [hleft]
      rw [sideBit_append_left ([true] ++ d1pow a)
        (markerWord 0 ++ d0 ++ d1pow L ++ lh) i
        (by simp [d1pow_length]; omega)]
      exact hprefix
    by_cases hin : m1OneQ4Inside r = true
    · have hcut := m1OneQ4CutTape_eq_end_inside L a b h (h-(i:Int)) (by
        simpa [r,N] using hin)
      have hr : 1 ≤ r ∧ r ≤ 4 := by
        simpa [r,N,m1OneQ4Inside] using hin
      have hmark : decide (r ∈ m1OddQ4BridgeEnd.marked) = true := by
        have hcases : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
        rcases hcases with h1r | h2r | h3r | h4r
        all_goals subst r <;> simp [m1OddQ4BridgeEnd]
      exact (hcut.trans hmark).trans htarget.symm
    · have hcut := m1OneQ4CutTape_eq_swept L a b h (h-(i:Int)) (by
        simpa [r,N] using hin)
      have hblock : sweptLeft (3*a+1)
          (s1Config L 1 1 a 0 b h).tape h (h-(i:Int)) = true := by
        have hidx : i < 3*a+1 := by omega
        have hb := sweptLeft_block (3*a+1) i
          (s1Config L 1 1 a 0 b h).tape h hidx
        simpa using hb
      exact (hcut.trans hblock).trans htarget.symm
  · by_cases hieq : i = 3*a+1
    · have hcut := m1OneQ4CutTape_eq_end_inside L a b h (h-(i:Int)) (by
        simp [r,N,m1OneQ4Inside,hieq])
      have hmark : decide ((0:Int) ∈ m1OddQ4BridgeEnd.marked) = false := by
        simp [m1OddQ4BridgeEnd]
      have htarget : sideBit (m1OneQ4LeftFacing L a) i = false := by
        subst i
        have hleft :
            m1OneQ4LeftFacing L a =
              ([true] ++ d1pow a) ++
                (markerWord 0 ++ d0 ++ d1pow L ++ lh) := by
          simp [m1OneQ4LeftFacing,List.append_assoc]
        have hlen : ([true] ++ d1pow a).length = 3*a+1 := by
          simp [d1pow_length]
        rw [hleft]
        rw [sideBit_append_right ([true] ++ d1pow a)
          (markerWord 0 ++ d0 ++ d1pow L ++ lh) (3*a+1) (by rw [hlen])]
        simp [markerWord,sideBit]
      simpa [r,N,hieq] using (hcut.trans hmark).trans htarget.symm
    · have hsmall : i ≤ 3*a+8 := by omega
      let k : Nat := i-(3*a+1)
      have hk : 1 ≤ k ∧ k ≤ 7 := by dsimp [k]; omega
      have hcut := m1OneQ4CutTape_eq_end_inside L a b h (h-(i:Int)) (by
        have hr : r = -(k:Int) := by dsimp [r,N,k]; omega
        simp [m1OneQ4Inside,hr,hk])
      have hr : r = -(k:Int) := by dsimp [r,N,k]; omega
      have hmark : decide (r ∈ m1OddQ4BridgeEnd.marked) =
          sideBit (m1OneQ4LeftFacing L a) i := by
        rw [hr]
        have hb := m1OneQ4LeftFacingBridgeBit L a k hL hk
        have hidx : i = 3*a+1+k := by dsimp [k]; omega
        rw [hidx]
        exact hb.symm
      exact hcut.trans hmark
  · have htail : 3*a+9 ≤ i := by omega
    have hcut := m1OneQ4CutTape_eq_source_left L a b h i hL htail
    have hcell := s1Config_left_cell L 1 1 a 0 b h i
    rw [m1OneQ4LeftFacingTail L a i hL htail] at hcell
    exact hcut.trans hcell

/-- The Q4 suffix transforms the source-left stream into the canonical
marker-zero S1 target for the final n=1 reset. -/
theorem m1OneQ4SuffixTargetLeft
    (L a b : Nat) :
    s1LeftFacing L 0 0 (a+b+2) (2^b-1) =
      d0pow b ++ d1pow 2 ++ (m1OneQ4LeftFacing L a).drop 1 := by
  unfold s1LeftFacing m1OneQ4LeftFacing
  rw [binDec_pow2_sub_one]
  rw [binDec_zero]
  rw [d1pow_add_right a 2]
  simp [List.drop,List.append_assoc]

/-- Exact source-level final Rst1 prefix for arbitrary positive L,a,b.
This is the final machine-specific premise needed by the conditional TM63
champion-score theorem. -/
theorem m1One_q4_reset_prefix_source
    (L a b : Nat) (h : Int) (hL : 0 < L) :
    run tm2 (resetPrefixCost 1 1 a b)
      (s1Config L 1 1 a 0 b h) =
      some (s1Config L 0 0 (a+b+2) (2^b-1) 0 (h+5+3*b)) := by
  let T := m1OneQ4CutTape L a b h
  have hprefix := m1One_q4_prefix_run L a b h hL
  have hshape := m1One_q4_prefix_rightShape L a b h
  have htail := m1One_q4_prefix_far_tail L a b h
  have hleft := m1One_q4_prefix_leftFacing L a b h hL
  have happend := m1OneQ4SuffixTargetLeft L a b
  have hq4 := q4_suffix_run_to_s1Config T h b L 0 0
    (a+b+2) (2^b-1) (m1OneQ4LeftFacing L a)
    hshape htail hleft happend
  have hlinear : linearRightOnes T h 4 := by
    intro i hi
    exact hshape.1 i (by omega)
  have hfirst := E_scan T h 4 hlinear
  have hsplit : 39+3*b = 4+(35+3*b) := by omega
  have hq4split :
      run tm2 (4+(35+3*b)) ⟨4,h,T⟩ =
        some (s1Config L 0 0 (a+b+2) (2^b-1) 0
          (h+5+3*b)) := by
    simpa [hsplit] using hq4
  rw [run_append,hfirst] at hq4split
  simp only [Option.bind_some] at hq4split
  have htotal :
      run tm2 ((32+12*a)+(35+3*b)) (s1Config L 1 1 a 0 b h) =
        some (s1Config L 0 0 (a+b+2) (2^b-1) 0
          (h+5+3*b)) := by
    rw [run_append,hprefix]
    simp only [Option.bind_some]
    exact hq4split
  have hv : v2 1 = 0 := v2_of_odd 1 (by decide)
  have hcost : resetPrefixCost 1 1 a b = (32+12*a)+(35+3*b) := by
    simp [resetPrefixCost,hv]
    omega
  rw [hcost]
  exact htotal

#print axioms m1One_q4_prefix_run
#print axioms m1One_q4_prefix_rightShape
#print axioms m1One_q4_prefix_leftFacing
#print axioms m1One_q4_reset_prefix_source

end BB6Coverage.Agent48FinalRst1
