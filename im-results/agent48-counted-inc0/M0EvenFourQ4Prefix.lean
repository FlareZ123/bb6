import CountedReset
import CountedSweep
import ChampionRootBridge
import S1Encoder
import CountedQ4Prefix
import M0EvenFourQ4Bridge
import Lean.Elab.Tactic.Omega

/-!
# Base m=0,n=4 even q4 source prefix

This composes the 3a-cell original-table left sweep, the 51-step
m0EvenFour bridge, and the 3(a-1)-cell E-scan. The theorem is the
L=3 base source run needed for the later arbitrary-binary-tail lift.
-/

namespace BB6Coverage.Agent48M0EvenFourQ4Prefix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent48M0EvenFourQ4Bridge

/-- Explicit tape at the m=0,n=4 even q4 cut. -/
def m0EvenFourQ4CutTape (a b : Nat) (h : Int) : Int → Bool :=
  let T := (s1Config 3 4 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  (frameAt T1 (h-(N:Int)) m0EvenFourInside m0EvenFourBridgeEnd).tape

/-- The fixed bridge frame agrees with the swept source tape outside
its local [-12,3] window. -/
private theorem m0EvenFourQ4CutTape_eq_swept
    (a b : Nat) (h x : Int)
    (hout : m0EvenFourInside (x-(h-((3*a : Nat) : Int))) = false) :
    m0EvenFourQ4CutTape a b h x =
      sweptLeft (3*a) (s1Config 3 4 0 a 0 b h).tape h x := by
  let T := (s1Config 3 4 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_outside T1 (h-(N:Int))
    m0EvenFourInside m0EvenFourBridgeEnd x hout
  simpa [m0EvenFourQ4CutTape,T,N,T1] using hf

private theorem m0EvenFourQ4CutTape_eq_end_inside
    (a b : Nat) (h x : Int)
    (hin : m0EvenFourInside (x-(h-((3*a : Nat) : Int))) = true) :
    m0EvenFourQ4CutTape a b h x =
      decide ((x-(h-((3*a : Nat) : Int))) ∈ m0EvenFourBridgeEnd.marked) := by
  let T := (s1Config 3 4 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_inside T1 (h-(N:Int))
    m0EvenFourInside m0EvenFourBridgeEnd x hin
  simpa [m0EvenFourQ4CutTape,T,N,T1] using hf

private theorem m0EvenFourQ4CutTape_eq_source_right
    (a b : Nat) (h x : Int) (ha : 0 < a) (hx : h+2 ≤ x) :
    m0EvenFourQ4CutTape a b h x =
      (s1Config 3 4 0 a 0 b h).tape x := by
  let T := (s1Config 3 4 0 a 0 b h).tape
  have hgt : 3 < x-(h-((3*a : Nat) : Int)) := by omega
  have hnot : ¬(-12 ≤ x-(h-((3*a : Nat) : Int)) ∧
      x-(h-((3*a : Nat) : Int)) ≤ 3) := by omega
  have hout : m0EvenFourInside
      (x-(h-((3*a : Nat) : Int))) = false := by
    change decide (-12 ≤ _ ∧ _ ≤ 3) = false
    exact decide_eq_false_iff_not.mpr hnot
  have hcut := m0EvenFourQ4CutTape_eq_swept a b h x hout
  have hpres := sweptLeft_preserves_right (3*a) T h x (by omega)
  simpa [T] using hcut.trans hpres

/-- The q4 cut follows a 3a counted sweep, the fixed 51-step bridge,
and a 3(a-1)-cell E-scan. -/
theorem m0EvenFour_q4_prefix_run
    (a b : Nat) (h : Int) (ha : 0 < a) :
    run tm2 (48+12*a)
      ⟨3,h,(s1Config 3 4 0 a 0 b h).tape⟩ =
      some ⟨4,h,m0EvenFourQ4CutTape a b h⟩ := by
  let T := (s1Config 3 4 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := (frameAt T1 hN m0EvenFourInside m0EvenFourBridgeEnd).tape
  have hleftFacing :
      s1LeftFacing 3 4 0 a 0 =
        d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh := by
    simp [s1LeftFacing,binDec_zero,m0Even_binDec_three_four,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 4 0 a 0 b h i
    have hside : sideBit (s1LeftFacing 3 4 0 a 0) i = true := by
      rw [hleftFacing]
      let R : List Bool := markerWord 0 ++ (d0 ++ (d1 ++ (d1 ++ (d0 ++ lh))))
      simp only [List.append_assoc]
      change sideBit (d1pow a ++ R) i = true
      have hiLen : i < (d1pow a).length := by
        simpa [d1pow_length] using hi
      rw [sideBit_append_left (d1pow a) R i hiLen]
      exact sideBit_d1pow_true a i (by simpa [d1pow_length] using hi)
    simpa [T,hside] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 4 0 a 0 b h 0
    simpa [T,s1PhysicalRight_source,sideBit] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch := m0EvenFourBridge_input_match a b h ha
  have hBridge := bridgeAt T1 hN m0EvenFourInside
    m0EvenFourBridgeStart m0EvenFourBridgeEnd 51 rfl
    m0EvenFourBridge_exact m0EvenFourBridge_heads hmatch
  have hBridge' :
      run tm2 51 ⟨3,hN,T1⟩ = some ⟨4,hN+3,T2⟩ := by
    have hframeConfig :
        frameAt T1 hN m0EvenFourInside m0EvenFourBridgeEnd =
          (⟨4,hN+3,T2⟩ : Config) := by
      apply config_ext
      · simp [frameAt_state,m0EvenFourBridgeEnd]
      · simp [frameAt_head,m0EvenFourBridgeEnd] <;> omega
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
      have hin : m0EvenFourInside ((hN+3)-(h-((3*a:Nat):Int))) = true := by
        rw [hcoord]
        decide
      have hcut := m0EvenFourQ4CutTape_eq_end_inside a b h (hN+3) hin
      have hmark :
          decide (((hN+3)-(h-((3*a:Nat):Int))) ∈ m0EvenFourBridgeEnd.marked) = true := by
        rw [hcoord]
        simp [m0EvenFourBridgeEnd]
      have htrue : m0EvenFourQ4CutTape a b h (hN+3) = true :=
        hcut.trans hmark
      simpa [m0EvenFourQ4CutTape,T,N,T1,hN,T2] using htrue
    · let x : Int := hN+3+(i:Int)
      have hgt : 3 < x-hN := by
        dsimp [x]
        omega
      have hout : m0EvenFourInside (x-hN) = false := by
        simp [m0EvenFourInside,hgt]
      have hframe : T2 x = T1 x := by
        simpa [T2] using
          frameAt_tape_outside T1 hN m0EvenFourInside m0EvenFourBridgeEnd x hout
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
      run tm2 (3*(a-1)) ⟨4,hN+3,T2⟩ = some ⟨4,h,T2⟩ := by
    simpa [hhead] using hScan
  have htotal : run tm2 (3*N+(51+3*(a-1))) ⟨3,h,T⟩ =
      some ⟨4,h,T2⟩ := by
    rw [run_append,hSweep]
    simp only [Option.bind_some]
    rw [run_append,hBridge']
    simp only [Option.bind_some]
    exact hscan
  have hnum : 48+12*a = 3*N+(51+3*(a-1)) := by
    dsimp [N]
    omega
  simpa [T,N,T1,hN,T2,m0EvenFourQ4CutTape,hnum] using htotal

#print axioms m0EvenFour_q4_prefix_run

end BB6Coverage.Agent48M0EvenFourQ4Prefix
