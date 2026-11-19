import ChampionRootBridge
import Q4Suffix
import Lean.Elab.Tactic.Omega

/-!
# P2 continuation from the actual 0101 residual boundary

The proposed 4-step q4/S0 final bridge expects 0100. The authentic
second-cycle residual instead gives 0101, followed on the left by seven
ones and then two zeroes. This finite 73-step trace is the exact local
continuation from that source window: state 3 at head h reaches state 4
at head h-1, with a three-cell rightward one-run. The arbitrary exterior
is preserved by the frame lift.

This is an intermediate source draft; it has not yet passed Lean
compilation in the repository environment.
-/

namespace BB6Coverage.Agent38P2ActualBoundary

open BB6Coverage
open BB6Coverage.Agent48Champion

/-- The 13-cell local window, relative to the state-3 head. -/
def p2ActualBoundaryInside (x : Int) : Bool :=
  decide (-12 ≤ x ∧ x ≤ 1)

/-- Input: 0101 to the right-facing side, seven ones to the left,
then two zeroes. -/
def p2ActualBoundaryStart : FConfig :=
  ⟨3, 0, [-1,-3,-4,-5,-6,-7,-8,-9,-10]⟩

/-- After 73 moves, state 4 is at the old head minus one. -/
def p2ActualBoundaryEnd : FConfig :=
  ⟨4, -1, [-12,-11,-10,-9,-8,-7,-4,-2,-1,0,1]⟩

theorem p2ActualBoundary_exact :
    fRun tm2 73 p2ActualBoundaryStart =
      some p2ActualBoundaryEnd := by
  decide

theorem p2ActualBoundary_heads :
    (List.range 73).all (fun k =>
      match fRun tm2 k p2ActualBoundaryStart with
      | none => true
      | some f => p2ActualBoundaryInside f.head) = true := by
  decide

/-- Exact arbitrary-tape input contract for the 73-step bridge. -/
def p2ActualBoundaryInput (T : Int → Bool) (h : Int) : Prop :=
  T h = false ∧
  T (h-1) = true ∧
  T (h-2) = false ∧
  T (h-3) = true ∧
  (∀ i : Nat, i<7 → T (h-4-(i:Int)) = true) ∧
  T (h-11) = false ∧
  T (h-12) = false ∧
  T (h+1) = false

/-- Source-level lift of the finite trace to an arbitrary bi-infinite tape. -/
theorem p2ActualBoundary_at (T : Int → Bool) (h : Int)
    (hin : p2ActualBoundaryInput T h) :
    run tm2 73 ⟨3,h,T⟩ =
      some (frameAt T h p2ActualBoundaryInside p2ActualBoundaryEnd) := by
  rcases hin with ⟨h0,hm1,hm2,hm3,hones,hm11,hm12,hp1⟩
  apply bridgeAt T h p2ActualBoundaryInside
    p2ActualBoundaryStart p2ActualBoundaryEnd 73 rfl
    p2ActualBoundary_exact p2ActualBoundary_heads
  intro x hx
  have hrange : -12 ≤ x ∧ x ≤ 1 := by
    simpa [p2ActualBoundaryInside] using hx
  have hcases :
      x = -12 ∨ x = -11 ∨ x = -10 ∨ x = -9 ∨
      x = -8 ∨ x = -7 ∨ x = -6 ∨ x = -5 ∨
      x = -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨
      x = 0 ∨ x = 1 := by omega
  rcases hcases with
    hx12|hx11|hx10|hx9|hx8|hx7|hx6|hx5|hx4|hx3|hx2|hx1|hx0|hxp1
  · have heq : h+(-12:Int) = h-12 := by omega
    rw [heq]
    simpa [p2ActualBoundaryStart] using hm12
  · have heq : h+(-11:Int) = h-11 := by omega
    rw [heq]
    simpa [p2ActualBoundaryStart] using hm11
  · have heq : h+(-10:Int) = h-4-(6:Int) := by omega
    rw [heq]
    simpa [p2ActualBoundaryStart] using hones 6 (by omega)
  · have heq : h+(-9:Int) = h-4-(5:Int) := by omega
    rw [heq]
    simpa [p2ActualBoundaryStart] using hones 5 (by omega)
  · have heq : h+(-8:Int) = h-4-(4:Int) := by omega
    rw [heq]
    simpa [p2ActualBoundaryStart] using hones 4 (by omega)
  · have heq : h+(-7:Int) = h-4-(3:Int) := by omega
    rw [heq]
    simpa [p2ActualBoundaryStart] using hones 3 (by omega)
  · have heq : h+(-6:Int) = h-4-(2:Int) := by omega
    rw [heq]
    simpa [p2ActualBoundaryStart] using hones 2 (by omega)
  · have heq : h+(-5:Int) = h-4-(1:Int) := by omega
    rw [heq]
    simpa [p2ActualBoundaryStart] using hones 1 (by omega)
  · have heq : h+(-4:Int) = h-4-(0:Int) := by omega
    rw [heq]
    simpa [p2ActualBoundaryStart] using hones 0 (by omega)
  · have heq : h+(-3:Int) = h-3 := by omega
    rw [heq]
    simpa [p2ActualBoundaryStart] using hm3
  · have heq : h+(-2:Int) = h-2 := by omega
    rw [heq]
    simpa [p2ActualBoundaryStart] using hm2
  · have heq : h+(-1:Int) = h-1 := by omega
    rw [heq]
    simpa [p2ActualBoundaryStart] using hm1
  · simpa [p2ActualBoundaryStart] using h0
  · simpa [p2ActualBoundaryStart] using hp1

/-- The bridge ends in state 4 with its head and next two cells set to one. -/
theorem p2ActualBoundary_end_right_ones
    (T : Int → Bool) (h : Int) :
    (frameAt T h p2ActualBoundaryInside p2ActualBoundaryEnd).state = 4 ∧
    (frameAt T h p2ActualBoundaryInside p2ActualBoundaryEnd).head = h-1 ∧
    (frameAt T h p2ActualBoundaryInside p2ActualBoundaryEnd).tape (h-1) = true ∧
    (frameAt T h p2ActualBoundaryInside p2ActualBoundaryEnd).tape h = true ∧
    (frameAt T h p2ActualBoundaryInside p2ActualBoundaryEnd).tape (h+1) = true := by
  simp [frameAt_state,frameAt_head,frameAt_tape,
    p2ActualBoundaryInside,p2ActualBoundaryEnd]

/-- State 4 scans a contiguous rightward one-run without changing the tape. -/
theorem state4_right_ones (k : Nat) (T : Int → Bool) (h : Int)
    (hones : ∀ i : Nat, i<k → T (h+(i:Int)) = true) :
    run tm2 k ⟨4,h,T⟩ = some ⟨4,h+(k:Int),T⟩ := by
  induction k generalizing T h with
  | zero =>
      simp [run]
  | succ k ih =>
      have h0 : T h = true := by
        simpa using hones 0 (by omega)
      have hstep :
          run tm2 1 ⟨4,h,T⟩ = some ⟨4,h+1,T⟩ := by
        have htrans : tm2 ((4:Fin 6),true) = some ⟨true,true,4⟩ := rfl
        simp [run,rawStep,readSlot,applyMove,h0,htrans]
      have htail : ∀ i : Nat, i<k → T (h+1+(i:Int)) = true := by
        intro i hi
        have hp := hones (i+1) (by omega)
        have heq : h+1+(i:Int) = h+((i+1:Int)) := by omega
        rw [heq]
        exact hp
      have hrun := ih T (h+1) htail
      have hcost : k+1 = 1+k := by omega
      rw [hcost,run_append,hstep]
      simpa [Int.add_assoc] using hrun

#print axioms p2ActualBoundary_exact
#print axioms p2ActualBoundary_heads
#print axioms p2ActualBoundary_at
#print axioms p2ActualBoundary_end_right_ones
#print axioms state4_right_ones



/-- A single source transition that writes one cell. -/
def p2WriteOne (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x = h then true else T x

/-- The two zero cells following the long q4 one-run are written to one. -/
def p2AfterTwoZeros (T : Int → Bool) (H : Int) : Int → Bool :=
  p2WriteOne (p2WriteOne T (H+5)) (H+6)

/-- From q4 on the first of two zeroes, the source takes two moves to
state 1 at the first cell of the following three-one blocks. -/
theorem p2_two_zero_setup (T : Int → Bool) (H : Int)
    (h0 : T (H+5) = false) (h1 : T (H+6) = false) :
    run tm2 2 ⟨4,H+5,T⟩ =
      some ⟨1,H+7,p2AfterTwoZeros T H⟩ := by
  have hstep0 :
      run tm2 1 ⟨4,H+5,T⟩ =
        some ⟨0,H+6,p2WriteOne T (H+5)⟩ := by
    have htrans : tm2 ((4:Fin 6),false) = some ⟨true,true,0⟩ := rfl
    simp [run,rawStep,readSlot,applyMove,h0,htrans,p2WriteOne]
  have hread1 : p2WriteOne T (H+5) (H+6) = false := by
    simp [p2WriteOne]
    exact h1
  have hstep1 :
      run tm2 1 ⟨0,H+6,p2WriteOne T (H+5)⟩ =
        some ⟨1,H+7,p2AfterTwoZeros T H⟩ := by
    have htrans : tm2 ((0:Fin 6),false) = some ⟨true,true,1⟩ := rfl
    simp [run,rawStep,readSlot,applyMove,hread1,htrans,
      p2WriteOne,p2AfterTwoZeros]
  rw [show 2 = 1+1 by omega,run_append,hstep0]
  simp only [Option.bind_some]
  exact hstep1

/-- The state-1 boundary after the final three-one block writes one and
moves left into state 2. -/
theorem p2_final_zero (T : Int → Bool) (h : Int)
    (hblank : T h = false) :
    run tm2 1 ⟨1,h,T⟩ =
      some ⟨2,h-1,p2WriteOne T h⟩ := by
  have htrans : tm2 ((1:Fin 6),false) = some ⟨true,false,2⟩ := rfl
  simp [run,rawStep,readSlot,applyMove,hblank,htrans,p2WriteOne]

/-- Right continuation from the actual-boundary bridge's q4 output.
The q4 state scans the long one-run, crosses two zeroes, converts the
following d1-blocks to d0-blocks, and stops in state 2 at the next
blank boundary. -/
theorem p2ActualRightContinuation
    (H a : Nat) (T : Int → Bool)
    (hones : ∀ i : Nat, i < H+3 → T (2+(i:Int)) = true)
    (hzero5 : T ((H:Int)+5) = false)
    (hzero6 : T ((H:Int)+6) = false)
    (hblocks :
      BB6Coverage.Agent8Q4Suffix.d1BlocksOn
        (p2AfterTwoZeros T (H:Int)) ((H:Int)+7) (2^a))
    (hblank :
      p2AfterTwoZeros T (H:Int)
        ((H:Int)+7+(3*(2^a:Int))) = false) :
    run tm2 (H+6+3*2^a) ⟨4,2,T⟩ =
      some ⟨2,(H:Int)+6+(3*(2^a:Int)),
        p2WriteOne
          (BB6Coverage.Agent8Q4Suffix.d0Sweep
            (2^a) (p2AfterTwoZeros T (H:Int)) ((H:Int)+7))
          ((H:Int)+7+(3*(2^a:Int)))⟩ := by
  have hscan4raw :=
    state4_right_ones (H+3) T 2 hones
  have hhead4 : (2:Int)+((H+3:Int)) = (H:Int)+5 := by omega
  have hscan4 :
      run tm2 (H+3) ⟨4,2,T⟩ =
        some ⟨4,(H:Int)+5,T⟩ := by
    simpa [hhead4] using hscan4raw
  have hsetup :=
    p2_two_zero_setup T (H:Int) hzero5 hzero6
  have hscan1 :=
    BB6Coverage.Agent8Q4Suffix.state1_d1_blocks_right
      (2^a) (p2AfterTwoZeros T (H:Int)) ((H:Int)+7) hblocks
  have hblank' :
      BB6Coverage.Agent8Q4Suffix.d0Sweep
        (2^a) (p2AfterTwoZeros T (H:Int)) ((H:Int)+7)
        ((H:Int)+7+(3*(2^a:Int))) = false := by
    rw [BB6Coverage.Agent8Q4Suffix.d0Sweep_after]
    · exact hblank
    · omega
  have hfinal :=
    p2_final_zero
      (BB6Coverage.Agent8Q4Suffix.d0Sweep
        (2^a) (p2AfterTwoZeros T (H:Int)) ((H:Int)+7))
      ((H:Int)+7+(3*(2^a:Int))) hblank'
  have hrest :
      run tm2 (2+(3*2^a+1)) ⟨4,(H:Int)+5,T⟩ =
        some ⟨2,(H:Int)+6+(3*(2^a:Int)),
          p2WriteOne
            (BB6Coverage.Agent8Q4Suffix.d0Sweep
              (2^a) (p2AfterTwoZeros T (H:Int)) ((H:Int)+7))
            ((H:Int)+7+(3*(2^a:Int)))⟩ := by
    have hcost : 2+(3*2^a+1) = 2+(3*2^a)+1 := by omega
    rw [hcost,run_append,hsetup]
    simp only [Option.bind_some]
    rw [run_append,hscan1]
    simp only [Option.bind_some]
    exact hfinal
  have hcost : H+6+3*2^a = (H+3)+(2+(3*2^a+1)) := by omega
  rw [hcost,run_append,hscan4]
  simp only [Option.bind_some]
  exact hrest

#print axioms p2_two_zero_setup
#print axioms p2_final_zero
#print axioms p2ActualRightContinuation

end BB6Coverage.Agent38P2ActualBoundary
