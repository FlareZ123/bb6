import CountedCarryPrefix
import CountedCarryBoundaryTraces
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48Champion

set_option maxHeartbeats 1000000

/-- Away from the two cells changed by the closed-form left sweep, the
post-sweep tape is exactly the source tape. -/
theorem carryLeftSweep_preserves_at (r s : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea r x = true → T x = carryInputBit r x)
    (hs : 0 < s) (hbound : 4*s ≤ 3*r) (x : Int)
    (hx1 : x ≠ 1) (hxb : x ≠ 1-4*(s:Int)) :
    sweptLeft (4*s) T 0 x = T x := by
  have hon := carryInput_leftOnes r s T hmatch hbound
  have hzero : T 1 = false := by
    exact carryInput_unmarked r T hmatch 1 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  rw [carryLeftSweep_closed s T hs hon hzero]
  simp [hx1,hxb]

/-- The left sweep moves its unique zero boundary to head+1. -/
theorem carryLeftSweep_boundary_zero (r s : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea r x = true → T x = carryInputBit r x)
    (hs : 0 < s) (hbound : 4*s ≤ 3*r) :
    sweptLeft (4*s) T 0 (1-4*(s:Int)) = false := by
  have hon := carryInput_leftOnes r s T hmatch hbound
  have hzero : T 1 = false := by
    exact carryInput_unmarked r T hmatch 1 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  rw [carryLeftSweep_closed s T hs hon hzero]
  simp

/-- rho=0: the source's final 4k ones give the nine-cell bridge window. -/
theorem carryBridge0_input_match (k : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea (4*k) x = true →
      T x = carryInputBit (4*k) x) (hk : 0 < k) :
    ∀ i : Int, -1 ≤ i → i ≤ 10 →
      sweptLeft (4*(3*k)) T 0 (-(4*(3*(k:Int)))+i) =
        decide (i ∈ ([2,3,4,5,6,7,8,9,10] : List Int)) := by
  have hs : 0 < 3*k := by omega
  have hb : 4*(3*k) ≤ 3*(4*k) := by omega
  intro i hlo hhi
  have hcases : i = -1 ∨ i = 0 ∨ i = 1 ∨ (2 ≤ i ∧ i ≤ 10) := by omega
  rcases hcases with hneg | hzero | hone | hpos
  · subst i
    have hblank := carryInput_unmarked (4*k) T hmatch
      (-(4*(3*(k:Int))) + (-1)) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k) (3*k) T hmatch hs hb
      (-(4*(3*(k:Int))) + (-1)) (by omega) (by omega)
    have hmem : (-1:Int) ∉ ([2,3,4,5,6,7,8,9,10] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hblank := carryInput_unmarked (4*k) T hmatch
      (-(4*(3*(k:Int)))) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k) (3*k) T hmatch hs hb
      (-(4*(3*(k:Int)))) (by omega) (by omega)
    have hmem : (0:Int) ∉ ([2,3,4,5,6,7,8,9,10] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hval := carryLeftSweep_boundary_zero (4*k) (3*k) T hmatch hs hb
    have hcoord : 1-4*(3*(k:Int)) = -(4*(3*(k:Int)))+1 := by omega
    have hmem : (1:Int) ∉ ([2,3,4,5,6,7,8,9,10] : List Int) := by simp
    simpa [hcoord,hmem] using hval
  · have hval := carryLeftSweep_marked (4*k) (3*k) T hmatch hs hb
      (-(4*(3*(k:Int)))+i) (by omega) (by omega)
    have hmem : i ∈ ([2,3,4,5,6,7,8,9,10] : List Int) := by simp; omega
    simpa [hmem] using hval

/-- rho=1: the residual one and the rightward run give the bridge window. -/
theorem carryBridge1_input_match (k : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea (4*k+3) x = true →
      T x = carryInputBit (4*k+3) x) :
    ∀ i : Int, -2 ≤ i → i ≤ 6 →
      sweptLeft (4*(3*k+2)) T 0 (-(4*(3*(k:Int)+2))+i) =
        decide (i ∈ ([0,2,3,4,5,6] : List Int)) := by
  have hs : 0 < 3*k+2 := by omega
  have hb : 4*(3*k+2) ≤ 3*(4*k+3) := by omega
  intro i hlo hhi
  have hcases : i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨ (2 ≤ i ∧ i ≤ 6) := by omega
  rcases hcases with hneg | hzero | hone | hboundary | hpos
  · subst i
    have hblank := carryInput_unmarked (4*k+3) T hmatch
      (-(4*(3*(k:Int)+2)) + (-2)) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k+3) (3*k+2) T hmatch hs hb
      (-(4*(3*(k:Int)+2)) + (-2)) (by omega) (by omega)
    have hmem : (-2:Int) ∉ ([0,2,3,4,5,6] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hblank := carryInput_unmarked (4*k+3) T hmatch
      (-(4*(3*(k:Int)+2)) + (-1)) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k+3) (3*k+2) T hmatch hs hb
      (-(4*(3*(k:Int)+2)) + (-1)) (by omega) (by omega)
    have hmem : (-1:Int) ∉ ([0,2,3,4,5,6] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hone' := carryInput_marked (4*k+3) T hmatch
      (-(4*(3*(k:Int)+2))) (Or.inl (by constructor <;> omega))
    have hval := carryLeftSweep_preserves_at (4*k+3) (3*k+2) T hmatch hs hb
      (-(4*(3*(k:Int)+2))) (by omega) (by omega)
    have hmem : (0:Int) ∈ ([0,2,3,4,5,6] : List Int) := by simp
    simpa [hmem] using hval.trans hone'
  · subst i
    have hval := carryLeftSweep_boundary_zero (4*k+3) (3*k+2) T hmatch hs hb
    have hcoord : 1-4*(3*(k:Int)+2) = -(4*(3*(k:Int)+2))+1 := by omega
    have hmem : (1:Int) ∉ ([0,2,3,4,5,6] : List Int) := by simp
    simpa [hcoord,hmem] using hval
  · have hval := carryLeftSweep_marked (4*k+3) (3*k+2) T hmatch hs hb
      (-(4*(3*(k:Int)+2))+i) (by omega) (by omega)
    have hmem : i ∈ ([0,2,3,4,5,6] : List Int) := by simp; omega
    simpa [hmem] using hval

/-- rho=2: two residual ones, a rightward guard, and the zero boundary. -/
theorem carryBridge2_input_match (k : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea (4*k+2) x = true →
      T x = carryInputBit (4*k+2) x) :
    ∀ i : Int, -3 ≤ i → i ≤ 2 →
      sweptLeft (4*(3*k+1)) T 0 (-(4*(3*(k:Int)+1))+i) =
        decide (i ∈ ([-1,0,2] : List Int)) := by
  have hs : 0 < 3*k+1 := by omega
  have hb : 4*(3*k+1) ≤ 3*(4*k+2) := by omega
  intro i hlo hhi
  have hcases : i = -3 ∨ i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hcases with hneg | hzero | hone1 | hone0 | hboundary | hpos
  · subst i
    have hblank := carryInput_unmarked (4*k+2) T hmatch
      (-(4*(3*(k:Int)+1)) + (-3)) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k+2) (3*k+1) T hmatch hs hb
      (-(4*(3*(k:Int)+1)) + (-3)) (by omega) (by omega)
    have hmem : (-3:Int) ∉ ([-1,0,2] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hblank := carryInput_unmarked (4*k+2) T hmatch
      (-(4*(3*(k:Int)+1)) + (-2)) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k+2) (3*k+1) T hmatch hs hb
      (-(4*(3*(k:Int)+1)) + (-2)) (by omega) (by omega)
    have hmem : (-2:Int) ∉ ([-1,0,2] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hone := carryInput_marked (4*k+2) T hmatch
      (-(4*(3*(k:Int)+1)) + (-1)) (Or.inl (by constructor <;> omega))
    have hval := carryLeftSweep_preserves_at (4*k+2) (3*k+1) T hmatch hs hb
      (-(4*(3*(k:Int)+1)) + (-1)) (by omega) (by omega)
    have hmem : (-1:Int) ∈ ([-1,0,2] : List Int) := by simp
    simpa [hmem] using hval.trans hone
  · subst i
    have hone := carryInput_marked (4*k+2) T hmatch
      (-(4*(3*(k:Int)+1))) (Or.inl (by constructor <;> omega))
    have hval := carryLeftSweep_preserves_at (4*k+2) (3*k+1) T hmatch hs hb
      (-(4*(3*(k:Int)+1))) (by omega) (by omega)
    have hmem : (0:Int) ∈ ([-1,0,2] : List Int) := by simp
    simpa [hmem] using hval.trans hone
  · subst i
    have hval := carryLeftSweep_boundary_zero (4*k+2) (3*k+1) T hmatch hs hb
    have hcoord : 1-4*(3*(k:Int)+1) = -(4*(3*(k:Int)+1))+1 := by omega
    have hmem : (1:Int) ∉ ([-1,0,2] : List Int) := by simp
    simpa [hcoord,hmem] using hval
  · subst i
    have hval := carryLeftSweep_marked (4*k+2) (3*k+1) T hmatch hs hb
      (-(4*(3*(k:Int)+1))+2) (by omega) (by omega)
    have hmem : (2:Int) ∈ ([-1,0,2] : List Int) := by simp
    simpa [hmem] using hval

/-- rho=3 for k>0: the three residual ones and the zero boundary. -/
theorem carryBridge3_input_match (k : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea (4*k+1) x = true →
      T x = carryInputBit (4*k+1) x) (hk : 0 < k) :
    ∀ i : Int, -4 ≤ i → i ≤ 1 →
      sweptLeft (4*(3*k)) T 0 (-(4*(3*(k:Int)))+i) =
        decide (i ∈ ([-2,-1,0] : List Int)) := by
  have hs : 0 < 3*k := by omega
  have hb : 4*(3*k) ≤ 3*(4*k+1) := by omega
  intro i hlo hhi
  have hcases : i = -4 ∨ i = -3 ∨ i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 := by omega
  rcases hcases with hneg | hzero | hone2 | hone1 | hone0 | hboundary
  · subst i
    have hblank := carryInput_unmarked (4*k+1) T hmatch
      (-(4*(3*(k:Int))) + (-4)) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k+1) (3*k) T hmatch hs hb
      (-(4*(3*(k:Int))) + (-4)) (by omega) (by omega)
    have hmem : (-4:Int) ∉ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hblank := carryInput_unmarked (4*k+1) T hmatch
      (-(4*(3*(k:Int))) + (-3)) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k+1) (3*k) T hmatch hs hb
      (-(4*(3*(k:Int))) + (-3)) (by omega) (by omega)
    have hmem : (-3:Int) ∉ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hone := carryInput_marked (4*k+1) T hmatch
      (-(4*(3*(k:Int))) + (-2)) (Or.inl (by constructor <;> omega))
    have hval := carryLeftSweep_preserves_at (4*k+1) (3*k) T hmatch hs hb
      (-(4*(3*(k:Int))) + (-2)) (by omega) (by omega)
    have hmem : (-2:Int) ∈ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hval.trans hone
  · subst i
    have hone := carryInput_marked (4*k+1) T hmatch
      (-(4*(3*(k:Int))) + (-1)) (Or.inl (by constructor <;> omega))
    have hval := carryLeftSweep_preserves_at (4*k+1) (3*k) T hmatch hs hb
      (-(4*(3*(k:Int))) + (-1)) (by omega) (by omega)
    have hmem : (-1:Int) ∈ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hval.trans hone
  · subst i
    have hone := carryInput_marked (4*k+1) T hmatch
      (-(4*(3*(k:Int)))) (Or.inl (by constructor <;> omega))
    have hval := carryLeftSweep_preserves_at (4*k+1) (3*k) T hmatch hs hb
      (-(4*(3*(k:Int)))) (by omega) (by omega)
    have hmem : (0:Int) ∈ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hval.trans hone
  · subst i
    have hval := carryLeftSweep_boundary_zero (4*k+1) (3*k) T hmatch hs hb
    have hcoord : 1-4*(3*(k:Int)) = -(4*(3*(k:Int)))+1 := by omega
    have hmem : (1:Int) ∉ ([-2,-1,0] : List Int) := by simp
    simpa [hcoord,hmem] using hval

/-- The r=1 short branch enters the rho=3 bridge without a left sweep. -/
theorem carryBridge3_input_match_r1 (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea 1 x = true → T x = carryInputBit 1 x) :
    ∀ i : Int, -4 ≤ i → i ≤ 1 →
      T i = decide (i ∈ ([-2,-1,0] : List Int)) := by
  intro i hlo hhi
  have hcases : i = -4 ∨ i = -3 ∨ i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 := by omega
  rcases hcases with hneg | hzero | hone2 | hone1 | hone0 | hboundary
  · subst i
    have hblank := carryInput_unmarked 1 T hmatch (-4) (by omega) (by omega)
      (by simp [carryInputBit])
    have hmem : (-4:Int) ∉ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hblank
  · subst i
    have hblank := carryInput_unmarked 1 T hmatch (-3) (by omega) (by omega)
      (by simp [carryInputBit])
    have hmem : (-3:Int) ∉ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hblank
  · subst i
    have hone := carryInput_marked 1 T hmatch (-2) (Or.inl (by constructor <;> omega))
    have hmem : (-2:Int) ∈ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hone
  · subst i
    have hone := carryInput_marked 1 T hmatch (-1) (Or.inl (by constructor <;> omega))
    have hmem : (-1:Int) ∈ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hone
  · subst i
    have hone := carryInput_marked 1 T hmatch 0 (Or.inl (by constructor <;> omega))
    have hmem : (0:Int) ∈ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hone
  · subst i
    have hblank := carryInput_unmarked 1 T hmatch 1 (by omega) (by omega)
      (by simp [carryInputBit])
    have hmem : (1:Int) ∉ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hblank


/-- Finish the arbitrary counted right sweep with the open-end D-tail.
The final E head is at 7, and the source cell at 7 is preserved. -/
theorem carryFinishFromD (T : Int → Bool) (h : Int) (n : Nat)
    (hfinish : h+3*(n:Int) = -2)
    (hseg : carrySegmentOnes T h (3*n+7))
    (hz0 : T (h+3*(n:Int)+7) = false)
    (hz1 : T (h+3*(n:Int)+8) = false) :
    ∃ T' : Int → Bool,
      run tm2 (3*n+15) ⟨3,h,T⟩ = some ⟨4,7,T'⟩ ∧
      T' 1 = true ∧ T' 2 = true ∧ T' 3 = true ∧
      T' 4 = true ∧ T' 5 = false ∧ T' 6 = true ∧
      (∀ x, 6 < x → T' x = T x) := by
  let T3 := sweptRight n T h
  have hseg0 : carrySegmentOnes T h (3*n) := by
    intro i hi
    exact hseg i (by omega)
  have hright : rightOnes T h n := rightOnes_of_segment n T h hseg0
  have hrunRight0 := counted_right_sweep n T h hright
  have hrunRight : run tm2 (3*n) ⟨3,h,T⟩ = some ⟨3,-2,T3⟩ := by
    simpa [T3,hfinish] using hrunRight0
  have hseven := sweptRight_keeps_seven n T h hseg
  have hzeros := sweptRight_keeps_two_zeroes n T h hz0 hz1
  have hlocal : ∀ x, carryDTail15OpenArea (x-(-2)) = true →
      (embed carryDTail15Base).tape (x-(-2)) = T3 x := by
    intro x hx
    have haux : 0 ≤ x+2 ∧ x+2 ≤ 8 := by
      simpa [carryDTail15OpenArea] using hx
    have hrange : -2 ≤ x ∧ x ≤ 6 := by omega
    have hcases : x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨
        x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · subst x
      have hv := hseven 0 (by omega)
      have hv' : T3 (-2) = true := by simpa [T3,hfinish] using hv
      simpa [embed,carryDTail15Base] using hv'
    · subst x
      have hv := hseven 1 (by omega)
      have hv' : T3 (-1) = true := by simpa [T3,hfinish] using hv
      simpa [embed,carryDTail15Base] using hv'
    · subst x
      have hv := hseven 2 (by omega)
      have hv' : T3 0 = true := by simpa [T3,hfinish] using hv
      simpa [embed,carryDTail15Base] using hv'
    · subst x
      have hv := hseven 3 (by omega)
      have hv' : T3 1 = true := by simpa [T3,hfinish] using hv
      simpa [embed,carryDTail15Base] using hv'
    · subst x
      have hv := hseven 4 (by omega)
      have hv' : T3 2 = true := by simpa [T3,hfinish] using hv
      simpa [embed,carryDTail15Base] using hv'
    · subst x
      have hv := hseven 5 (by omega)
      have hv' : T3 3 = true := by simpa [T3,hfinish] using hv
      simpa [embed,carryDTail15Base] using hv'
    · subst x
      have hv := hseven 6 (by omega)
      have hv' : T3 4 = true := by simpa [T3,hfinish] using hv
      simpa [embed,carryDTail15Base] using hv'
    · subst x
      have hv' : T3 5 = false := by simpa [T3,hfinish] using hzeros.1
      simpa [embed,carryDTail15Base] using hv'
    · subst x
      have hv' : T3 6 = false := by simpa [T3,hfinish] using hzeros.2
      simpa [embed,carryDTail15Base] using hv'
  have htail := carryDTail15_openEnd T3 (-2) hlocal
  let T4 := (frame (fun x => carryDTail15OpenArea (x+2)) T3
    (shiftConfig (-2) (embed carryDTail15Final))).tape
  have hrunTail : run tm2 15 ⟨3,-2,T3⟩ = some ⟨4,7,T4⟩ := by
    simpa [T4,shiftConfig,embed,carryDTail15Final] using htail
  have hrun := run_compose tm2 (3*n) 15
    ⟨3,h,T⟩ ⟨3,-2,T3⟩ ⟨4,7,T4⟩ hrunRight hrunTail
  have hframe : ∀ x, -2 ≤ x → x ≤ 6 →
      T4 x = (embed carryDTail15Final).tape (x+2) := by
    intro x hlo hhi
    have harea : carryDTail15OpenArea (x+2) = true := by
      simp [carryDTail15OpenArea]
      omega
    simp [T4,frame,shiftConfig,harea]
  have hout : ∀ x, 6 < x → T4 x = T x := by
    intro x hx
    have harea : carryDTail15OpenArea (x+2) = false := by
      simp [carryDTail15OpenArea]
      omega
    have hfuture : T3 x = T x := by
      apply sweptRight_future
      rw [hfinish]
      omega
    simp [T4,frame,shiftConfig,harea,hfuture]
  refine ⟨T4,hrun,?_,?_,?_,?_,?_,?_,hout⟩
  · have hv := hframe 1 (by omega) (by omega)
    simpa [embed,carryDTail15Final] using hv
  · have hv := hframe 2 (by omega) (by omega)
    simpa [embed,carryDTail15Final] using hv
  · have hv := hframe 3 (by omega) (by omega)
    simpa [embed,carryDTail15Final] using hv
  · have hv := hframe 4 (by omega) (by omega)
    simpa [embed,carryDTail15Final] using hv
  · have hv := hframe 5 (by omega) (by omega)
    simpa [embed,carryDTail15Final] using hv
  · have hv := hframe 6 (by omega) (by omega)
    simpa [embed,carryDTail15Final] using hv


end BB6Coverage.Agent48Champion
