import CountedCarryLeftOutput
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent24CarryLeftOutput

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent3CarryLeftOutput

set_option maxHeartbeats 3000000

/-- Residue 2: the bridge seed is the three-cell terminal d1 block
followed by the d0 stream. The common right sweep supplies the rest. -/
theorem carryLongPrefix_r2_left (k : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea (4*k+2) x = true →
      T x = carryInputBit (4*k+2) x) :
    ∃ T' : Int → Bool,
      run tm2 (15+12*(4*k+2)) ⟨3,0,T⟩ = some ⟨4,7,T'⟩ ∧
      (∀ x, x ≤ 0 → T' x = carryLeftOutputBit (4*k+2) T x) := by
  let h' : Int := -(4*(3*(k:Int)+1))
  let T1 := sweptLeft (4*(3*k+1)) T 0
  have hs : 0 < 3*k+1 := by omega
  have hb : 4*(3*k+1) ≤ 3*(4*k+2) := by omega
  have hon := carryInput_leftOnes (4*k+2) (3*k+1) T hmatch hb
  have hzero : T 1 = false := by
    exact carryInput_unmarked (4*k+2) T hmatch 1 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  have hleft0 := counted_left_sweep (4*(3*k+1)) T 0 hon hzero
  have hleft : run tm2 (3*(4*(3*k+1))) ⟨3,0,T⟩ =
      some ⟨3,h',T1⟩ := by
    simpa [h',T1,Int.zero_sub] using hleft0
  have hmatchB := carryBridge2_input_match k T hmatch
  have hbridge0 := carryBridge2 T1 h' hmatchB
  let T2 := (frame (fun x => carryBridgeArea2 (x-h')) T1
    (shiftConfig h' (embed carryBridgeFinal2))).tape
  have hbridge : run tm2 12 ⟨3,h',T1⟩ =
      some ⟨3,2+h',T2⟩ := by
    simpa [T2,frame,shiftConfig,embed,carryBridgeFinal2] using hbridge0
  have hseg0 : carrySegmentOnes T2 (h'+2) (3*(4*k)+7) := by
    apply frame_head_segment carryBridgeArea2 T1 (embed carryBridgeFinal2)
      h' 2 (3*(4*k)+7)
    · simp [carryBridgeArea2]
    · simp [embed,carryBridgeFinal2]
    · intro i hi
      simp [carryBridgeArea2]
      omega
    · intro i hi
      have hv := carryLeftSweep_marked (4*k+2) (3*k+1) T hmatch hs hb
        (h'+2+(i:Int)) (by omega) (by omega)
      simpa [T1] using hv
  have hseg : carrySegmentOnes T2 (2+h') (3*(4*k)+7) := by
    simpa [Int.add_comm] using hseg0
  have h5input : T 5 = false := by
    exact carryInput_unmarked (4*k+2) T hmatch 5 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  have h6input : T 6 = false := by
    exact carryInput_unmarked (4*k+2) T hmatch 6 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  have h5sweep : T1 5 = T 5 := by
    exact carryLeftSweep_preserves_at (4*k+2) (3*k+1) T hmatch hs hb 5
      (by omega) (by omega)
  have h6sweep : T1 6 = T 6 := by
    exact carryLeftSweep_preserves_at (4*k+2) (3*k+1) T hmatch hs hb 6
      (by omega) (by omega)
  have h5area : carryBridgeArea2 (5-h') = false := by
    simp [carryBridgeArea2,h']
    omega
  have h6area : carryBridgeArea2 (6-h') = false := by
    simp [carryBridgeArea2,h']
    omega
  have h5 : T2 5 = false := by
    simp [T2,frame,shiftConfig,h5area,h5sweep,h5input]
  have h6 : T2 6 = false := by
    simp [T2,frame,shiftConfig,h6area,h6sweep,h6input]
  let nR := 4*k
  have hfinish : (2+h')+3*(nR:Int) = -2 := by
    dsimp [h',nR]
    omega
  have hz0 : T2 ((2+h')+3*(nR:Int)+7) = false := by
    have heq : (2+h')+3*(nR:Int)+7 = 5 := by omega
    simpa [heq] using h5
  have hz1 : T2 ((2+h')+3*(nR:Int)+8) = false := by
    have heq : (2+h')+3*(nR:Int)+8 = 6 := by omega
    simpa [heq] using h6
  have hseed : ∀ x, x < 2+h' →
      T2 x = carryLeftOutputBit (4*k+2) T x := by
    intro x hx
    by_cases hfar : x < -3*(4*(k:Int)+2)-2
    · have ha : carryBridgeArea2 (x-h') = false := by
        simp [carryBridgeArea2,h']
        omega
      have hpres := carryLeftSweep_preserves_at (4*k+2) (3*k+1) T hmatch hs hb x
        (by omega) (by omega)
      simp [T2,T1,frame,shiftConfig,ha,hpres,carryLeftOutputBit,hfar,h']
    · have hcases : x-h' = -4 ∨ x-h' = -3 ∨ x-h' = -2 ∨
          x-h' = -1 ∨ x-h' = 0 ∨ x-h' = 1 := by
        simp [h']
        omega
      rcases hcases with hi4 | hi3 | hi2 | hi1 | hi0 | hi1p
      · have hxEq : x = h'+(-4) := by omega
        have ha : carryBridgeArea2 ((h'+(-4))-h') = false := by
          simp [carryBridgeArea2]
          omega
        have hpres := carryLeftSweep_preserves_at (4*k+2) (3*k+1) T hmatch hs hb
          (h'+(-4)) (by omega) (by omega)
        have harea : carryInputArea (4*k+2) (h'+(-4)) = true := by
          simp [carryInputArea,h']
          omega
        have hbit : carryInputBit (4*k+2) (h'+(-4)) = true := by
          simp [carryInputBit,h']
          omega
        have hmark : T (h'+(-4)) = true := by
          rw [hmatch (h'+(-4)) harea]
          exact hbit
        have hleft : T2 (h'+(-4)) = true := by
          simp [T2,T1,frame,shiftConfig,ha,hpres,hmark,h']
        have hright : carryLeftOutputBit (4*k+2) T (h'+(-4)) = true := by
          simp [carryLeftOutputBit,h']
          omega
        simpa [hxEq] using hleft.trans hright.symm
      · have hxEq : x = h'+(-3) := by omega
        have hcase : T2 (h'+(-3)) =
            carryLeftOutputBit (4*k+2) T (h'+(-3)) := by
          simp [T2,frame,shiftConfig,carryBridgeArea2,embed,carryBridgeFinal2,
            carryLeftOutputBit,h'] <;> omega only [h']
        simpa [hxEq] using hcase
      · have hxEq : x = h'+(-2) := by omega
        have hcase : T2 (h'+(-2)) =
            carryLeftOutputBit (4*k+2) T (h'+(-2)) := by
          simp [T2,frame,shiftConfig,carryBridgeArea2,embed,carryBridgeFinal2,
            carryLeftOutputBit,h'] <;> omega only [h']
        simpa [hxEq] using hcase
      · have hxEq : x = h'+(-1) := by omega
        have hcase : T2 (h'+(-1)) =
            carryLeftOutputBit (4*k+2) T (h'+(-1)) := by
          simp [T2,frame,shiftConfig,carryBridgeArea2,embed,carryBridgeFinal2,
            carryLeftOutputBit,h'] <;> omega only [h']
        simpa [hxEq] using hcase
      · have hxEq : x = h'+0 := by omega
        have hcase : T2 (h'+0) =
            carryLeftOutputBit (4*k+2) T (h'+0) := by
          simp [T2,frame,shiftConfig,carryBridgeArea2,embed,carryBridgeFinal2,
            carryLeftOutputBit,h'] <;> omega only [h']
        simpa [hxEq] using hcase
      · have hxEq : x = h'+1 := by omega
        have hcase : T2 (h'+1) =
            carryLeftOutputBit (4*k+2) T (h'+1) := by
          simp [T2,frame,shiftConfig,carryBridgeArea2,embed,carryBridgeFinal2,
            carryLeftOutputBit,h'] <;> omega only [h']
        simpa [hxEq] using hcase
  have htotal := carryFinishWithLeftPattern (4*k+2)
    (3*(4*(3*k+1))) 12 nR ⟨3,0,T⟩ ⟨3,h',T1⟩ T T2 (2+h')
    hleft hbridge (by dsimp [nR]; omega) hfinish hseg hz0 hz1 hseed
    (by dsimp [h']; omega) (by dsimp [h']; omega)
  exact htotal

/-- Residue 3: the bridge seed is the terminal d1 block followed by
the d0 stream. The common right sweep supplies the rest. -/
theorem carryLongPrefix_r3_left (k : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea (4*k+3) x = true →
      T x = carryInputBit (4*k+3) x) :
    ∃ T' : Int → Bool,
      run tm2 (15+12*(4*k+3)) ⟨3,0,T⟩ = some ⟨4,7,T'⟩ ∧
      (∀ x, x ≤ 0 → T' x = carryLeftOutputBit (4*k+3) T x) := by
  let h' : Int := -(4*(3*(k:Int)+2))
  let T1 := sweptLeft (4*(3*k+2)) T 0
  have hs : 0 < 3*k+2 := by omega
  have hb : 4*(3*k+2) ≤ 3*(4*k+3) := by omega
  have hon := carryInput_leftOnes (4*k+3) (3*k+2) T hmatch hb
  have hzero : T 1 = false := by
    exact carryInput_unmarked (4*k+3) T hmatch 1 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  have hleft0 := counted_left_sweep (4*(3*k+2)) T 0 hon hzero
  have hleft : run tm2 (3*(4*(3*k+2))) ⟨3,0,T⟩ =
      some ⟨3,h',T1⟩ := by
    simpa [h',T1,Int.zero_sub] using hleft0
  have hmatchB := carryBridge1_input_match k T hmatch
  have hbridge0 := carryBridge1 T1 h' hmatchB
  let T2 := (frame (fun x => carryBridgeArea1 (x-h')) T1
    (shiftConfig h' (embed carryBridgeFinal1))).tape
  have hbridge : run tm2 12 ⟨3,h',T1⟩ =
      some ⟨3,6+h',T2⟩ := by
    simpa [T2,frame,shiftConfig,embed,carryBridgeFinal1] using hbridge0
  have hseg0 : carrySegmentOnes T2 (h'+6) (3*(4*k)+7) := by
    apply frame_head_segment carryBridgeArea1 T1 (embed carryBridgeFinal1)
      h' 6 (3*(4*k)+7)
    · simp [carryBridgeArea1]
    · simp [embed,carryBridgeFinal1]
    · intro i hi
      simp [carryBridgeArea1]
      omega
    · intro i hi
      have hv := carryLeftSweep_marked (4*k+3) (3*k+2) T hmatch hs hb
        (h'+6+(i:Int)) (by omega) (by omega)
      simpa [T1] using hv
  have hseg : carrySegmentOnes T2 (6+h') (3*(4*k)+7) := by
    simpa [Int.add_comm] using hseg0
  have h5input : T 5 = false := by
    exact carryInput_unmarked (4*k+3) T hmatch 5 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  have h6input : T 6 = false := by
    exact carryInput_unmarked (4*k+3) T hmatch 6 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  have h5sweep : T1 5 = T 5 := by
    exact carryLeftSweep_preserves_at (4*k+3) (3*k+2) T hmatch hs hb 5
      (by omega) (by omega)
  have h6sweep : T1 6 = T 6 := by
    exact carryLeftSweep_preserves_at (4*k+3) (3*k+2) T hmatch hs hb 6
      (by omega) (by omega)
  have h5area : carryBridgeArea1 (5-h') = false := by
    simp [carryBridgeArea1,h']
    omega
  have h6area : carryBridgeArea1 (6-h') = false := by
    simp [carryBridgeArea1,h']
    omega
  have h5 : T2 5 = false := by
    simp [T2,frame,shiftConfig,h5area,h5sweep,h5input]
  have h6 : T2 6 = false := by
    simp [T2,frame,shiftConfig,h6area,h6sweep,h6input]
  let nR := 4*k
  have hfinish : (6+h')+3*(nR:Int) = -2 := by
    dsimp [h',nR]
    omega
  have hz0 : T2 ((6+h')+3*(nR:Int)+7) = false := by
    have heq : (6+h')+3*(nR:Int)+7 = 5 := by omega
    simpa [heq] using h5
  have hz1 : T2 ((6+h')+3*(nR:Int)+8) = false := by
    have heq : (6+h')+3*(nR:Int)+8 = 6 := by omega
    simpa [heq] using h6
  have hseed : ∀ x, x < 6+h' →
      T2 x = carryLeftOutputBit (4*k+3) T x := by
    intro x hx
    by_cases hfar : x < -3*(4*(k:Int)+3)-2
    · have ha : carryBridgeArea1 (x-h') = false := by
        simp [carryBridgeArea1,h']
        omega
      have hpres := carryLeftSweep_preserves_at (4*k+3) (3*k+2) T hmatch hs hb x
        (by omega) (by omega)
      simp [T2,T1,frame,shiftConfig,ha,hpres,carryLeftOutputBit,hfar,h']
    · have hcases : x-h' = -3 ∨ x-h' = -2 ∨ x-h' = -1 ∨
          x-h' = 0 ∨ x-h' = 1 ∨ x-h' = 2 ∨ x-h' = 3 ∨
          x-h' = 4 ∨ x-h' = 5 := by
        simp [h']
        omega
      rcases hcases with hi3 | hi2 | hi1 | hi0 | hi1p | hi2p |
          hi3p | hi4 | hi5
      · have hxEq : x = h'+(-3) := by omega
        have ha : carryBridgeArea1 ((h'+(-3))-h') = false := by
          simp [carryBridgeArea1]
          omega
        have hpres := carryLeftSweep_preserves_at (4*k+3) (3*k+2) T hmatch hs hb
          (h'+(-3)) (by omega) (by omega)
        have harea : carryInputArea (4*k+3) (h'+(-3)) = true := by
          simp [carryInputArea,h']
          omega
        have hbit : carryInputBit (4*k+3) (h'+(-3)) = true := by
          simp [carryInputBit,h']
          omega
        have hmark : T (h'+(-3)) = true := by
          rw [hmatch (h'+(-3)) harea]
          exact hbit
        have hleft : T2 (h'+(-3)) = true := by
          simp [T2,T1,frame,shiftConfig,ha,hpres,hmark,h']
        have hright : carryLeftOutputBit (4*k+3) T (h'+(-3)) = true := by
          simp [carryLeftOutputBit,h']
          omega
        simpa [hxEq] using hleft.trans hright.symm
      · have hxEq : x = h'+(-2) := by omega
        have hcase : T2 (h'+(-2)) =
            carryLeftOutputBit (4*k+3) T (h'+(-2)) := by
          simp [T2,frame,shiftConfig,carryBridgeArea1,embed,carryBridgeFinal1,
            carryLeftOutputBit,h'] <;> omega only [h']
        simpa [hxEq] using hcase
      · have hxEq : x = h'+(-1) := by omega
        have hcase : T2 (h'+(-1)) =
            carryLeftOutputBit (4*k+3) T (h'+(-1)) := by
          simp [T2,frame,shiftConfig,carryBridgeArea1,embed,carryBridgeFinal1,
            carryLeftOutputBit,h'] <;> omega only [h']
        simpa [hxEq] using hcase
      · have hxEq : x = h'+0 := by omega
        have hcase : T2 (h'+0) =
            carryLeftOutputBit (4*k+3) T (h'+0) := by
          simp [T2,frame,shiftConfig,carryBridgeArea1,embed,carryBridgeFinal1,
            carryLeftOutputBit,h'] <;> omega only [h']
        simpa [hxEq] using hcase
      · have hxEq : x = h'+1 := by omega
        have hcase : T2 (h'+1) =
            carryLeftOutputBit (4*k+3) T (h'+1) := by
          simp [T2,frame,shiftConfig,carryBridgeArea1,embed,carryBridgeFinal1,
            carryLeftOutputBit,h'] <;> omega only [h']
        simpa [hxEq] using hcase
      · have hxEq : x = h'+2 := by omega
        have hcase : T2 (h'+2) =
            carryLeftOutputBit (4*k+3) T (h'+2) := by
          simp [T2,frame,shiftConfig,carryBridgeArea1,embed,carryBridgeFinal1,
            carryLeftOutputBit,h'] <;> omega only [h']
        simpa [hxEq] using hcase
      · have hxEq : x = h'+3 := by omega
        have hcase : T2 (h'+3) =
            carryLeftOutputBit (4*k+3) T (h'+3) := by
          simp [T2,frame,shiftConfig,carryBridgeArea1,embed,carryBridgeFinal1,
            carryLeftOutputBit,h'] <;> omega only [h']
        simpa [hxEq] using hcase
      · have hxEq : x = h'+4 := by omega
        have hcase : T2 (h'+4) =
            carryLeftOutputBit (4*k+3) T (h'+4) := by
          simp [T2,frame,shiftConfig,carryBridgeArea1,embed,carryBridgeFinal1,
            carryLeftOutputBit,h'] <;> omega only [h']
        simpa [hxEq] using hcase
      · have hxEq : x = h'+5 := by omega
        have hcase : T2 (h'+5) =
            carryLeftOutputBit (4*k+3) T (h'+5) := by
          simp [T2,frame,shiftConfig,carryBridgeArea1,embed,carryBridgeFinal1,
            carryLeftOutputBit,h'] <;> omega only [h']
        simpa [hxEq] using hcase
  have htotal := carryFinishWithLeftPattern (4*k+3)
    (3*(4*(3*k+2))) 12 nR ⟨3,0,T⟩ ⟨3,h',T1⟩ T T2 (6+h')
    hleft hbridge (by dsimp [nR]; omega) hfinish hseg hz0 hz1 hseed
    (by dsimp [h']; omega) (by dsimp [h']; omega)
  exact htotal

#print axioms carryLongPrefix_r2_left
#print axioms carryLongPrefix_r3_left

end BB6Coverage.Agent24CarryLeftOutput
