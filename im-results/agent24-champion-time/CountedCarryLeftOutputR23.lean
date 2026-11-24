import CountedCarryLeftOutput
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent24CarryLeftOutput

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent3CarryLeftOutput
open BB6Coverage.Agent42CarryLeftFrames

set_option maxHeartbeats 3000000

private theorem carryLeftOutputBit_bridge2
    (r : Nat) (T : Int → Bool) (h x : Int)
    (hrel : h = -3*(r:Int)+2)
    (hnot : ¬ x < -3*(r:Int)-2) :
    carryLeftOutputBit r T x =
      (if x ≤ h-2 then true else decide (x % 3 = 1)) := by
  have hbound : -3*(r:Int) = h-2 := by rw [hrel]; omega
  have hnot' : ¬ x < h-2-2 := by simpa [hbound] using hnot
  simp [carryLeftOutputBit, hbound, hnot']

private theorem carryLeftOutputBit_bridge1
    (r : Nat) (T : Int → Bool) (h x : Int)
    (hh : h % 3 = 1)
    (hrel : h = -3*(r:Int)+1)
    (hnot : ¬ x < -3*(r:Int)-2) :
    carryLeftOutputBit r T x =
      (if x ≤ h then true else decide (x % 3 = 1)) := by
  by_cases hle : x ≤ -3*(r:Int)
  · have hle' : x ≤ h := by rw [hrel]; omega
    simp [carryLeftOutputBit,hnot,hle,hle']
  · by_cases hx : x ≤ h
    · have hxEq : x = h := by
        rw [hrel] at hx
        omega
      subst x
      have hfar : ¬ (-3*(r:Int)+1 < -3*(r:Int)-2) := by omega
      have hleft : ¬ (-3*(r:Int)+1 ≤ -3*(r:Int)) := by omega
      have hmod : (-3*(r:Int)+1) % 3 = 1 := by simpa [hrel] using hh
      simp [carryLeftOutputBit, hrel, hfar, hleft, hmod]
    · simp [carryLeftOutputBit,hnot,hle,hx]

/-- Residue 2: the bridge seed is the three-cell terminal d1 block
followed by the d0 stream. The common right sweep supplies the rest. -/
theorem carryLongPrefix_r2_left (k : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea (4*k+2) x = true →
      T x = carryInputBit (4*k+2) x) :
    ∃ T' : Int → Bool,
      run tm2 (15+12*(4*k+2)) ⟨3,0,T⟩ = some ⟨4,7,T'⟩ ∧
      T' 1 = true ∧ T' 2 = true ∧ T' 3 = true ∧
      T' 4 = true ∧ T' 5 = false ∧ T' 6 = true ∧
      (∀ x, 6 < x → T' x = T x) ∧
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
  have hthreshold : h' = -3*(4*k+2:Int)+2 := by
    dsimp [h']
    omega
  have hmod' : h' % 3 = 2 := by
    rw [hthreshold]
    omega
  have hseed : ∀ x, x < 2+h' →
      T2 x = carryLeftOutputBit (4*k+2) T x := by
    intro x hx
    by_cases hfar : x < -3*(4*(k:Int)+2)-2
    · have ha : carryBridgeArea2 (x-h') = false := by
        have hnot : ¬ (-3 ≤ x-h') := by
          rw [hthreshold]
          omega
        simp [carryBridgeArea2,hnot]
      have hpres := carryLeftSweep_preserves_at (4*k+2) (3*k+1) T hmatch hs hb x
        (by omega) (by omega)
      have hframe : T2 x = T1 x := by
        simp [T2,frame,shiftConfig,ha]
      calc
        T2 x = T1 x := hframe
        _ = T x := by simpa [T1] using hpres
        _ = carryLeftOutputBit (4*k+2) T x := by
          simp [carryLeftOutputBit,hfar]
    · by_cases hEdge : x-h' = -4
      · have hxEq : x = h'+(-4) := by omega
        have ha : carryBridgeArea2 (x-h') = false := by
          simp [carryBridgeArea2,hEdge]
        have hpres := carryLeftSweep_preserves_at (4*k+2) (3*k+1) T hmatch hs hb x
          (by omega) (by omega)
        have hlow : -(3*(4*k+2:Int))-2 ≤ x := by
          rw [hxEq,hthreshold]
          omega
        have hupper : x ≤ 6 := by
          rw [hxEq,hthreshold]
          omega
        have harea : carryInputArea (4*k+2) x = true := by
          simp [carryInputArea,hlow,hupper]
        have hbit : carryInputBit (4*k+2) x = true := by
          rw [hxEq,hthreshold]
          simp [carryInputBit] <;> omega
        have hmark : T x = true := by
          rw [hmatch x harea]
          exact hbit
        have hframe : T2 x = T1 x := by
          simp [T2,frame,shiftConfig,ha]
        have hxval : x = -3*(4*k+2:Int)-2 := by
          rw [hxEq, hthreshold]
          omega
        have hle : -3*(4*k+2:Int)-2 ≤ -3*(4*k+2:Int) := by omega
        have htarget : carryLeftOutputBit (4*k+2) T x = true := by
          simp [carryLeftOutputBit, hxval, hle]
        calc
          T2 x = T1 x := hframe
          _ = T x := by simpa [T1] using hpres
          _ = true := hmark
          _ = carryLeftOutputBit (4*k+2) T x := htarget.symm
      · have hinside : -3 ≤ x-h' ∧ x-h' ≤ 2 := by
          have hge : -(3*(4*k+2:Int))-2 ≤ x := by omega
          omega
        have hframe : T2 x =
            (if x ≤ h'-2 then true else decide (x % 3 = 1)) := by
          simpa [T2] using bridge2FrameOutput T1 h' x hmod' hinside
        have hnot : ¬ x < -3*(4*k+2:Int)-2 := by omega
        have htarget := carryLeftOutputBit_bridge2
          (4*k+2) T h' x hthreshold hnot
        exact hframe.trans htarget.symm
  have hbound : -3*((4*k+2:Int))+1 ≤ 2+h' := by
    dsimp [h']
    omega
  have hmod : (2+h') % 3 = 1 := by
    dsimp [h']
    omega
  rcases carryFinishFromD T2 (2+h') nR hfinish hseg hz0 hz1 with
    ⟨Tout,hfinishRun,ho1,ho2,ho3,ho4,ho5,ho6,hout,hformula⟩
  have htotal := composeCarryRuns (4*k+2) (3*(4*(3*k+1))) 12 nR
    ⟨3,0,T⟩ ⟨3,h',T1⟩ ⟨3,2+h',T2⟩ ⟨4,7,Tout⟩
    hleft hbridge hfinishRun (by dsimp [nR]; omega)
  have hT2out : ∀ x, 6 < x → T2 x = T x := by
    intro x hx
    have ha : carryBridgeArea2 (x-h') = false := by
      simp [carryBridgeArea2,h']
      omega
    have hleftout : T1 x = T x :=
      carryLeftSweep_rightOutside (4*k+2) (3*k+1) T hmatch hs hb x hx
    simp [T2,frame,shiftConfig,ha,hleftout]
  have hout' : ∀ x, 6 < x → Tout x = T x := by
    intro x hx
    rw [hout x hx]
    exact hT2out x hx
  have hleft' : ∀ x, x ≤ 0 → Tout x = carryLeftOutputBit (4*k+2) T x := by
    intro x hx
    rw [hformula x hx]
    by_cases hlt : x < 2+h'
    · simp [hlt,hseed x hlt]
    · have hge : 2+h' ≤ x := by omega
      have hfarFalse : ¬ x < -3*((4*k+2:Int))-2 := by omega
      have htermFalse : ¬ x ≤ -3*((4*k+2:Int)) := by omega
      have hmodEq := carryIntModSub x (2+h') hmod
      have htarget : carryLeftOutputBit (4*k+2) T x =
          decide (x % 3 = 1) := by
        simp [carryLeftOutputBit,hfarFalse,htermFalse]
      have hmodBool : decide ((x-(2+h')) % 3 = 0) =
          decide (x % 3 = 1) := by
        simp [hmodEq]
      simp [hlt,hmodBool,htarget]
  exact ⟨Tout,htotal,ho1,ho2,ho3,ho4,ho5,ho6,hout',hleft'⟩

/-- Residue 3: the bridge seed is the terminal d1 block followed by
the d0 stream. The common right sweep supplies the rest. -/
theorem carryLongPrefix_r3_left (k : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea (4*k+3) x = true →
      T x = carryInputBit (4*k+3) x) :
    ∃ T' : Int → Bool,
      run tm2 (15+12*(4*k+3)) ⟨3,0,T⟩ = some ⟨4,7,T'⟩ ∧
      T' 1 = true ∧ T' 2 = true ∧ T' 3 = true ∧
      T' 4 = true ∧ T' 5 = false ∧ T' 6 = true ∧
      (∀ x, 6 < x → T' x = T x) ∧
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
  have hthreshold : h' = -3*(4*k+3:Int)+1 := by
    dsimp [h']
    omega
  have hmod' : h' % 3 = 1 := by
    rw [hthreshold]
    omega
  have hseed : ∀ x, x < 6+h' →
      T2 x = carryLeftOutputBit (4*k+3) T x := by
    intro x hx
    by_cases hfar : x < -3*(4*(k:Int)+3)-2
    · have ha : carryBridgeArea1 (x-h') = false := by
        have hnot : ¬ (-2 ≤ x-h') := by
          rw [hthreshold]
          omega
        simp [carryBridgeArea1,hnot]
      have hpres := carryLeftSweep_preserves_at (4*k+3) (3*k+2) T hmatch hs hb x
        (by omega) (by omega)
      have hframe : T2 x = T1 x := by
        simp [T2,frame,shiftConfig,ha]
      calc
        T2 x = T1 x := hframe
        _ = T x := by simpa [T1] using hpres
        _ = carryLeftOutputBit (4*k+3) T x := by
          simp [carryLeftOutputBit,hfar]
    · by_cases hEdge : x-h' = -3
      · have hxEq : x = h'+(-3) := by omega
        have ha : carryBridgeArea1 (x-h') = false := by
          simp [carryBridgeArea1,hEdge]
        have hpres := carryLeftSweep_preserves_at (4*k+3) (3*k+2) T hmatch hs hb x
          (by omega) (by omega)
        have hlow : -(3*(4*k+3:Int))-2 ≤ x := by
          rw [hxEq,hthreshold]
          omega
        have hupper : x ≤ 6 := by
          rw [hxEq,hthreshold]
          omega
        have harea : carryInputArea (4*k+3) x = true := by
          simp [carryInputArea,hlow,hupper]
        have hbit : carryInputBit (4*k+3) x = true := by
          rw [hxEq,hthreshold]
          simp [carryInputBit] <;> omega
        have hmark : T x = true := by
          rw [hmatch x harea]
          exact hbit
        have hframe : T2 x = T1 x := by
          simp [T2,frame,shiftConfig,ha]
        have hxval : x = -3*(4*k+3:Int)-2 := by
          rw [hxEq, hthreshold]
          omega
        have hle : -3*(4*k+3:Int)-2 ≤ -3*(4*k+3:Int) := by omega
        have htarget : carryLeftOutputBit (4*k+3) T x = true := by
          simp [carryLeftOutputBit, hxval, hle]
        calc
          T2 x = T1 x := hframe
          _ = T x := by simpa [T1] using hpres
          _ = true := hmark
          _ = carryLeftOutputBit (4*k+3) T x := htarget.symm
      · have hinside : -2 ≤ x-h' ∧ x-h' ≤ 6 := by
          have hge : -(3*(4*k+3:Int))-2 ≤ x := by omega
          omega
        have hframe : T2 x =
            (if x ≤ h' then true else decide (x % 3 = 1)) := by
          simpa [T2] using bridge1FrameOutput T1 h' x hmod' hinside
        have hnot : ¬ x < -3*(4*k+3:Int)-2 := by omega
        have htarget := carryLeftOutputBit_bridge1
          (4*k+3) T h' x hmod' hthreshold hnot
        exact hframe.trans htarget.symm
  have hbound : -3*((4*k+3:Int))+1 ≤ 6+h' := by
    dsimp [h']
    omega
  have hmod : (6+h') % 3 = 1 := by
    dsimp [h']
    omega
  rcases carryFinishFromD T2 (6+h') nR hfinish hseg hz0 hz1 with
    ⟨Tout,hfinishRun,ho1,ho2,ho3,ho4,ho5,ho6,hout,hformula⟩
  have htotal := composeCarryRuns (4*k+3) (3*(4*(3*k+2))) 12 nR
    ⟨3,0,T⟩ ⟨3,h',T1⟩ ⟨3,6+h',T2⟩ ⟨4,7,Tout⟩
    hleft hbridge hfinishRun (by dsimp [nR]; omega)
  have hT2out : ∀ x, 6 < x → T2 x = T x := by
    intro x hx
    have ha : carryBridgeArea1 (x-h') = false := by
      simp [carryBridgeArea1,h']
      omega
    have hleftout : T1 x = T x :=
      carryLeftSweep_rightOutside (4*k+3) (3*k+2) T hmatch hs hb x hx
    simp [T2,frame,shiftConfig,ha,hleftout]
  have hout' : ∀ x, 6 < x → Tout x = T x := by
    intro x hx
    rw [hout x hx]
    exact hT2out x hx
  have hleft' : ∀ x, x ≤ 0 → Tout x = carryLeftOutputBit (4*k+3) T x := by
    intro x hx
    rw [hformula x hx]
    by_cases hlt : x < 6+h'
    · simp [hlt,hseed x hlt]
    · have hge : 6+h' ≤ x := by omega
      have hfarFalse : ¬ x < -3*((4*k+3:Int))-2 := by omega
      have htermFalse : ¬ x ≤ -3*((4*k+3:Int)) := by omega
      have hmodEq := carryIntModSub x (6+h') hmod
      have htarget : carryLeftOutputBit (4*k+3) T x =
          decide (x % 3 = 1) := by
        simp [carryLeftOutputBit,hfarFalse,htermFalse]
      have hmodBool : decide ((x-(6+h')) % 3 = 0) =
          decide (x % 3 = 1) := by
        simp [hmodEq]
      simp [hlt,hmodBool,htarget]
  exact ⟨Tout,htotal,ho1,ho2,ho3,ho4,ho5,ho6,hout',hleft'⟩

#print axioms carryLongPrefix_r2_left
#print axioms carryLongPrefix_r3_left

/-! Diagnostic provenance for the transitive axiom gate. These declarations
are the only imported theorem families used by the two new residue bridges. -/
#print axioms carryInput_leftOnes
#print axioms carryInput_unmarked
#print axioms counted_left_sweep
#print axioms carryBridge2
#print axioms carryBridge1
#print axioms carryLeftSweep_closed
#print axioms carryLeftSweep_marked
#print axioms carryLeftSweep_preserves_at
#print axioms carryLeftSweep_rightOutside
#print axioms frame_head_segment
#print axioms carryFinishFromD
#print axioms composeCarryRuns
#print axioms bridge2FrameOutput
#print axioms bridge1FrameOutput
#print axioms carryLongPrefix_r0_left

end BB6Coverage.Agent24CarryLeftOutput
