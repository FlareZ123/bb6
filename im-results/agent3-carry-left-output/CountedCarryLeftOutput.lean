import CountedCarryPrefixGeneral

namespace BB6Coverage.Agent3CarryLeftOutput

open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent48Champion

/-- The head-facing left word after an even-counter carry prefix:
    d0^r ++ d1 ++ the untouched suffix. -/
def carryLeftOutputBit (r : Nat) (T : Int → Bool) (x : Int) : Bool :=
  if x < -3*(r:Int)-2 then T x
  else if x ≤ -3*(r:Int) then true
  else decide (x % 3 = 1)

/-- Once the bridge seed is established, the common right-sweep/D-tail
    finish writes the remaining d0 blocks.  The bridge head is congruent
    to 1 modulo 3, so its every-third-cell output is the canonical d0 word. -/
theorem carryFinishWithLeftPattern
    (r nL nB nR : Nat) (c0 c1 : Config)
    (T T2 : Int → Bool) (hB : Int)
    (hL : run tm2 nL c0 = some c1)
    (hBridge : run tm2 nB c1 = some ⟨3,hB,T2⟩)
    (hsteps : nL+nB+(3*nR+15) = 15+12*r)
    (hfinish : hB+3*(nR:Int) = -2)
    (hseg : carrySegmentOnes T2 hB (3*nR+7))
    (hz0 : T2 (hB+3*(nR:Int)+7) = false)
    (hz1 : T2 (hB+3*(nR:Int)+8) = false)
    (hseed : ∀ x, x < hB → T2 x = carryLeftOutputBit r T x)
    (hbound : -3*(r:Int)+1 ≤ hB)
    (hmod : hB % 3 = 1) :
    ∃ T' : Int → Bool,
      run tm2 (15+12*r) c0 = some ⟨4,7,T'⟩ ∧
      (∀ x, x ≤ 0 → T' x = carryLeftOutputBit r T x) := by
  rcases carryFinishFromD T2 hB nR hfinish hseg hz0 hz1 with
    ⟨Tout,hfinishRun,ho1,ho2,ho3,ho4,ho5,ho6,hout,hformula⟩
  have htotal := composeCarryRuns r nL nB nR
    c0 c1 ⟨3,hB,T2⟩ ⟨4,7,Tout⟩ hL hBridge hfinishRun hsteps
  refine ⟨Tout,htotal,?_⟩
  intro x hx
  rw [hformula x hx]
  by_cases hlt : x < hB
  · simp [hlt, hseed x hlt]
  · have hge : hB ≤ x := le_of_not_gt hlt
    have hgt : -3*(r:Int) < x := by omega
    have hmodEq : (x-hB) % 3 = 0 ↔ x % 3 = 1 := by omega only [hmod]
    have htarget : carryLeftOutputBit r T x = decide (x % 3 = 1) := by
      simp [carryLeftOutputBit, hgt]
      omega
    have hmodBool : decide ((x-hB) % 3 = 0) = decide (x % 3 = 1) := by
      exact congrArg decide hmodEq
    simp [hlt,hmodBool,htarget]

/-- Residue 0: the finite bridge seed is the terminal d1 block followed by
    three d0 marks; carryFinishFromD supplies all remaining d0 blocks. -/
theorem carryLongPrefix_r0_left (k : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea (4*k) x = true →
      T x = carryInputBit (4*k) x) (hk : 0 < k) :
    ∃ T' : Int → Bool,
      run tm2 (15+12*(4*k)) ⟨3,0,T⟩ = some ⟨4,7,T'⟩ ∧
      (∀ x, x ≤ 0 → T' x = carryLeftOutputBit (4*k) T x) := by
  let h' : Int := -(4*(3*(k:Int)))
  let T1 := sweptLeft (4*(3*k)) T 0
  have hs : 0 < 3*k := by omega
  have hb : 4*(3*k) ≤ 3*(4*k) := by omega
  have hon := carryInput_leftOnes (4*k) (3*k) T hmatch hb
  have hzero : T 1 = false := by
    exact carryInput_unmarked (4*k) T hmatch 1 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  have hleft0 := counted_left_sweep (4*(3*k)) T 0 hon hzero
  have hleft : run tm2 (3*(4*(3*k))) ⟨3,0,T⟩ =
      some ⟨3,h',T1⟩ := by
    simpa [h',T1,Int.zero_sub] using hleft0
  have hmatchB := carryBridge0_input_match k T hmatch hk
  have hbridge0 := carryBridge0 T1 h' hmatchB
  let T2 := (frame (fun x => carryBridgeArea0 (x-h')) T1
    (shiftConfig h' (embed carryBridgeFinal0))).tape
  have hbridge : run tm2 12 ⟨3,h',T1⟩ =
      some ⟨3,10+h',T2⟩ := by
    simpa [T2,frame,shiftConfig,embed,carryBridgeFinal0] using hbridge0
  have hseg0 : carrySegmentOnes T2 (h'+10) (3*(4*(k-1))+7) := by
    apply frame_head_segment carryBridgeArea0 T1 (embed carryBridgeFinal0)
      h' 10 (3*(4*(k-1))+7)
    · simp [carryBridgeArea0]
    · simp [embed,carryBridgeFinal0]
    · intro i hi
      simp [carryBridgeArea0]
      omega
    · intro i hi
      have hv := carryLeftSweep_marked (4*k) (3*k) T hmatch hs hb
        (h'+10+(i:Int)) (by omega) (by omega)
      simpa [T1] using hv
  have hseg : carrySegmentOnes T2 (10+h') (3*(4*(k-1))+7) := by
    simpa [Int.add_comm] using hseg0
  have h5input : T 5 = false := by
    exact carryInput_unmarked (4*k) T hmatch 5 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  have h6input : T 6 = false := by
    exact carryInput_unmarked (4*k) T hmatch 6 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  have h5sweep : T1 5 = T 5 := by
    exact carryLeftSweep_preserves_at (4*k) (3*k) T hmatch hs hb 5
      (by omega) (by omega)
  have h6sweep : T1 6 = T 6 := by
    exact carryLeftSweep_preserves_at (4*k) (3*k) T hmatch hs hb 6
      (by omega) (by omega)
  have h5area : carryBridgeArea0 (5-h') = false := by
    simp [carryBridgeArea0,h']
    omega
  have h6area : carryBridgeArea0 (6-h') = false := by
    simp [carryBridgeArea0,h']
    omega
  have h5 : T2 5 = false := by
    simp [T2,frame,shiftConfig,h5area,h5sweep,h5input]
  have h6 : T2 6 = false := by
    simp [T2,frame,shiftConfig,h6area,h6sweep,h6input]
  let nR := 4*(k-1)
  have hfinish : (10+h')+3*(nR:Int) = -2 := by
    dsimp [h',nR]
    omega
  have hz0 : T2 ((10+h')+3*(nR:Int)+7) = false := by
    have heq : (10+h')+3*(nR:Int)+7 = 5 := by omega
    simpa [heq] using h5
  have hz1 : T2 ((10+h')+3*(nR:Int)+8) = false := by
    have heq : (10+h')+3*(nR:Int)+8 = 6 := by omega
    simpa [heq] using h6
  have hseed : ∀ x, x < 10+h' →
      T2 x = carryLeftOutputBit (4*k) T x := by
    intro x hx
    by_cases hfar : x < -3*(4*(k:Int))-2
    · have ha : carryBridgeArea0 (x-h') = false := by
        simp [carryBridgeArea0,h']
        omega
      have hpres := carryLeftSweep_preserves_at (4*k) (3*k) T hmatch hs hb x
        (by omega) (by omega)
      simp [T2,T1,frame,shiftConfig,ha,hpres,carryLeftOutputBit,hfar]
    · let i : Int := x-h'
      have hi : i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2 ∨
          i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by
        dsimp [i,h']
        omega
      have hxEq : x = h'+i := by dsimp [i]; omega
      rcases hi with hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi
      · subst i
        rw [hxEq]
        have ha : carryBridgeArea0 ((h'+(-2))-h') = false := by
          simp [carryBridgeArea0]
        have hpres := carryLeftSweep_preserves_at (4*k) (3*k) T hmatch hs hb
          (h'+(-2)) (by omega) (by omega)
        have harea : carryInputArea (4*k) (h'+(-2)) = true := by
          simp [carryInputArea,h']
          omega
        have hbit : carryInputBit (4*k) (h'+(-2)) = true := by
          simp [carryInputBit,h']
          omega
        have hmark : T (h'+(-2)) = true := by
          rw [hmatch (h'+(-2)) harea]
          exact hbit
        simp [T2,T1,frame,shiftConfig,ha,hpres,carryLeftOutputBit,h',hmark]
      · subst i; rw [hxEq]
        simp [T2,frame,shiftConfig,carryBridgeArea0,embed,carryBridgeFinal0,
          carryLeftOutputBit,h'] <;> omega
      · subst i; rw [hxEq]
        simp [T2,frame,shiftConfig,carryBridgeArea0,embed,carryBridgeFinal0,
          carryLeftOutputBit,h'] <;> omega
      · subst i; rw [hxEq]
        simp [T2,frame,shiftConfig,carryBridgeArea0,embed,carryBridgeFinal0,
          carryLeftOutputBit,h'] <;> omega
      · subst i; rw [hxEq]
        simp [T2,frame,shiftConfig,carryBridgeArea0,embed,carryBridgeFinal0,
          carryLeftOutputBit,h'] <;> omega
      · subst i; rw [hxEq]
        simp [T2,frame,shiftConfig,carryBridgeArea0,embed,carryBridgeFinal0,
          carryLeftOutputBit,h'] <;> omega
      · subst i; rw [hxEq]
        simp [T2,frame,shiftConfig,carryBridgeArea0,embed,carryBridgeFinal0,
          carryLeftOutputBit,h'] <;> omega
      · subst i; rw [hxEq]
        simp [T2,frame,shiftConfig,carryBridgeArea0,embed,carryBridgeFinal0,
          carryLeftOutputBit,h'] <;> omega
      · subst i; rw [hxEq]
        simp [T2,frame,shiftConfig,carryBridgeArea0,embed,carryBridgeFinal0,
          carryLeftOutputBit,h'] <;> omega
      · subst i; rw [hxEq]
        simp [T2,frame,shiftConfig,carryBridgeArea0,embed,carryBridgeFinal0,
          carryLeftOutputBit,h'] <;> omega
      · subst i; rw [hxEq]
        simp [T2,frame,shiftConfig,carryBridgeArea0,embed,carryBridgeFinal0,
          carryLeftOutputBit,h'] <;> omega
      · subst i; rw [hxEq]
        simp [T2,frame,shiftConfig,carryBridgeArea0,embed,carryBridgeFinal0,
          carryLeftOutputBit,h'] <;> omega
  have htotal := carryFinishWithLeftPattern (4*k)
    (3*(4*(3*k))) 12 nR ⟨3,0,T⟩ ⟨3,h',T1⟩ T T2 (10+h')
    hleft hbridge (by dsimp [nR]; omega) hfinish hseg hz0 hz1 hseed
    (by dsimp [h']; omega) (by dsimp [h']; omega)
  exact htotal

end BB6Coverage.Agent3CarryLeftOutput
