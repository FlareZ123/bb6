import CountedCarryPrefixGeneral
import FrameCellLemmas

namespace BB6Coverage.Agent42CarryLeftOutput

open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent42CarryLeftFrames

def carryLeftOutputBit (r : Nat) (T : Int → Bool) (x : Int) : Bool :=
  if x < -3*(r:Int)-2 then T x
  else if x ≤ -3*(r:Int) then true
  else decide (x % 3 = 1)

theorem carryIntModSub (x h : Int) (hh : h % 3 = 1) :
    (x-h) % 3 = 0 ↔ x % 3 = 1 := by omega

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
  · have hge : hB ≤ x := by omega
    have hfarFalse : ¬ x < -3*(r:Int)-2 := by omega
    have htermFalse : ¬ x ≤ -3*(r:Int) := by omega
    have hmodEq := carryIntModSub x hB hmod
    have htarget : carryLeftOutputBit r T x = decide (x % 3 = 1) := by
      simp [carryLeftOutputBit, hfarFalse, htermFalse]
    have hmodBool : decide ((x-hB) % 3 = 0) = decide (x % 3 = 1) := by
      simp [hmodEq]
    simp [hlt,hmodBool,htarget]

theorem carryLongPrefix_r1_left (k : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea (4*k+1) x = true →
      T x = carryInputBit (4*k+1) x) (hk : 0 < k) :
    ∃ T' : Int → Bool,
      run tm2 (15+12*(4*k+1)) ⟨3,0,T⟩ = some ⟨4,7,T'⟩ ∧
      (∀ x, x ≤ 0 → T' x = carryLeftOutputBit (4*k+1) T x) := by
  let h' : Int := -(4*(3*(k:Int)))
  let T1 := sweptLeft (4*(3*k)) T 0
  have hs : 0 < 3*k := by omega
  have hb : 4*(3*k) ≤ 3*(4*k+1) := by omega
  have hon := carryInput_leftOnes (4*k+1) (3*k) T hmatch hb
  have hzero : T 1 = false := by
    exact carryInput_unmarked (4*k+1) T hmatch 1 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  have hleft0 := counted_left_sweep (4*(3*k)) T 0 hon hzero
  have hleft : run tm2 (3*(4*(3*k))) ⟨3,0,T⟩ =
      some ⟨3,h',T1⟩ := by
    simpa [h',T1,Int.zero_sub] using hleft0
  have hmatchB := carryBridge3_input_match k T hmatch hk
  have hbridge0 := carryBridge3 T1 h' hmatchB
  let Tbridge := (frame (fun x => carryBridgeArea3 (x-h')) T1
    (shiftConfig h' (embed carryBridgeFinal3))).tape
  have hbridge : run tm2 12 ⟨3,h',T1⟩ =
      some ⟨0,h'-2,Tbridge⟩ := by
    simpa [Tbridge,frame,shiftConfig,embed,carryBridgeFinal3,Int.sub_eq_add_neg,Int.add_comm] using hbridge0
  have hRight : ∀ i : Int, 2 ≤ i → i ≤ 10 → T1 (h'+i) = true := by
    intro i hlo hhi
    have hv := carryLeftSweep_marked (4*k+1) (3*k) T hmatch hs hb
      (h'+i) (by omega) (by omega)
    simpa [T1] using hv
  have hADmatch := carryBridge3_matches_carryAD12 T1 h' hRight
  have hk1 : (k-1)+1=k := by omega
  have hA := carryAD12 Tbridge (h'-2) hADmatch
  let hB : Int := 12+(h'-2)
  let T2 := (frame (fun x => carryAD12Area (x-(h'-2))) Tbridge
    (shiftConfig (h'-2) (embed carryAD12Final))).tape
  have hARun : run tm2 12 ⟨0,h'-2,Tbridge⟩ =
      some ⟨3,hB,T2⟩ := by
    simpa [hB,T2,frame,shiftConfig,embed,carryAD12Final] using hA
  have hseg0 : carrySegmentOnes T2 ((h'-2)+12) (3*(4*(k-1))+7) := by
    apply frame_head_segment carryAD12Area Tbridge (embed carryAD12Final)
      (h'-2) 12 (3*(4*(k-1))+7)
    · simp [carryAD12Area]
    · simp [embed,carryAD12Final]
    · intro i hi
      simp [carryAD12Area]
      omega
    · intro i hi
      let x : Int := (h'-2)+12+(i:Int)
      have harea : carryBridgeArea3 (x-h') = false := by
        simp [carryBridgeArea3,x,h']
        omega
      have hbridgeOutside : Tbridge x = T1 x := by
        simp [Tbridge,frame,shiftConfig,harea]
      have hleftMarked : T1 x = true := by
        have hxlo : 2-4*(3*(k:Int)) ≤ x := by dsimp [x,h']; omega
        have hxhi : x ≤ 4 := by dsimp [x,h']; omega
        have hv := carryLeftSweep_marked (4*k+1) (3*k) T hmatch hs hb x hxlo hxhi
        simpa [T1,x] using hv
      simpa [x] using hbridgeOutside.trans hleftMarked
  have hseg : carrySegmentOnes T2 hB (3*(4*(k-1))+7) := by
    simpa [hB,Int.add_comm] using hseg0
  have h5input : T 5 = false := by
    exact carryInput_unmarked (4*k+1) T hmatch 5 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  have h6input : T 6 = false := by
    exact carryInput_unmarked (4*k+1) T hmatch 6 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  have h5sweep : T1 5 = T 5 := by
    exact carryLeftSweep_preserves_at (4*k+1) (3*k) T hmatch hs hb 5
      (by omega) (by omega)
  have h6sweep : T1 6 = T 6 := by
    exact carryLeftSweep_preserves_at (4*k+1) (3*k) T hmatch hs hb 6
      (by omega) (by omega)
  have h5bridgeArea : carryBridgeArea3 (5-h') = false := by
    simp [carryBridgeArea3,h']
    omega
  have h6bridgeArea : carryBridgeArea3 (6-h') = false := by
    simp [carryBridgeArea3,h']
    omega
  have h5bridge : Tbridge 5 = T1 5 := by
    simp [Tbridge,frame,shiftConfig,h5bridgeArea]
  have h6bridge : Tbridge 6 = T1 6 := by
    simp [Tbridge,frame,shiftConfig,h6bridgeArea]
  have h5ADArea : carryAD12Area (5-(h'-2)) = false := by
    simp [carryAD12Area,h']
    omega
  have h6ADArea : carryAD12Area (6-(h'-2)) = false := by
    simp [carryAD12Area,h']
    omega
  have h5 : T2 5 = false := by
    simp [T2,frame,shiftConfig,h5ADArea,h5bridge,h5sweep,h5input]
  have h6 : T2 6 = false := by
    simp [T2,frame,shiftConfig,h6ADArea,h6bridge,h6sweep,h6input]
  let nR := 4*(k-1)
  have hfinish : hB+3*(nR:Int) = -2 := by
    dsimp [hB,h',nR]
    omega
  have hz0 : T2 (hB+3*(nR:Int)+7) = false := by
    have heq : hB+3*(nR:Int)+7 = 5 := by omega
    simpa [heq] using h5
  have hz1 : T2 (hB+3*(nR:Int)+8) = false := by
    have heq : hB+3*(nR:Int)+8 = 6 := by omega
    simpa [heq] using h6

  have hthreshold : -3*((4*k+1:Nat):Int)-2 = h'-5 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [h']
    omega
  have hthreshold' : -3*((4*k+1:Nat):Int) = h'-3 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [h']
    omega
  have ad12Seed (x : Int) (hlo : h'-2 ≤ x) (hhi : x ≤ h'+9) :
      T2 x = carryLeftOutputBit (4*k+1) T x := by
    have hi : 0 ≤ x-(h'-2) ∧ x-(h'-2) ≤ 12 := by omega
    have harea : carryAD12Area (x-(h'-2)) = true := by
      simp [carryAD12Area]
      omega
    have hT2 : T2 x = (embed carryAD12Final).tape (x-(h'-2)) := by
      simp [T2,frame,shiftConfig,harea]
    have hcell := ad12FinalCell_mod (x-(h'-2)) hi
    have hh : h' % 3 = 0 := by
      simp [h']
    have hmod := ad12Offset_mod h' x hh
    have htarget : carryLeftOutputBit (4*k+1) T x =
        decide (x % 3 = 1) := by
      simp [carryLeftOutputBit,hthreshold,hthreshold']
      omega
    rw [hT2,hcell]
    simpa [hmod,htarget]

  have hB_eq : hB = h'+10 := by
    dsimp [hB]
    omega
  have hseed : ∀ x, x < hB → T2 x = carryLeftOutputBit (4*k+1) T x := by
    intro x hx
    by_cases hfar : x < h'-5
    · have hbridgeArea : carryBridgeArea3 (x-h') = false := by
        simp [carryBridgeArea3]
        omega
      have hADArea : carryAD12Area (x-(h'-2)) = false := by
        simp [carryAD12Area]
        omega
      have hfar' : x < -(4*(3*(k:Int)))-5 := by
        simpa [h'] using hfar
      have hpres : T1 x = T x :=
        carryLeftSweep_preserves_at (4*k+1) (3*k) T hmatch hs hb x
          (by omega) (by omega)
      simp [T2,Tbridge,frame,shiftConfig,hADArea,hbridgeArea,hpres,
        carryLeftOutputBit,hthreshold,hfar]
    · by_cases hspecial : x = h'-5
      · subst x
        have hpres : T1 (h'-5) = T (h'-5) :=
          carryLeftSweep_preserves_at (4*k+1) (3*k) T hmatch hs hb (h'-5)
            (by dsimp [h']; omega) (by dsimp [h']; omega)
        have hinputArea : carryInputArea (4*k+1) (h'-5) = true := by
          simp [carryInputArea,h']
          omega
        have hinputBit : carryInputBit (4*k+1) (h'-5) = true := by
          simp [carryInputBit,h']
          omega
        have hmark : T (h'-5) = true := by
          rw [hmatch (h'-5) hinputArea]
          exact hinputBit
        have hbridgeArea : carryBridgeArea3 ((h'-5)-h') = false := by
          simp [carryBridgeArea3]
          omega
        have hADArea : carryAD12Area ((h'-5)-(h'-2)) = false := by
          simp [carryAD12Area]
          omega
        have hT1 : T1 (h'-5) = true := by
          rw [hpres,hmark]
        have hT2 : T2 (h'-5) = true := by
          simp [T2,Tbridge,frame,shiftConfig,hADArea,hbridgeArea,hT1]
        have htarget : carryLeftOutputBit (4*k+1) T (h'-5) = true := by
          simp [carryLeftOutputBit,hthreshold,hthreshold']
        exact hT2.trans htarget.symm
      · by_cases hbridge4 : x = h'-4
        · subst x
          have hbridgeArea : carryBridgeArea3 ((h'-4)-h') = true := by
            simp [carryBridgeArea3]
            omega
          have hADArea : carryAD12Area ((h'-4)-(h'-2)) = false := by
            simp [carryAD12Area]
            omega
          have hbridgeCell : (embed carryBridgeFinal3).tape (-4) = true :=
            bridge3FinalCell_left (-4) (Or.inl rfl)
          have hT2 : T2 (h'-4) = true := by
            simp [T2,Tbridge,frame,shiftConfig,hADArea,hbridgeArea,hbridgeCell]
          have htarget : carryLeftOutputBit (4*k+1) T (h'-4) = true := by
            simp [carryLeftOutputBit,hthreshold,hthreshold']
          exact hT2.trans htarget.symm
        · by_cases hbridge3 : x = h'-3
          · subst x
            have hbridgeArea : carryBridgeArea3 ((h'-3)-h') = true := by
              simp [carryBridgeArea3]
              omega
            have hADArea : carryAD12Area ((h'-3)-(h'-2)) = false := by
              simp [carryAD12Area]
              omega
            have hbridgeCell : (embed carryBridgeFinal3).tape (-3) = true :=
              bridge3FinalCell_left (-3) (Or.inr rfl)
            have hT2 : T2 (h'-3) = true := by
              simp [T2,Tbridge,frame,shiftConfig,hADArea,hbridgeArea,hbridgeCell]
            have htarget : carryLeftOutputBit (4*k+1) T (h'-3) = true := by
              simp [carryLeftOutputBit,hthreshold,hthreshold']
            exact hT2.trans htarget.symm
          · have hlo : h'-2 ≤ x := by omega
            have hhi : x ≤ h'+9 := by
              have hxB : x < h'+10 := by rw [hB_eq] at hx; exact hx
              omega
            have hmid := ad12Seed x hlo hhi
            exact hmid

  have hbridgeAD := run_compose tm2 12 12
    ⟨3,h',T1⟩ ⟨0,h'-2,Tbridge⟩ ⟨3,hB,T2⟩ hbridge hARun
  have hsteps : 3*(4*(3*k)) + 24 + (3*nR+15) = 15+12*(4*k+1) := by
    dsimp [nR]
    omega
  have hbound : -3*((4*k+1:Nat):Int)+1 ≤ hB := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [hB,h']
    omega
  have hmod : hB % 3 = 1 := by
    dsimp [hB,h']
    omega
  exact carryFinishWithLeftPattern (4*k+1) (3*(4*(3*k))) 24 nR
    ⟨3,0,T⟩ ⟨3,h',T1⟩ T T2 hB
    hleft hbridgeAD hsteps hfinish hseg hz0 hz1 hseed hbound hmod

#print axioms carryIntModSub
#print axioms carryFinishWithLeftPattern
#print axioms carryLongPrefix_r1_left

end BB6Coverage.Agent42CarryLeftOutput
