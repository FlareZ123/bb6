import PositiveZCheckpointSetupFirstGuards
import PositiveZCheckpointSetupComposition
import Agent6Q4Prefix
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent42PositiveZSetupAllGuards

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48PositiveZSetup
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent42PositiveZSetupBlanks
open BB6Coverage.Agent42PositiveZSetupFirstGuards

theorem setupPrefixInput_right_cell (L A z i : Nat) :
    setupPrefixInputTape L A z (1+(i:Int)) =
      sideBit (s0RightFacing z) i := by
  have hcell := s0Config_right_cell
    (markerWord 1 ++ d0 ++ d1pow L ++ lh) A 0 z 0 i
  have hcoord : (0:Int)+1+(i:Int) = 1+(i:Int) := by omega
  rw [hcoord] at hcell
  simpa [setupPrefixInputTape] using hcell

theorem setupPrefixInput_right_d1pow_cell
    (L A z i : Nat) (hi : i < 3*(z+1)) :
    setupPrefixInputTape L A z (7+(i:Int)) = true := by
  rw [setupPrefixInput_right_cell]
  have hside :
      sideBit (s0RightFacing z) (6+i) =
        sideBit (d1pow (z+1)) i := by
    rw [s0RightFacing]
    rw [sideBit_append_right [false,true,true,true,false,false]
      (d1pow (z+1)) (6+i) (by simp)]
    simp
  rw [hside]
  exact BB6Coverage.Agent6Q4Prefix.sideBit_d1pow_true (z+1) i hi

theorem setupPrefixInput_right_cells (L A z : Nat) :
    setupPrefixInputTape L A z 2 = true ∧
    setupPrefixInputTape L A z 3 = true ∧
    setupPrefixInputTape L A z 4 = true ∧
    setupPrefixInputTape L A z 5 = false ∧
    setupPrefixInputTape L A z 6 = false ∧
    setupPrefixInputTape L A z 7 = true ∧
    setupPrefixInputTape L A z 8 = true := by
  have h2 := setupPrefixInput_right_cell L A z 1
  have h3 := setupPrefixInput_right_cell L A z 2
  have h4 := setupPrefixInput_right_cell L A z 3
  have h5 := setupPrefixInput_right_cell L A z 4
  have h6 := setupPrefixInput_right_cell L A z 5
  have h7 := setupPrefixInput_right_d1pow_cell L A z 0 (by omega)
  have h8 := setupPrefixInput_right_d1pow_cell L A z 1 (by omega)
  constructor
  · simpa [s0RightFacing,sideBit] using h2
  constructor
  · simpa [s0RightFacing,sideBit] using h3
  constructor
  · simpa [s0RightFacing,sideBit] using h4
  constructor
  · simpa [s0RightFacing,sideBit] using h5
  constructor
  · simpa [s0RightFacing,sideBit] using h6
  constructor
  · simpa [show 7 = 7+0 by omega] using h7
  · simpa [show 8 = 7+1 by omega] using h8

theorem setupPrefixAfterScans_right_preserves_input
    (L A z : Nat) (x : Int) (hx : 2 ≤ x) :
    setupPrefixAfterScans L A z x = setupPrefixInputTape L A z x := by
  rw [setupPrefixAfterScans_eq]
  have hsecond :
      sweptLeft (3*L+5) (setupPrefixAfterB8 L A z)
        (-(3*A+3:Int)) x = setupPrefixAfterB8 L A z x :=
    sweptLeft_preserves_after (3*L+5) _ (-(3*A+3:Int)) x (by omega)
  rw [hsecond]
  unfold setupPrefixAfterB8
  rw [q4FrameAt_tape]
  have hnot : setupB8Inside (x-(-(3*A+1:Int))) = false := by
    simp [setupB8Inside]
    omega
  simp [hnot]
  exact sweptLeft_preserves_after (3*A+1)
    (setupPrefixInputTape L A z) 0 x (by omega)

theorem setupPrefixAfterScans_firstSweepOnes
    (L A z : Nat) (x : Int)
    (hlo : -(3*A:Int)+1 ≤ x) (hhi : x ≤ 1) :
    setupPrefixAfterScans L A z x = true := by
  rw [setupPrefixAfterScans_eq]
  have hsecond :
      sweptLeft (3*L+5) (setupPrefixAfterB8 L A z)
        (-(3*A+3:Int)) x = setupPrefixAfterB8 L A z x :=
    sweptLeft_preserves_after (3*L+5) _ (-(3*A+3:Int)) x (by omega)
  rw [hsecond]
  unfold setupPrefixAfterB8
  rw [q4FrameAt_tape]
  have hnot : setupB8Inside (x-(-(3*A+1:Int))) = false := by
    simp [setupB8Inside]
    omega
  simp [hnot]
  have hfirst := sweptLeft_shift (3*A)
    (setupPrefixInputTape L A z) 0 x
  have hne : x ≠ -(3*A:Int) := by omega
  have hbounds : -(3*A:Int)+1 ≤ x ∧ x ≤ 1 := ⟨hlo,hhi⟩
  simpa [hne,hbounds] using hfirst

theorem setupPrefixAfterScans_at_B9Head (L A z : Nat) :
    setupPrefixAfterScans L A z (-(3*A+1:Int)) = true := by
  rw [setupPrefixAfterScans_eq]
  have hsecond :
      sweptLeft (3*L+5) (setupPrefixAfterB8 L A z)
        (-(3*A+3:Int)) (-(3*A+1:Int)) =
      setupPrefixAfterB8 L A z (-(3*A+1:Int)) :=
    sweptLeft_preserves_after (3*L+5) _ (-(3*A+3:Int))
      (-(3*A+1:Int)) (by omega)
  rw [hsecond]
  unfold setupPrefixAfterB8
  rw [q4FrameAt_tape]
  simp [setupB8Inside,setupB8End]

theorem setupPrefixAfterScans_at_B9Head_plus_one (L A z : Nat) :
    setupPrefixAfterScans L A z (-(3*A:Int)) = false := by
  rw [setupPrefixAfterScans_eq]
  have hsecond :
      sweptLeft (3*L+5) (setupPrefixAfterB8 L A z)
        (-(3*A+3:Int)) (-(3*A:Int)) =
      setupPrefixAfterB8 L A z (-(3*A:Int)) :=
    sweptLeft_preserves_after (3*L+5) _ (-(3*A+3:Int))
      (-(3*A:Int)) (by omega)
  rw [hsecond]
  unfold setupPrefixAfterB8
  rw [q4FrameAt_tape]
  have hnot : setupB8Inside ((-(3*A:Int))-(-(3*A+1:Int))) = false := by
    simp [setupB8Inside]
  simp [hnot]
  have hfirst := sweptLeft_shift (3*A)
    (setupPrefixInputTape L A z) 0 (-(3*A:Int))
  have hclear : (-(3*A:Int)) = (0:Int)-(3*A:Int)+1 := by omega
  simpa [hclear] using hfirst

theorem setupPrefixAfterScans_at_B9Head_plus_two (L A z : Nat) :
    setupPrefixAfterScans L A z (-(3*A:Int)+1) = true := by
  exact setupPrefixAfterScans_firstSweepOnes L A z
    (-(3*A:Int)+1) (by omega) (by omega)

theorem setupB9Config_preserves_after
    (T : Int → Bool) (h : Int) (L : Nat) (x : Int)
    (hx : h+10+3*(L:Int) ≤ x) :
    (setupB9Config T h L).tape x = T x := by
  have hL :
      (setupLConfig T h L).tape x = T x := by
    unfold setupLConfig
    rw [sweptRight_preserves_after (L+1)
      (setupB20Config T h).tape (h+4) x (by omega)]
    exact setupB20Config_preserves_after T h x (by omega)
  unfold setupB9Config
  rw [q4FrameAt_tape]
  have hnot :
      setupB9Inside (x-(h+7+3*(L:Int))) = false := by
    simp [setupB9Inside]
    omega
  simp [hnot]
  exact hL

theorem setupPrefixAfterScans_b9Input (L A z : Nat) :
    setupB9Input
      (setupLConfig (setupPrefixAfterScans L A z)
        (setupPrefixHead A L) L).tape
      (setupPrefixHead A L+7+3*(L:Int)) := by
  let h : Int := setupPrefixHead A L
  let T : Int → Bool := setupPrefixAfterScans L A z
  let h9 : Int := h+7+3*(L:Int)
  have h9eq : h9 = -(3*A+1:Int) := by
    dsimp [h,setupPrefixHead,h9]
    omega
  have hclear2 :
      (setupLConfig T h L).tape (h9-2) = false := by
    have heq : h9-2 = h+4+3*(L:Int)+1 := by dsimp [h9]; omega
    change sweptRight (L+1) (setupB20Config T h).tape
      (h+4) (h9-2) = false
    rw [heq]
    exact sweptRight_clears_second (L+1)
      (setupB20Config T h).tape (h+4) L (by omega)
  have hclear3 :
      (setupLConfig T h L).tape (h9-1) = false := by
    have heq : h9-1 = h+4+3*(L:Int)+2 := by dsimp [h9]; omega
    change sweptRight (L+1) (setupB20Config T h).tape
      (h+4) (h9-1) = false
    rw [heq]
    exact sweptRight_clears_third (L+1)
      (setupB20Config T h).tape (h+4) L (by omega)
  have hpres (x : Int) (hx : h9 ≤ x) :
      (setupLConfig T h L).tape x = T x := by
    unfold setupLConfig
    rw [sweptRight_preserves_after (L+1)
      (setupB20Config T h).tape (h+4) x (by dsimp [h9] at hx; omega)]
    exact setupB20Config_preserves_after T h x (by omega)
  unfold setupB9Input
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [h9] using hclear2
  · simpa [h9] using hclear3
  · rw [hpres h9 (by omega), h9eq]
    exact setupPrefixAfterScans_at_B9Head L A z
  · rw [hpres (h9+1) (by omega), h9eq]
    simpa using setupPrefixAfterScans_at_B9Head_plus_one L A z
  · rw [hpres (h9+2) (by omega), h9eq]
    simpa using setupPrefixAfterScans_at_B9Head_plus_two L A z

theorem setupPrefixAfterScans_aRun (L A z : Nat) :
    rightOnes
      (setupB9Config (setupPrefixAfterScans L A z)
        (setupPrefixHead A L) L).tape
      (setupPrefixHead A L+10+3*(L:Int)) (A+1) := by
  let h : Int := setupPrefixHead A L
  let T : Int → Bool := setupPrefixAfterScans L A z
  let start : Int := h+10+3*(L:Int)
  have hstart : start = -(3*A:Int)+2 := by
    dsimp [h,start,setupPrefixHead]
    omega
  intro i hi
  have hcell (j : Nat) (hj : j ≤ 2) :
      (setupB9Config T h L).tape (start+3*(i:Int)+(j:Int)) = true := by
    have hpres := setupB9Config_preserves_after T h L
      (start+3*(i:Int)+(j:Int)) (by dsimp [start]; omega)
    rw [hpres]
    by_cases hiA : i = A
    · subst i
      have heq : start+3*(A:Int)+(j:Int) = 2+(j:Int) := by
        dsimp [start,h,setupPrefixHead]
        omega
      rw [heq]
      have hinput := setupPrefixAfterScans_right_preserves_input L A z
        (2+(j:Int)) (by omega)
      rw [hinput]
      have hsmall := setupPrefixInput_right_cells L A z
      rcases hsmall with ⟨h2,h3,h4,_,_,_,_⟩
      interval_cases j <;> simp_all
    · have hiLt : i < A := by omega
      have hlo :
          -(3*A:Int)+1 ≤ start+3*(i:Int)+(j:Int) := by
        rw [hstart]
        omega
      have hhi :
          start+3*(i:Int)+(j:Int) ≤ 1 := by
        rw [hstart]
        omega
      exact setupPrefixAfterScans_firstSweepOnes L A z
        (start+3*(i:Int)+(j:Int)) hlo hhi
  constructor
  · exact hcell 0 (by omega)
  constructor
  · exact hcell 1 (by omega)
  · exact hcell 2 (by omega)

theorem setupPrefixAfterScans_b6Input (L A z : Nat) :
    setupB6Input
      (setupAConfig (setupPrefixAfterScans L A z)
        (setupPrefixHead A L) L A).tape
      (setupPrefixHead A L+13+3*(L:Int)+3*(A:Int)) := by
  let h : Int := setupPrefixHead A L
  let T : Int → Bool := setupPrefixAfterScans L A z
  let start : Int := h+10+3*(L:Int)
  let h6 : Int := h+13+3*(L:Int)+3*(A:Int)
  have h6eq : h6 = 5 := by
    dsimp [h,h6,setupPrefixHead]
    omega
  have hthird :
      sweptRight (A+1) (setupB9Config T h L).tape start
        (start+3*(A:Int)+2) = false :=
    sweptRight_clears_third (A+1) (setupB9Config T h L).tape
      start A (by omega)
  have hpres (x : Int) (hx : h6 ≤ x) :
      (setupAConfig T h L A).tape x = T x := by
    unfold setupAConfig
    rw [sweptRight_preserves_after (A+1)
      (setupB9Config T h L).tape start x (by dsimp [h6] at hx; omega)]
    exact setupB9Config_preserves_after T h L x (by dsimp [start] at hx; omega)
  have hsmall := setupPrefixInput_right_cells L A z
  rcases hsmall with ⟨h2,h3,h4,h5,h6v,h7,h8⟩
  unfold setupB6Input
  refine ⟨?_,?_,?_,?_,?_⟩
  · have heq : h6-1 = start+3*(A:Int)+2 := by
      dsimp [h6,start,h,setupPrefixHead]
      omega
    change sweptRight (A+1) (setupB9Config T h L).tape
      start (h6-1) = false
    rw [heq]
    exact hthird
  · rw [hpres h6 (by omega), h6eq]
    rw [setupPrefixAfterScans_right_preserves_input L A z 5 (by omega)]
    exact h5
  · rw [hpres (h6+1) (by omega), h6eq]
    rw [setupPrefixAfterScans_right_preserves_input L A z 6 (by omega)]
    exact h6v
  · rw [hpres (h6+2) (by omega), h6eq]
    rw [setupPrefixAfterScans_right_preserves_input L A z 7 (by omega)]
    exact h7
  · rw [hpres (h6+3) (by omega), h6eq]
    rw [setupPrefixAfterScans_right_preserves_input L A z 8 (by omega)]
    exact h8

theorem setupB6Config_preserves_after
    (T : Int → Bool) (h : Int) (L A : Nat) (x : Int)
    (hx : h+17+3*(L:Int)+3*(A:Int) ≤ x) :
    (setupB6Config T h L A).tape x = T x := by
  have hA :
      (setupAConfig T h L A).tape x = T x := by
    unfold setupAConfig
    rw [sweptRight_preserves_after (A+1)
      (setupB9Config T h L).tape (h+10+3*(L:Int)) x (by omega)]
    exact setupB9Config_preserves_after T h L x (by omega)
  unfold setupB6Config
  rw [q4FrameAt_tape]
  have hnot :
      setupB6Inside
        (x-(h+13+3*(L:Int)+3*(A:Int))) = false := by
    simp [setupB6Inside]
    omega
  simp [hnot]
  exact hA

theorem setupPrefixAfterScans_zRun (L A z : Nat) :
    rightOnes
      (setupB6Config (setupPrefixAfterScans L A z)
        (setupPrefixHead A L) L A).tape
      (setupPrefixHead A L+17+3*(L:Int)+3*(A:Int)) z := by
  let h : Int := setupPrefixHead A L
  let T : Int → Bool := setupPrefixAfterScans L A z
  let start : Int := h+17+3*(L:Int)+3*(A:Int)
  have hstart : start = 9 := by
    dsimp [h,start,setupPrefixHead]
    omega
  intro i hi
  have hcell (j : Nat) (hj : j ≤ 2) :
      (setupB6Config T h L A).tape (start+3*(i:Int)+(j:Int)) = true := by
    have hpres := setupB6Config_preserves_after T h L A
      (start+3*(i:Int)+(j:Int)) (by dsimp [start]; omega)
    rw [hpres]
    have hinput := setupPrefixAfterScans_right_preserves_input L A z
      (start+3*(i:Int)+(j:Int)) (by dsimp [start]; omega)
    rw [hinput]
    have hindex :
        start+3*(i:Int)+(j:Int) =
          7+(2+3*i+j:Int) := by
      rw [hstart]
      omega
    rw [hindex]
    exact setupPrefixInput_right_d1pow_cell L A z (2+3*i+j) (by omega)
  constructor
  · exact hcell 0 (by omega)
  constructor
  · exact hcell 1 (by omega)
  · exact hcell 2 (by omega)

theorem setupPrefixAfterScans_guards (L A z : Nat) (hz : 0 < z) :
    SetupSuffixGuards (setupPrefixAfterScans L A z)
      (setupPrefixHead A L) A L z := by
  refine ⟨
    setupPrefixAfterScans_b20Input L A z,
    setupPrefixAfterScans_lRun L A z,
    setupPrefixAfterScans_b9Input L A z,
    setupPrefixAfterScans_aRun L A z,
    setupPrefixAfterScans_b6Input L A z,
    setupPrefixAfterScans_zRun L A z,
    ?_⟩
  let h : Int := setupPrefixHead A L
  let T : Int → Bool := setupPrefixAfterScans L A z
  let start : Int := h+17+3*(L:Int)+3*(A:Int)
  let h30 : Int := start+3*(z:Int)
  have hstart : start = 9 := by
    dsimp [h,start,setupPrefixHead]
    omega
  have h30eq : h30 = 3*z+9 := by
    dsimp [h30]
    rw [hstart]
    omega
  have hB6false8 :
      (setupB6Config T h L A).tape 8 = false := by
    unfold setupB6Config
    rw [q4FrameAt_tape]
    have hrel :
        (8:Int)-(h+13+3*(L:Int)+3*(A:Int)) = 3 := by
      dsimp [h,setupPrefixHead]
      omega
    rw [hrel]
    simp [setupB6Inside,setupB6End]
  have hsourceLast :
      (setupB6Config T h L A).tape h30 = true := by
    rw [setupB6Config_preserves_after T h L A h30 (by rw [h30eq]; omega)]
    rw [setupPrefixAfterScans_right_preserves_input L A z h30 (by rw [h30eq]; omega)]
    rw [h30eq]
    have hidx : 3*z+9 = 7+(3*z+2:Int) := by omega
    rw [hidx]
    exact setupPrefixInput_right_d1pow_cell L A z (3*z+2) (by omega)
  have hsourceBlank (x : Int) (hx : h30 < x) :
      (setupB6Config T h L A).tape x = false := by
    rw [setupB6Config_preserves_after T h L A x
      (by rw [h30eq] at hx; rw [hstart]; omega)]
    have hblank :
        SetupPrefixRightBlank T (setupPrefixHead A L) A L z :=
      setupPrefixAfterScans_rightBlank L A z
    apply hblank
    dsimp [h30,h,start,setupPrefixHead] at hx ⊢
    omega
  have hZpres (x : Int) (hx : h30 ≤ x) :
      (setupZConfig T h L A z).tape x =
        (setupB6Config T h L A).tape x := by
    unfold setupZConfig
    rw [sweptRight_preserves_after z
      (setupB6Config T h L A).tape start x (by dsimp [h30] at hx; exact hx)]
  have hlast : z-1 < z := by omega
  have hlastStart :
      h30-3 = start+3*((z-1):Int) := by
    dsimp [h30]
    omega
  have hlastSecond :
      h30-2 = start+3*((z-1):Int)+1 := by
    dsimp [h30]
    omega
  have hlastThird :
      h30-1 = start+3*((z-1):Int)+2 := by
    dsimp [h30]
    omega
  have hlastTrue :
      (setupB6Config T h L A).tape (start+3*((z-1):Int)) = true := by
    have hr := setupPrefixAfterScans_zRun L A z (z-1) hlast
    exact hr.1
  have hlastStartTrue :
      (setupZConfig T h L A z).tape (h30-3) = true := by
    rw [hZpres (h30-3) (by omega), hlastStart]
    rw [sweptRight_preserves_block_start z
      (setupB6Config T h L A).tape start (z-1) hlast]
    exact hlastTrue
  have hlastSecondFalse :
      (setupZConfig T h L A z).tape (h30-2) = false := by
    rw [hlastSecond]
    exact sweptRight_clears_second z
      (setupB6Config T h L A).tape start (z-1) hlast
  have hlastThirdFalse :
      (setupZConfig T h L A z).tape (h30-1) = false := by
    rw [hlastThird]
    exact sweptRight_clears_third z
      (setupB6Config T h L A).tape start (z-1) hlast
  have hlastMinusFourFalse :
      (setupZConfig T h L A z).tape (h30-4) = false := by
    by_cases hz1 : z = 1
    · subst z
      have hbefore : h30-4 < start := by
        rw [h30eq,hstart]
        omega
      have hpres := sweptRight_preserves_before 1
        (setupB6Config T h L A).tape start (h30-4) hbefore
      rw [hZpres (h30-4) (by rw [h30eq]; omega)] at hpres
      simpa [h30eq] using hpres.trans hB6false8
    · have hz2 : 2 ≤ z := by omega
      have hi : z-2 < z := by omega
      have heq : h30-4 = start+3*((z-2):Int)+2 := by
        dsimp [h30]
        omega
      rw [heq]
      exact sweptRight_clears_third z
        (setupB6Config T h L A).tape start (z-2) hi
  have hheadTrue :
      (setupZConfig T h L A z).tape h30 = true := by
    rw [hZpres h30 (by omega)]
    exact hsourceLast
  have hblank1 :
      (setupZConfig T h L A z).tape (h30+1) = false := by
    rw [hZpres (h30+1) (by omega)]
    exact hsourceBlank (h30+1) (by omega)
  have hblank2 :
      (setupZConfig T h L A z).tape (h30+2) = false := by
    rw [hZpres (h30+2) (by omega)]
    exact hsourceBlank (h30+2) (by omega)
  have hblank3 :
      (setupZConfig T h L A z).tape (h30+3) = false := by
    rw [hZpres (h30+3) (by omega)]
    exact hsourceBlank (h30+3) (by omega)
  have hblank4 :
      (setupZConfig T h L A z).tape (h30+4) = false := by
    rw [hZpres (h30+4) (by omega)]
    exact hsourceBlank (h30+4) (by omega)
  have hblank5 :
      (setupZConfig T h L A z).tape (h30+5) = false := by
    rw [hZpres (h30+5) (by omega)]
    exact hsourceBlank (h30+5) (by omega)
  unfold setupB30Input
  rw [h30eq]
  exact ⟨
    by simpa [h30eq] using hlastMinusFourFalse,
    by simpa [h30eq] using hlastStartTrue,
    by simpa [h30eq] using hlastSecondFalse,
    by simpa [h30eq] using hlastThirdFalse,
    by simpa [h30eq] using hheadTrue,
    by simpa [h30eq] using hblank1,
    by simpa [h30eq] using hblank2,
    by simpa [h30eq] using hblank3,
    by simpa [h30eq] using hblank4,
    by simpa [h30eq] using hblank5⟩

#print axioms setupPrefixAfterScans_guards

end BB6Coverage.Agent42PositiveZSetupAllGuards
