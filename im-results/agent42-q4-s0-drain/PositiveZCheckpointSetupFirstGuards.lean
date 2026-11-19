import PositiveZCheckpointSetupBlanks
import PositiveZCheckpointSetupComposition
import Agent6Q4Prefix
import Lean.Elab.Tactic.Omega

/-!
# First two guards for the positive-z setup suffix

The two-scan prefix tape satisfies the B20 input frame and the following
(L+1)-triple rightOnes premise.  These are the first two fields of
Agent 48's SetupSuffixGuards structure.  The proof is entirely by exact
coordinate formulas for sweptLeft and the source S0 side encoding.
-/

namespace BB6Coverage.Agent42PositiveZSetupFirstGuards

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48PositiveZSetup
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent42PositiveZSetupBlanks

def setupPrefixAfterB8 (L A z : Nat) : Int → Bool :=
  (q4FrameAt
    (sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0)
    (-(3*A+1:Int)) setupB8Inside setupB8End).tape

/-- The two-scan tape is the second left sweep of the B8 output. -/
theorem setupPrefixAfterScans_eq (L A z : Nat) :
    setupPrefixAfterScans L A z =
      sweptLeft (3*L+5) (setupPrefixAfterB8 L A z)
        (-(3*A+3:Int)) := rfl

private theorem sweptLeft_shift_simple (n : Nat) (T : Int → Bool) (h x : Int) :
    sweptLeft (n+1) T h x =
      if x = h-(n:Int) then false
      else if h-(n:Int)+1 ≤ x ∧ x ≤ h+1 then true
      else T x := by
  induction n generalizing T h with
  | zero =>
      have hne : h ≠ h+1 := by omega
      have hne' : h+1 ≠ h := by omega
      by_cases hx0 : x = h
      · subst x
        simp [sweptLeft,holeThree,hne,hne']
      · by_cases hx1 : x = h+1
        · subst x
          simp [sweptLeft,holeThree,hne,hne']
        · have hcond : ¬ (h+1 ≤ x ∧ x ≤ h+1) := by
            intro hc
            have hxeq : x = h+1 := le_antisymm hc.2 hc.1
            exact hx1 hxeq
          simp [sweptLeft,holeThree,hx0,hx1,hne,hne',hcond]
  | succ n ih =>
      change sweptLeft (n+1) (holeThree T h) (h-1) x = _
      rw [ih (holeThree T h) (h-1)]
      have h1 : h-1-(n:Int) = h-(n+1:Int) := by omega
      have h3 : h-1+1 = h := by omega
      have hcast : (n+1:Int) = (n:Int)+1 := by omega
      rw [h1,h3,←hcast]
      have hlow1 : h-(n+1:Int)+1 ≤ h+1 := by omega
      have hlow0 : h-(n+1:Int)+1 ≤ h := by omega
      by_cases hx1 : x = h+1
      · subst x
        have hneq : h+1 ≠ h-(n+1:Int) := by omega
        simp [holeThree,hneq,hlow1]
      · by_cases hx0 : x = h
        · subst x
          have hneq : h ≠ h-(n+1:Int) := by omega
          simp [holeThree,hx1,hneq,hlow0] <;> omega
        · have hupper : x ≤ h ↔ x ≤ h+1 := by omega
          simp [holeThree,hx0,hx1,hupper]

/-- Exact pointwise formula for the final left sweep. -/
theorem sweptLeft_shift (n : Nat) (T : Int → Bool) (h x : Int) :
    sweptLeft (n+1) T h x =
      if x = h-(n+1:Int)+1 then false
      else if h-(n+1:Int)+2 ≤ x ∧ x ≤ h+1 then true
      else T x := by
  have hclear : h-(n+1:Int)+1 = h-(n:Int) := by omega
  have hlower : h-(n+1:Int)+2 = h-(n:Int)+1 := by omega
  rw [hclear,hlower]
  exact sweptLeft_shift_simple n T h x

/-- The second sweep's zero boundary and rightward block, in absolute
coordinates relative to the B20 head h=-(3*A+3*L+8). -/
theorem setupPrefixAfterScans_sweepCell
    (L A z : Nat) (x : Int) :
    setupPrefixAfterScans L A z x =
      if x = setupPrefixHead A L + 1 then false
      else if setupPrefixHead A L + 2 ≤ x ∧ x ≤ -(3*A+2:Int) then true
      else setupPrefixAfterB8 L A z x := by
  rw [setupPrefixAfterScans_eq]
  have h1 :
      (-(3*A+3:Int))-(3*L+5:Int)+1 =
        setupPrefixHead A L+1 := by
    simp [setupPrefixHead]
    omega
  have h2 :
      (-(3*A+3:Int))-(3*L+5:Int)+2 =
        setupPrefixHead A L+2 := by
    simp [setupPrefixHead]
    omega
  have h3 : (-(3*A+3:Int))+1 = -(3*A+2:Int) := by omega
  simpa [h1,h2,h3] using
    sweptLeft_shift (3*L+4) (setupPrefixAfterB8 L A z)
      (-(3*A+3:Int)) x

/-- Cells at or to the left of the final scan head are inherited from the
initial S0 tape: neither sweep nor B8 reaches them. -/
theorem setupPrefixAfterScans_left_preserves
    (L A z : Nat) (x : Int)
    (hx : x ≤ setupPrefixHead A L) :
    setupPrefixAfterScans L A z x =
      setupPrefixInputTape L A z x := by
  have hsecond :
      setupPrefixAfterScans L A z x =
        setupPrefixAfterB8 L A z x := by
    rw [setupPrefixAfterScans_eq]
    apply sweptLeft_preserves_before
    dsimp [setupPrefixHead] at hx
    omega
  have hb8 :
      setupPrefixAfterB8 L A z x =
        sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0 x := by
    unfold setupPrefixAfterB8
    rw [q4FrameAt_tape]
    have hnot : setupB8Inside (x-(-(3*A+1:Int))) = false := by
      simp [setupB8Inside]
      dsimp [setupPrefixHead] at hx
      omega
    simp [hnot]
  have hfirst :
      sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0 x =
        setupPrefixInputTape L A z x := by
    apply sweptLeft_preserves_before
    dsimp [setupPrefixHead] at hx
    omega
  rw [hsecond,hb8,hfirst]

def setupPrefixInputLeftFacing (L A : Nat) : List Bool :=
  d1pow A ++ markerWord 1 ++ d0 ++ d1pow L ++ lh

theorem setupPrefixInput_left_cell
    (L A z i : Nat) :
    setupPrefixInputTape L A z (-(i:Int)) =
      sideBit (setupPrefixInputLeftFacing L A) i := by
  have hcell := s0Config_left_cell
    (markerWord 1 ++ d0 ++ d1pow L ++ lh) A 0 z 0 i
  have hcoord : (0:Int)-(i:Int) = -(i:Int) := by omega
  rw [hcoord] at hcell
  have hleft :
      s0LeftFacing (markerWord 1 ++ d0 ++ d1pow L ++ lh) A 0 =
        setupPrefixInputLeftFacing L A := by
    simp [s0LeftFacing,binDec_zero,setupPrefixInputLeftFacing,
      List.append_assoc]
  rw [hleft] at hcell
  simpa [setupPrefixInputTape] using hcell

private theorem setupPrefixInput_leftFacing_length (L A : Nat) :
    (setupPrefixInputLeftFacing L A).length = 3*A+3*L+12 := by
  simp [setupPrefixInputLeftFacing,d1pow_length,markerWord,d0,lh,
    List.append_assoc]

private theorem setupPrefixInput_left_lh_cell
    (L A j : Nat) (hj : j < 6) :
    sideBit (setupPrefixInputLeftFacing L A) (3*A+3*L+6+j) =
      sideBit lh j := by
  have hprefix :
      (d1pow A ++ markerWord 1 ++ d0 ++ d1pow L).length =
        3*A+3*L+6 := by
    simp [d1pow_length,markerWord,d0,List.append_assoc]
  unfold setupPrefixInputLeftFacing
  rw [show d1pow A ++ markerWord 1 ++ d0 ++ d1pow L ++ lh =
      (d1pow A ++ markerWord 1 ++ d0 ++ d1pow L) ++ lh by
        simp [List.append_assoc]]
  rw [sideBit_append_right
    (d1pow A ++ markerWord 1 ++ d0 ++ d1pow L) lh
    (3*A+3*L+6+j) (by rw [hprefix]; omega)]
  rw [hprefix]
  omega

/-- The six cells at the far-left end of the initial S0 word. -/
theorem setupPrefixInput_left_tail_cells (L A z : Nat) :
    setupPrefixInputTape L A z (-(3*A+3*L+13:Int)) = false ∧
    setupPrefixInputTape L A z (-(3*A+3*L+12:Int)) = false ∧
    setupPrefixInputTape L A z (-(3*A+3*L+11:Int)) = true ∧
    setupPrefixInputTape L A z (-(3*A+3*L+10:Int)) = true ∧
    setupPrefixInputTape L A z (-(3*A+3*L+9:Int)) = true ∧
    setupPrefixInputTape L A z (-(3*A+3*L+8:Int)) = false := by
  have hlen := setupPrefixInput_leftFacing_length L A
  have h13 : setupPrefixInputTape L A z (-(3*A+3*L+13:Int)) = false := by
    rw [setupPrefixInput_left_cell]
    exact sideBit_ge_length _ _ (by rw [hlen]; omega)
  have h12 : setupPrefixInputTape L A z (-(3*A+3*L+12:Int)) = false := by
    rw [setupPrefixInput_left_cell]
    exact sideBit_ge_length _ _ (by rw [hlen]; omega)
  have h11 : setupPrefixInputTape L A z (-(3*A+3*L+11:Int)) = true := by
    rw [setupPrefixInput_left_cell]
    have hs := setupPrefixInput_left_lh_cell L A 5 (by omega)
    have hi : 3*A+3*L+11 = 3*A+3*L+6+5 := by omega
    rw [hi,hs]
    simp [lh,sideBit]
  have h10 : setupPrefixInputTape L A z (-(3*A+3*L+10:Int)) = true := by
    rw [setupPrefixInput_left_cell]
    have hs := setupPrefixInput_left_lh_cell L A 4 (by omega)
    have hi : 3*A+3*L+10 = 3*A+3*L+6+4 := by omega
    rw [hi,hs]
    simp [lh,sideBit]
  have h9 : setupPrefixInputTape L A z (-(3*A+3*L+9:Int)) = true := by
    rw [setupPrefixInput_left_cell]
    have hs := setupPrefixInput_left_lh_cell L A 3 (by omega)
    have hi : 3*A+3*L+9 = 3*A+3*L+6+3 := by omega
    rw [hi,hs]
    simp [lh,sideBit]
  have h8 : setupPrefixInputTape L A z (-(3*A+3*L+8:Int)) = false := by
    rw [setupPrefixInput_left_cell]
    have hs := setupPrefixInput_left_lh_cell L A 2 (by omega)
    have hi : 3*A+3*L+8 = 3*A+3*L+6+2 := by omega
    rw [hi,hs]
    simp [lh,sideBit]
  exact ⟨h13,h12,h11,h10,h9,h8⟩

/-- The B20 frame preserves every cell strictly to the right of h+3. -/
theorem setupB20Config_preserves_after
    (T : Int → Bool) (h x : Int) (hx : h+4 ≤ x) :
    (setupB20Config T h).tape x = T x := by
  rw [setupB20Config,q4FrameAt_tape]
  have hnot : setupB20Inside (x-h) = false := by
    simp [setupB20Inside]
    omega
  simp [hnot]

/-- The two-scan prefix satisfies the exact nine-cell B20 input guard. -/
theorem setupPrefixAfterScans_b20Input (L A z : Nat) :
    setupB20Input (setupPrefixAfterScans L A z)
      (setupPrefixHead A L) := by
  rcases setupPrefixInput_left_tail_cells L A z with
    ⟨h13,h12,h11,h10,h9,h8⟩
  let h : Int := setupPrefixHead A L
  have hp (x : Int) (hx : x ≤ h) :
      setupPrefixAfterScans L A z x = setupPrefixInputTape L A z x :=
    setupPrefixAfterScans_left_preserves L A z x hx
  unfold setupB20Input
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hp (h-5) (by omega)]
    simpa [h,setupPrefixHead] using h13
  · rw [hp (h-4) (by omega)]
    simpa [h,setupPrefixHead] using h12
  · rw [hp (h-3) (by omega)]
    simpa [h,setupPrefixHead] using h11
  · rw [hp (h-2) (by omega)]
    simpa [h,setupPrefixHead] using h10
  · rw [hp (h-1) (by omega)]
    simpa [h,setupPrefixHead] using h9
  · rw [hp h (by omega)]
    simpa [h,setupPrefixHead] using h8
  · rw [setupPrefixAfterScans_sweepCell]
    simp [h,setupPrefixHead]
  · rw [setupPrefixAfterScans_sweepCell]
    have hne : h+2 ≠ setupPrefixHead A L+1 := by dsimp [h]; omega
    have hbounds :
        setupPrefixHead A L+2 ≤ h+2 ∧
          h+2 ≤ -(3*A+2:Int) := by
      dsimp [h,setupPrefixHead]
      omega
    simp [hne,hbounds]
  · rw [setupPrefixAfterScans_sweepCell]
    have hne : h+3 ≠ setupPrefixHead A L+1 := by dsimp [h]; omega
    have hbounds :
        setupPrefixHead A L+2 ≤ h+3 ∧
          h+3 ≤ -(3*A+2:Int) := by
      dsimp [h,setupPrefixHead]
      omega
    simp [hne,hbounds]

/-- After B20, the L+1 rightward triples are all ones, so the counted
right sweep can start without any further tape assumptions. -/
theorem setupPrefixAfterScans_lRun (L A z : Nat) :
    rightOnes
      (setupB20Config (setupPrefixAfterScans L A z)
        (setupPrefixHead A L)).tape
      (setupPrefixHead A L+4) (L+1) := by
  intro i hi
  have hframe0 := setupB20Config_preserves_after
    (setupPrefixAfterScans L A z) (setupPrefixHead A L)
    (setupPrefixHead A L+4+3*(i:Int)) (by omega)
  have hframe1 := setupB20Config_preserves_after
    (setupPrefixAfterScans L A z) (setupPrefixHead A L)
    (setupPrefixHead A L+4+3*(i:Int)+1) (by omega)
  have hframe2 := setupB20Config_preserves_after
    (setupPrefixAfterScans L A z) (setupPrefixHead A L)
    (setupPrefixHead A L+4+3*(i:Int)+2) (by omega)
  have h0 :
      setupPrefixAfterScans L A z
        (setupPrefixHead A L+4+3*(i:Int)) = true := by
    rw [setupPrefixAfterScans_sweepCell]
    have hne : setupPrefixHead A L+4+3*(i:Int) ≠
        setupPrefixHead A L+1 := by omega
    have hbounds :
        setupPrefixHead A L+2 ≤ setupPrefixHead A L+4+3*(i:Int) ∧
          setupPrefixHead A L+4+3*(i:Int) ≤ -(3*A+2:Int) := by
      dsimp [setupPrefixHead]
      omega
    simp [hne,hbounds]
  have h1 :
      setupPrefixAfterScans L A z
        (setupPrefixHead A L+4+3*(i:Int)+1) = true := by
    rw [setupPrefixAfterScans_sweepCell]
    have hne : setupPrefixHead A L+4+3*(i:Int)+1 ≠
        setupPrefixHead A L+1 := by omega
    have hbounds :
        setupPrefixHead A L+2 ≤ setupPrefixHead A L+4+3*(i:Int)+1 ∧
          setupPrefixHead A L+4+3*(i:Int)+1 ≤ -(3*A+2:Int) := by
      dsimp [setupPrefixHead]
      omega
    simp [hne,hbounds]
  have h2 :
      setupPrefixAfterScans L A z
        (setupPrefixHead A L+4+3*(i:Int)+2) = true := by
    rw [setupPrefixAfterScans_sweepCell]
    have hne : setupPrefixHead A L+4+3*(i:Int)+2 ≠
        setupPrefixHead A L+1 := by omega
    have hbounds :
        setupPrefixHead A L+2 ≤ setupPrefixHead A L+4+3*(i:Int)+2 ∧
          setupPrefixHead A L+4+3*(i:Int)+2 ≤ -(3*A+2:Int) := by
      dsimp [setupPrefixHead]
      omega
    simp [hne,hbounds]
  constructor
  · rw [hframe0]
    exact h0
  constructor
  · rw [hframe1]
    exact h1
  · rw [hframe2]
    exact h2

#print axioms sweptLeft_shift
#print axioms setupPrefixAfterScans_b20Input
#print axioms setupPrefixAfterScans_lRun

end BB6Coverage.Agent42PositiveZSetupFirstGuards
