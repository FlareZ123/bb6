import PositiveZCheckpointSetupRootPrefix
import PositiveZCheckpointSetupAllGuards
import Lean.Elab.Tactic.Omega

/-!
# Exact positive-z S0-to-S0 source macro

The root-prefix theorem supplies the original-source first sweep, B8, and
second sweep. The existing suffix theorem supplies B20, the counted right
sweeps, B9/B6/B30, and the exact final configuration. This file identifies
that final configuration as another source S0 configuration.
-/

namespace BB6Coverage.Agent48PositiveZSetupRootCycle

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48PositiveZSetup
open BB6Coverage.Agent42PositiveZSetupBlanks
open BB6Coverage.Agent42PositiveZSetupAllGuards
open BB6Coverage.Agent48PositiveZSetupRootPrefix

set_option maxHeartbeats 4000000

private theorem binDec_allOnes (k : Nat) :
    binDec k (2^k-1) = d0pow k := by
  induction k with
  | zero => simp [binDec,d0pow]
  | succ k ih =>
      have hpow : 2^(k+1)-1 = 2*(2^k-1)+1 := by
        rw [Nat.pow_succ]
        have hp : 0 < 2^k := Nat.pow_pos (by decide)
        omega
      have hlt : 2^k-1 < 2^k := by
        exact Nat.sub_lt (Nat.pow_pos (by decide)) (by decide)
      rw [hpow,binDec_odd k (2^k-1) hlt]
      simp [d0pow,ih]

private theorem setupConfig_ext {c d : Config}
    (hs : c.state = d.state) (hh : c.head = d.head)
    (ht : c.tape = d.tape) : c = d := by
  cases c
  cases d
  simp_all

/-- The suffix's final frame is exactly an S0 encoding with the
counter word d0^z and the fixed setup right word. -/
theorem setupB30Config_as_s0Config
    (T : Int → Bool) (h : Int) (A L z : Nat)
    (g : SetupSuffixGuards T h A L z) (hz : 2≤z)
    (htail : SetupB6LeftTail T h A L)
    (hblank : SetupPrefixRightBlank T h A L z) :
    setupB30Config T h L A z =
      s0Config (setupL2 A L) z (2^z-1) 0
        (h+3*((A+L+z:Int))+13) := by
  let H : Int := h+3*((A+L+z:Int))+13
  have hhead : (setupB30Config T h L A z).head = H := by
    rw [setupB30Config_head]
    dsimp [H]
    omega
  have hcoordB30 :
      h+13+3*(L:Int)+3*(A:Int)+3*(z:Int) = H := by
    dsimp [H]
    omega
  have hstate :
      (setupB30Config T h L A z).state =
        (s0Config (setupL2 A L) z (2^z-1) 0 H).state := by
    simp [setupB30Config,q4FrameAt,q4Frame,shiftConfig,embed,
      setupB30End,s0Config]
  have hwordLeft :
      s0LeftFacing (setupL2 A L) z (2^z-1) =
        d0pow z ++ setupL2 A L := by
    simp [s0LeftFacing,binDec_allOnes]
  have hwordRight : setupRightWord = s0RightFacing 0 := by
    simp [setupRightWord,s0RightFacing,d1pow,d1]
  have htape :
      (setupB30Config T h L A z).tape =
        (s0Config (setupL2 A L) z (2^z-1) 0 H).tape := by
    funext x
    by_cases hx : x ≤ H
    · let i : Nat := Int.toNat (H-x)
      have hi : (i:Int) = H-x := by
        dsimp [i]
        exact Int.toNat_of_nonneg (by omega)
      have hcoord : H-(i:Int) = x := by omega
      have hleft := setupB30Config_leftFacing T h A L z g hz htail i
      have hs0 := s0Config_left_cell (setupL2 A L) z (2^z-1) 0 H i
      rw [hcoordB30] at hleft
      rw [hcoord] at hleft
      rw [hcoord] at hs0
      rw [hs0,hwordLeft]
      exact hleft
    · let i : Nat := Int.toNat (x-H-1)
      have hi : (i:Int) = x-H-1 := by
        dsimp [i]
        exact Int.toNat_of_nonneg (by omega)
      have hcoord : H+1+(i:Int) = x := by omega
      have hright := setupB30Config_rightFacing T h A L z hblank i
      have hs0 := s0Config_right_cell (setupL2 A L) z (2^z-1) 0 H i
      rw [hcoordB30] at hright
      rw [hcoord] at hright
      rw [hcoord] at hs0
      rw [hs0,hwordRight]
      exact hright
  exact setupConfig_ext hstate hhead htape

/-- A source-exact S0-to-S0 macro for every z≥2. The cost is the
complete original-machine itinerary, not merely the setup suffix. -/
theorem positiveZSetupRootS0Cycle (L A z : Nat) (hz : 2≤z) :
    run tm2 (12*A+12*L+3*z+97)
      (s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) A 0 z 0) =
      some (s0Config (setupL2 A L) z (2^z-1) 0 (3*z+5)) := by
  let T := setupPrefixAfterScans L A z
  let h := setupPrefixHead A L
  have g : SetupSuffixGuards T h A L z :=
    setupPrefixAfterScans_guards L A z (by omega)
  have hleftBlank : SetupPrefixLeftBlank T h :=
    setupPrefixAfterScans_leftBlank L A z
  have hrightBlank : SetupPrefixRightBlank T h A L z :=
    setupPrefixAfterScans_rightBlank L A z
  have htail : SetupB6LeftTail T h A L :=
    setupB6LeftTail_of_guards_and_blank T h A L z g hleftBlank
  have hprefix := positiveZSetupPrefix_run L A z
  have hsuffix := positiveZSetupSuffix_run T h A L z g
  have houtput := setupB30Config_as_s0Config T h A L z g hz htail hrightBlank
  have hcost :
      (3*(3*A+1)+8+3*(3*L+5)) +
        (20+3*(L+1)+9+3*(A+1)+6+3*z+30) =
      12*A+12*L+3*z+97 := by omega
  have hrun := run_append_some hprefix hsuffix
  rw [← hcost]
  rw [houtput] at hrun
  have hfinal : h+3*((A+L+z:Int))+13 = (3*z+5:Int) := by
    dsimp [h,setupPrefixHead]
    omega
  rw [hfinal] at hrun
  simpa [T,h] using hrun

#print axioms setupB30Config_as_s0Config
#print axioms positiveZSetupRootS0Cycle

end BB6Coverage.Agent48PositiveZSetupRootCycle
