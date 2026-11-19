import PositiveZCheckpointSetupBridges
import CountedSweep

/-!
# Compositional source theorem for the positive-z setup suffix

This module composes the five finite bridge lemmas with the three
parameterized rightward sweeps. The remaining S0-specific obligation is
to prove SetupSuffixGuards for the tape produced by the two left scans,
then identify the final tape with the target S0 encoder.
-/

namespace BB6Coverage.Agent48PositiveZSetup

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48Q4S0Macros

set_option maxHeartbeats 4000000

theorem run_append_some {n m : Nat} {c d e : Config}
    (h₁ : run tm2 n c = some d)
    (h₂ : run tm2 m d = some e) :
    run tm2 (n+m) c = some e := by
  simpa [run_append, h₁] using h₂

/-- State-3 configuration immediately after the 20-step B20 bridge. -/
def setupB20Config (T : Int → Bool) (h : Int) : Config :=
  q4FrameAt T h setupB20Inside setupB20End

/-- State-3 configuration after sweeping z rightward triples. -/
def setupZConfig (T : Int → Bool) (h : Int) (z : Nat) : Config :=
  ⟨3, h+4+3*(z:Int),
    sweptRight z (setupB20Config T h).tape (h+4)⟩

/-- State-3 configuration immediately after the 9-step B9 bridge. -/
def setupB9Config (T : Int → Bool) (h : Int) (z : Nat) : Config :=
  q4FrameAt (setupZConfig T h z).tape
    (h+7+3*(z:Int)) setupB9Inside setupB9End

/-- State-3 configuration after sweeping A+1 rightward triples. -/
def setupAConfig (T : Int → Bool) (h : Int) (z A : Nat) : Config :=
  ⟨3, h+10+3*(z:Int)+3*(A:Int),
    sweptRight (A+1) (setupB9Config T h z).tape
      (h+7+3*(z:Int))⟩

/-- State-3 configuration immediately after the 6-step B6 bridge. -/
def setupB6Config (T : Int → Bool) (h : Int) (z A : Nat) : Config :=
  q4FrameAt (setupAConfig T h z A).tape
    (h+14+3*(z:Int)+3*(A:Int)) setupB6Inside setupB6End

/-- State-3 configuration after sweeping L+1 rightward triples. -/
def setupLConfig (T : Int → Bool) (h : Int) (z A L : Nat) : Config :=
  ⟨3, h+17+3*(z:Int)+3*(A:Int)+3*(L:Int),
    sweptRight (L+1) (setupB6Config T h z A).tape
      (h+14+3*(z:Int)+3*(A:Int))⟩

/-- Final state-3 configuration after the 30-step B30 return bridge. -/
def setupB30Config (T : Int → Bool) (h : Int) (z A L : Nat) : Config :=
  q4FrameAt (setupLConfig T h z A L).tape
    (h+17+3*(z:Int)+3*(A:Int)+3*(L:Int))
    setupB30Inside setupB30End

/-- The exact local and unary-block guards needed to compose the suffix.
The later S0-specific proof should establish these from the output of the
two left-one scans. -/
structure SetupSuffixGuards (T : Int → Bool) (h : Int)
    (A L z : Nat) : Prop where
  b20 : setupB20Input T h
  zRun : rightOnes (setupB20Config T h).tape (h+4) z
  b9 : setupB9Input (setupZConfig T h z).tape
    (h+4+3*(z:Int))
  aRun : rightOnes (setupB9Config T h z).tape
    (h+7+3*(z:Int)) (A+1)
  b6 : setupB6Input (setupAConfig T h z A).tape
    (h+10+3*(z:Int)+3*(A:Int))
  lRun : rightOnes (setupB6Config T h z A).tape
    (h+14+3*(z:Int)+3*(A:Int)) (L+1)
  b30 : setupB30Input (setupLConfig T h z A L).tape
    (h+17+3*(z:Int)+3*(A:Int)+3*(L:Int))

/-- Exact suffix run: B20, right sweep z, B9, right sweep A+1,
B6, right sweep L+1, and B30. -/
theorem positiveZSetupSuffix_run (T : Int → Bool) (h : Int)
    (A L z : Nat) (g : SetupSuffixGuards T h A L z) :
    run tm2
      (20+3*z+9+3*(A+1)+6+3*(L+1)+30)
      ⟨3,h,T⟩ =
      some (setupB30Config T h z A L) := by
  have h20 : run tm2 20 ⟨3,h,T⟩ =
      some (setupB20Config T h) := by
    simpa [setupB20Config] using setupB20_at T h g.b20
  have hz : run tm2 (3*z) (setupB20Config T h) =
      some (setupZConfig T h z) := by
    simpa [setupZConfig, setupB20Config] using
      counted_right_sweep z (setupB20Config T h).tape (h+4) g.zRun
  have h9 : run tm2 9 (setupZConfig T h z) =
      some (setupB9Config T h z) := by
    simpa [setupB9Config, setupZConfig] using
      setupB9_at (setupZConfig T h z).tape
        (h+4+3*(z:Int)) g.b9
  have hA : run tm2 (3*(A+1)) (setupB9Config T h z) =
      some (setupAConfig T h z A) := by
    simpa [setupAConfig, setupB9Config] using
      counted_right_sweep (A+1) (setupB9Config T h z).tape
        (h+7+3*(z:Int)) g.aRun
  have h6 : run tm2 6 (setupAConfig T h z A) =
      some (setupB6Config T h z A) := by
    simpa [setupB6Config, setupAConfig] using
      setupB6_at (setupAConfig T h z A).tape
        (h+10+3*(z:Int)+3*(A:Int)) g.b6
  have hL : run tm2 (3*(L+1)) (setupB6Config T h z A) =
      some (setupLConfig T h z A L) := by
    simpa [setupLConfig, setupB6Config] using
      counted_right_sweep (L+1) (setupB6Config T h z A).tape
        (h+14+3*(z:Int)+3*(A:Int)) g.lRun
  have h30 : run tm2 30 (setupLConfig T h z A L) =
      some (setupB30Config T h z A L) := by
    simpa [setupB30Config, setupLConfig] using
      setupB30_at (setupLConfig T h z A L).tape
        (h+17+3*(z:Int)+3*(A:Int)+3*(L:Int)) g.b30
  have h12 := run_append_some h20 hz
  have h123 := run_append_some h12 h9
  have h1234 := run_append_some h123 hA
  have h12345 := run_append_some h1234 h6
  have h123456 := run_append_some h12345 hL
  exact run_append_some h123456 h30

/-- The suffix's head displacement is exactly 3*(A+L+z)+13. -/
theorem setupB30Config_head (T : Int → Bool) (h : Int)
    (A L z : Nat) :
    (setupB30Config T h z A L).head =
      h + 3*((A+L+z:Int)) + 13 := by
  simp [setupB30Config, setupLConfig, setupB6Config,
    setupAConfig, setupB9Config, setupZConfig, setupB20Config,
    q4FrameAt, q4Frame, q4CenterTape, shiftConfig, embed]
  omega

/-- The suffix's total cost is the linear remainder 3*(A+L+z)+71. -/
theorem setupSuffixCost_eq (A L z : Nat) :
    20+3*z+9+3*(A+1)+6+3*(L+1)+30 =
      3*(A+L+z)+71 := by
  omega

#print axioms positiveZSetupSuffix_run

end BB6Coverage.Agent48PositiveZSetup
