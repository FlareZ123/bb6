import PositiveZCheckpointSetupBridges
import CountedSweep
import D0SweepLeftFacing

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
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent48D0SweepLeftFacing

set_option maxHeartbeats 4000000

theorem sweptRight_preserves_before (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : x < h) :
    sweptRight n T h x = T x := by
  induction n generalizing T h x with
  | zero => rfl
  | succ n ih =>
      simp only [sweptRight]
      have hx1 : x ≠ h+1 := by omega
      have hx2 : x ≠ h+2 := by omega
      have hx' : x < h+3 := by omega
      simp [afterRight3, hx1, hx2, ih (afterRight3 T h) (h+3) x hx']

theorem sweptRight_preserves_after (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : h+3*(n:Int) ≤ x) :
    sweptRight n T h x = T x := by
  induction n generalizing T h x with
  | zero => rfl
  | succ n ih =>
      simp only [sweptRight]
      have hx1 : x ≠ h+1 := by omega
      have hx2 : x ≠ h+2 := by omega
      have hx' : (h+3)+3*(n:Int) ≤ x := by omega
      simpa [afterRight3, hx1, hx2] using
        ih (afterRight3 T h) (h+3) x hx'

theorem sweptRight_clears_second (n : Nat) (T : Int → Bool)
    (h : Int) (i : Nat) (hi : i<n) :
    sweptRight n T h (h+3*(i:Int)+1) = false := by
  induction n generalizing T h i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero =>
          simp only [sweptRight]
          have hp := sweptRight_preserves_before n (afterRight3 T h)
            (h+3) (h+1) (by omega)
          rw [hp]
          simp [afterRight3]
      | succ i =>
          have hi' : i<n := by omega
          have heq : h+3*((i+1:Int))+1 = (h+3)+3*(i:Int)+1 := by omega
          simp only [sweptRight]
          rw [heq]
          exact ih (afterRight3 T h) (h+3) i hi'

theorem sweptRight_clears_third (n : Nat) (T : Int → Bool)
    (h : Int) (i : Nat) (hi : i<n) :
    sweptRight n T h (h+3*(i:Int)+2) = false := by
  induction n generalizing T h i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero =>
          simp only [sweptRight]
          have hp := sweptRight_preserves_before n (afterRight3 T h)
            (h+3) (h+2) (by omega)
          rw [hp]
          simp [afterRight3]
      | succ i =>
          have hi' : i<n := by omega
          have heq : h+3*((i+1:Int))+2 = (h+3)+3*(i:Int)+2 := by omega
          simp only [sweptRight]
          rw [heq]
          exact ih (afterRight3 T h) (h+3) i hi'

theorem sweptRight_preserves_block_start (n : Nat) (T : Int → Bool)
    (h : Int) (i : Nat) (hi : i<n) :
    sweptRight n T h (h+3*(i:Int)) = T (h+3*(i:Int)) := by
  induction n generalizing T h i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero =>
          simp only [sweptRight]
          have hp := sweptRight_preserves_before n (afterRight3 T h)
            (h+3) h (by omega)
          rw [hp]
          simp [afterRight3]
      | succ i =>
          have hi' : i<n := by omega
          have heq : h+3*((i+1:Int)) = (h+3)+3*(i:Int) := by omega
          simp only [sweptRight]
          rw [heq]
          have hInd := ih (afterRight3 T h) (h+3) i hi'
          rw [hInd]
          have hneq1 : h+3+3*(i:Int) ≠ h+1 := by omega
          have hneq2 : h+3+3*(i:Int) ≠ h+2 := by omega
          simp [afterRight3, hneq1, hneq2]

theorem sweptRight_block_pattern (n : Nat) (T : Int → Bool)
    (h : Int) (i : Nat) (hi : i<n)
    (hon : rightOnes T h n) :
    sweptRight n T h (h+3*(i:Int)) = true ∧
    sweptRight n T h (h+3*(i:Int)+1) = false ∧
    sweptRight n T h (h+3*(i:Int)+2) = false := by
  obtain ⟨h0, h1, h2⟩ := hon i hi
  constructor
  · rw [sweptRight_preserves_block_start n T h i hi]
    exact h0
  constructor
  · exact sweptRight_clears_second n T h i hi
  · exact sweptRight_clears_third n T h i hi

theorem run_append_some {n m : Nat} {c d e : Config}
    (h₁ : run tm2 n c = some d)
    (h₂ : run tm2 m d = some e) :
    run tm2 (n+m) c = some e := by
  simpa [run_append, h₁] using h₂

/-- State-3 configuration immediately after the 20-step B20 bridge. -/
def setupB20Config (T : Int → Bool) (h : Int) : Config :=
  q4FrameAt T h setupB20Inside setupB20End

/-- State-3 configuration after sweeping the L+1 left-context triples. -/
def setupLConfig (T : Int → Bool) (h : Int) (L : Nat) : Config :=
  ⟨3, h+4+3*((L+1):Int),
    sweptRight (L+1) (setupB20Config T h).tape (h+4)⟩

/-- State-3 configuration immediately after the 9-step B9 bridge. -/
def setupB9Config (T : Int → Bool) (h : Int) (L : Nat) : Config :=
  q4FrameAt (setupLConfig T h L).tape
    (h+7+3*(L:Int)) setupB9Inside setupB9End

/-- State-3 configuration after sweeping the A+1 left-context triples. -/
def setupAConfig (T : Int → Bool) (h : Int) (L A : Nat) : Config :=
  ⟨3, h+13+3*(L:Int)+3*(A:Int),
    sweptRight (A+1) (setupB9Config T h L).tape
      (h+10+3*(L:Int))⟩

/-- State-3 configuration immediately after the 6-step B6 bridge. -/
def setupB6Config (T : Int → Bool) (h : Int) (L A : Nat) : Config :=
  q4FrameAt (setupAConfig T h L A).tape
    (h+13+3*(L:Int)+3*(A:Int)) setupB6Inside setupB6End

/-- State-3 configuration after sweeping the z right-counter triples. -/
def setupZConfig (T : Int → Bool) (h : Int) (L A z : Nat) : Config :=
  ⟨3, h+17+3*(L:Int)+3*(A:Int)+3*(z:Int),
    sweptRight z (setupB6Config T h L A).tape
      (h+17+3*(L:Int)+3*(A:Int))⟩

/-- Final state-3 configuration after the 30-step B30 return bridge. -/
def setupB30Config (T : Int → Bool) (h : Int)
    (L A z : Nat) : Config :=
  q4FrameAt (setupZConfig T h L A z).tape
    (h+17+3*(L:Int)+3*(A:Int)+3*(z:Int))
    setupB30Inside setupB30End

/-- The exact local and unary-block guards needed to compose the suffix.
The later S0-specific proof should establish these from the output of the
two left-one scans. -/
structure SetupSuffixGuards (T : Int → Bool) (h : Int)
    (A L z : Nat) : Prop where
  b20 : setupB20Input T h
  lRun : rightOnes (setupB20Config T h).tape (h+4) (L+1)
  b9 : setupB9Input (setupLConfig T h L).tape
    (h+7+3*(L:Int))
  aRun : rightOnes (setupB9Config T h L).tape
    (h+10+3*(L:Int)) (A+1)
  b6 : setupB6Input (setupAConfig T h L A).tape
    (h+13+3*(L:Int)+3*(A:Int))
  zRun : rightOnes (setupB6Config T h L A).tape
    (h+17+3*(L:Int)+3*(A:Int)) z
  b30 : setupB30Input (setupZConfig T h L A z).tape
    (h+17+3*(L:Int)+3*(A:Int)+3*(z:Int))

/-- Exact suffix run: B20, right sweep L+1, B9, right sweep A+1,
B6, right sweep z, and B30. -/
theorem positiveZSetupSuffix_run (T : Int → Bool) (h : Int)
    (A L z : Nat) (g : SetupSuffixGuards T h A L z) :
    run tm2
      (20+3*(L+1)+9+3*(A+1)+6+3*z+30)
      ⟨3,h,T⟩ =
      some (setupB30Config T h L A z) := by
  have h20 : run tm2 20 ⟨3,h,T⟩ =
      some (setupB20Config T h) := by
    simpa [setupB20Config] using setupB20_at T h g.b20
  have hL : run tm2 (3*(L+1)) (setupB20Config T h) =
      some (setupLConfig T h L) := by
    simpa [setupLConfig, setupB20Config] using
      counted_right_sweep (L+1) (setupB20Config T h).tape
        (h+4) g.lRun
  have h9 : run tm2 9 (setupLConfig T h L) =
      some (setupB9Config T h L) := by
    simpa [setupB9Config, setupLConfig] using
      setupB9_at (setupLConfig T h L).tape
        (h+7+3*(L:Int)) g.b9
  have hA : run tm2 (3*(A+1)) (setupB9Config T h L) =
      some (setupAConfig T h L A) := by
    simpa [setupAConfig, setupB9Config] using
      counted_right_sweep (A+1) (setupB9Config T h L).tape
        (h+10+3*(L:Int)) g.aRun
  have h6 : run tm2 6 (setupAConfig T h L A) =
      some (setupB6Config T h L A) := by
    simpa [setupB6Config, setupAConfig] using
      setupB6_at (setupAConfig T h L A).tape
        (h+13+3*(L:Int)+3*(A:Int)) g.b6
  have hz : run tm2 (3*z) (setupB6Config T h L A) =
      some (setupZConfig T h L A z) := by
    simpa [setupZConfig, setupB6Config] using
      counted_right_sweep z (setupB6Config T h L A).tape
        (h+17+3*(L:Int)+3*(A:Int)) g.zRun
  have h30 : run tm2 30 (setupZConfig T h L A z) =
      some (setupB30Config T h L A z) := by
    simpa [setupB30Config, setupZConfig] using
      setupB30_at (setupZConfig T h L A z).tape
        (h+17+3*(L:Int)+3*(A:Int)+3*(z:Int)) g.b30
  have h12 := run_append_some h20 hL
  have h123 := run_append_some h12 h9
  have h1234 := run_append_some h123 hA
  have h12345 := run_append_some h1234 h6
  have h123456 := run_append_some h12345 hz
  exact run_append_some h123456 h30

/-- The suffix's head displacement is exactly 3*(A+L+z)+13. -/
theorem setupB30Config_head (T : Int → Bool) (h : Int)
    (A L z : Nat) :
    (setupB30Config T h L A z).head =
      h + 3*((A+L+z:Int)) + 13 := by
  simp [setupB30Config, setupZConfig, setupB6Config,
    setupAConfig, setupB9Config, setupLConfig, setupB20Config,
    q4FrameAt, q4Frame, q4CenterTape, shiftConfig, embed]
  omega

/-- The suffix's total cost is the linear remainder 3*(A+L+z)+71. -/
/-- The B30 suffix exposes the complete d0 block prefix. Each block,
read leftward from the final head, is 001: the first z-1 blocks come from
the counted sweep and the final block is the B6 boundary frame. -/
theorem setupB30Config_d0_block (T : Int → Bool) (h : Int)
    (A L z : Nat) (g : SetupSuffixGuards T h A L z)
    (hz : 2≤z) (j : Nat) (hj : j<z) :
    (setupB30Config T h L A z).tape
      (h+13+3*(L:Int)+3*(A:Int)+3*(z:Int)-3*(j:Int)) = false ∧
    (setupB30Config T h L A z).tape
      (h+13+3*(L:Int)+3*(A:Int)+3*(z:Int)-3*(j:Int)-1) = false ∧
    (setupB30Config T h L A z).tape
      (h+13+3*(L:Int)+3*(A:Int)+3*(z:Int)-3*(j:Int)-2) = true := by
  let b6 : Int := h+13+3*(L:Int)+3*(A:Int)
  let hs : Int := b6+4
  let hb : Int := hs+3*(z:Int)
  let hf : Int := b6+3*(z:Int)
  have hbhf : hb-4=hf := by dsimp [hb,hs,hf,b6]; omega
  have hfinalCoord :
      h+13+3*(L:Int)+3*(A:Int)+3*(z:Int)=hf := by
    dsimp [hf,b6]
    omega
  rw [hfinalCoord]
  have hframe : ∀ x, (setupB30Config T h L A z).tape x =
      (if setupB30Inside (x-hb)
       then decide (x-hb ∈ setupB30End.marked)
       else (setupZConfig T h L A z).tape x) := by
    intro x
    simp [setupB30Config, hb, hs, b6, q4FrameAt_tape]
  have hzframe : ∀ x, (setupZConfig T h L A z).tape x =
      sweptRight z (setupB6Config T h L A).tape hs x := by
    intro x
    simp [setupZConfig, hs, b6]
  have hframeOutside {x : Int} (hx : x<hf) :
      (setupB30Config T h L A z).tape x =
        (setupZConfig T h L A z).tape x := by
    rw [hframe]
    have hnot : setupB30Inside (x-hb)=false := by
      simp [setupB30Inside, hbhf]
      omega
    simp [hnot]
  have hframeAtHead :
      (setupB30Config T h L A z).tape hf = false := by
    rw [hframe]
    have hin : setupB30Inside (hf-hb)=true := by
      simp [setupB30Inside, hbhf]
    have hnotmem : hf-hb ∉ setupB30End.marked := by
      have hEq : hf-hb = -4 := by omega
      simp [hEq, setupB30End]
    simp [hin, hnotmem]
  have hzpres {x : Int} (hx : x<hs) :
      (setupZConfig T h L A z).tape x =
        (setupB6Config T h L A).tape x := by
    rw [hzframe]
    exact sweptRight_preserves_before z
      (setupB6Config T h L A).tape hs x hx
  by_cases hjlast : j=z-1
  · have hx0 : hf-3*(j:Int)=b6+3 := by
      dsimp [hf,b6]; omega
    have hx1 : hf-3*(j:Int)-1=b6+2 := by
      dsimp [hf,b6]; omega
    have hx2 : hf-3*(j:Int)-2=b6+1 := by
      dsimp [hf,b6]; omega
    have hb6three :
        (setupB6Config T h L A).tape (b6+3)=false := by
      simp [setupB6Config, q4FrameAt_tape, setupB6Inside,
        setupB6End, b6]
    have hb6two :
        (setupB6Config T h L A).tape (b6+2)=false := by
      simp [setupB6Config, q4FrameAt_tape, setupB6Inside,
        setupB6End, b6]
    have hb6one :
        (setupB6Config T h L A).tape (b6+1)=true := by
      simp [setupB6Config, q4FrameAt_tape, setupB6Inside,
        setupB6End, b6]
    have hpres0 : (setupB30Config T h L A z).tape (b6+3) =
        (setupB6Config T h L A).tape (b6+3) := by
      rw [hframeOutside (by dsimp [hf,b6]; omega)]
      exact hzpres (by dsimp [hs,b6]; omega)
    have hpres1 : (setupB30Config T h L A z).tape (b6+2) =
        (setupB6Config T h L A).tape (b6+2) := by
      rw [hframeOutside (by dsimp [hf,b6]; omega)]
      exact hzpres (by dsimp [hs,b6]; omega)
    have hpres2 : (setupB30Config T h L A z).tape (b6+1) =
        (setupB6Config T h L A).tape (b6+1) := by
      rw [hframeOutside (by dsimp [hf,b6]; omega)]
      exact hzpres (by dsimp [hs,b6]; omega)
    rw [hx0, hx1, hx2]
    exact ⟨hpres0.trans hb6three, hpres1.trans hb6two,
      hpres2.trans hb6one⟩
  · have hjlt : j<z-1 := by omega
    let i : Nat := z-2-j
    have hi : i<z := by dsimp [i]; omega
    have hc0 : hs+3*(i:Int)=hf-3*(j:Int)-2 := by
      dsimp [i,hs,hf,b6]; omega
    have hc1 : hs+3*(i:Int)+1=hf-3*(j:Int)-1 := by
      dsimp [i,hs,hf,b6]; omega
    have hc2 : hs+3*(i:Int)+2=hf-3*(j:Int) := by
      dsimp [i,hs,hf,b6]; omega
    have hblock0 : (setupZConfig T h L A z).tape
        (hf-3*(j:Int)-2) = true := by
      rw [hzframe, ← hc0]
      rw [sweptRight_preserves_block_start z
        (setupB6Config T h L A).tape hs i hi]
      exact (g.zRun i hi).1
    have hblock1 : (setupZConfig T h L A z).tape
        (hf-3*(j:Int)-1) = false := by
      rw [hzframe, ← hc1]
      exact sweptRight_clears_second z
        (setupB6Config T h L A).tape hs i hi
    have hblock2 : (setupZConfig T h L A z).tape
        (hf-3*(j:Int)) = false := by
      rw [hzframe, ← hc2]
      exact sweptRight_clears_third z
        (setupB6Config T h L A).tape hs i hi
    have hx0 : hf-3*(j:Int)-2<hf := by omega
    have hx1 : hf-3*(j:Int)-1<hf := by omega
    have hpres0 := hframeOutside hx0
    have hpres1 := hframeOutside hx1
    have hfirst : (setupB30Config T h L A z).tape
        (hf-3*(j:Int)-2)=true := by
      rw [hpres0]
      exact hblock0
    have hsecond : (setupB30Config T h L A z).tape
        (hf-3*(j:Int)-1)=false := by
      rw [hpres1]
      exact hblock1
    have hthird : (setupB30Config T h L A z).tape
        (hf-3*(j:Int))=false := by
      by_cases hj0 : j=0
      · have heq : hf-3*(j:Int)=hf := by simp [hj0]
        rw [heq]
        exact hframeAtHead
      · have hx2 : hf-3*(j:Int)<hf := by omega
        rw [hframeOutside hx2]
        exact hblock2
    exact ⟨hthird, hsecond, hfirst⟩

/-- The z sweep and B30 preserve every cell in the B6 left tail.
For z≥2 the B30 frame begins strictly to the right of that tail. -/
theorem setupB30Config_preserves_b6_left (T : Int → Bool) (h : Int)
    (A L z : Nat) (hz : 2≤z) (i : Nat) :
    (setupB30Config T h L A z).tape
      (h+13+3*(L:Int)+3*(A:Int)-(i:Int)) =
    (setupB6Config T h L A).tape
      (h+13+3*(L:Int)+3*(A:Int)-(i:Int)) := by
  let b6 : Int := h+13+3*(L:Int)+3*(A:Int)
  let hs : Int := b6+4
  let hb : Int := hs+3*(z:Int)
  have hSweep : (setupZConfig T h L A z).tape (b6-(i:Int)) =
      (setupB6Config T h L A).tape (b6-(i:Int)) := by
    simp [setupZConfig, hs, b6, sweptRight_preserves_before
      z (setupB6Config T h L A).tape hs (b6-(i:Int)) (by omega)]
  have hnot : setupB30Inside ((b6-(i:Int))-hb)=false := by
    simp [setupB30Inside]
    dsimp [hb,hs,b6]
    omega
  rw [show h+13+3*(L:Int)+3*(A:Int)-(i:Int)=b6-(i:Int) by
    dsimp [b6]]
  simp [setupB30Config, q4FrameAt_tape, hnot,
    hb, hs, b6, hSweep]

/-- Physical-order 100 block power used for the simpler residual word. -/
def setupD100pow : Nat → List Bool
  | 0 => []
  | n+1 => [true,false,false] ++ setupD100pow n

/-- Agent 24's equivalent residual-context normal form:
110 ++ (100)^(A+1) ++ 111 ++ (100)^(L+1) ++ 1110111.
This is the same list as the shifted 010-expression in the checkpoint
dossier, but aligns directly with the counted sweep's physical output. -/
def setupL2 (A L : Nat) : List Bool :=
  [true,true,false] ++ setupD100pow (A+1) ++
  [true,true,true] ++ setupD100pow (L+1) ++
  [true,true,true,false,true,true,true]

/-- The sole z-independent left-tail identity still needed after B6. -/
def SetupB6LeftTail (T : Int → Bool) (h : Int) (A L : Nat) : Prop :=
  ∀ i : Nat,
    (setupB6Config T h L A).tape
      (h+13+3*(L:Int)+3*(A:Int)-(i:Int)) =
    sideBit (setupL2 A L) i

/-- Length of the base-3 all-zero counter word. -/
theorem setup_d0pow_length (n : Nat) : (d0pow n).length=3*n := by
  induction n with
  | zero => simp [d0pow]
  | succ n ih => simp [d0pow, d0, ih]

/-- Append decomposition for the tape-side indexing convention. -/
theorem setup_sideBit_append (xs ys : List Bool) (i : Nat) :
    sideBit (xs++ys) i =
      if i<xs.length then sideBit xs i else sideBit ys (i-xs.length) := by
  intro i
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons b xs ih =>
      cases i with
      | zero => simp [sideBit]
      | succ i => simp [sideBit, ih]

/-- Given the B6 left-tail identity, the z-sweep/B30 suffix produces the
complete left-facing word d0pow(z) ++ setupL2(A,L). -/
theorem setupB30Config_leftFacing (T : Int → Bool) (h : Int)
    (A L z : Nat) (g : SetupSuffixGuards T h A L z)
    (hz : 2≤z) (htail : SetupB6LeftTail T h A L) :
    ∀ i : Nat,
      (setupB30Config T h L A z).tape
        (h+13+3*(L:Int)+3*(A:Int)+3*(z:Int)-(i:Int)) =
      sideBit (d0pow z ++ setupL2 A L) i := by
  intro i
  have hlen : (d0pow z).length=3*z := setup_d0pow_length z
  by_cases hi : i<3*z
  · have hmod : i%3=0 ∨ i%3=1 ∨ i%3=2 := by omega
    rcases hmod with h0|h1|h2
    · let j : Nat := i/3
      have hiq : i=3*j := by dsimp [j]; omega
      have hj : j<z := by omega
      have hb := setupB30Config_d0_block T h A L z g hz j hj
      rw [setup_sideBit_append]
      simp [hlen, hi, hiq, sideBit_d0pow_pattern, h0]
      simpa [hiq] using hb.1
    · let j : Nat := i/3
      have hiq : i=3*j+1 := by dsimp [j]; omega
      have hj : j<z := by omega
      have hb := setupB30Config_d0_block T h A L z g hz j hj
      rw [setup_sideBit_append]
      simp [hlen, hi, hiq, sideBit_d0pow_pattern, h1]
      simpa [hiq] using hb.2.1
    · let j : Nat := i/3
      have hiq : i=3*j+2 := by dsimp [j]; omega
      have hj : j<z := by omega
      have hb := setupB30Config_d0_block T h A L z g hz j hj
      rw [setup_sideBit_append]
      simp [hlen, hi, hiq, sideBit_d0pow_pattern, h2]
      simpa [hiq] using hb.2.2
  · have hge : 3*z≤i := by omega
    let j : Nat := i-3*z
    have heq :
        h+13+3*(L:Int)+3*(A:Int)+3*(z:Int)-(i:Int) =
        h+13+3*(L:Int)+3*(A:Int)-(j:Int) := by
      dsimp [j]
      omega
    rw [heq]
    rw [setupB30Config_preserves_b6_left T h A L z hz j]
    rw [setup_sideBit_append]
    simp [hlen, hge, j]
    exact htail j

theorem setupSuffixCost_eq (A L z : Nat) :
    20+3*(L+1)+9+3*(A+1)+6+3*z+30 =
      3*(A+L+z)+71 := by
  omega

#print axioms positiveZSetupSuffix_run

end BB6Coverage.Agent48PositiveZSetup
