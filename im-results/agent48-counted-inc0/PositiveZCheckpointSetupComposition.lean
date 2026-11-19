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
/-- Shifted 010-to-100 rotation identities used to reconcile the two
presentations of the residual left context. -/
def setupD010pow : Nat → List Bool
  | 0 => []
  | n+1 => [false,true,false] ++ setupD010pow n

theorem setupShift10_short (n : Nat) :
    [true,false] ++ setupD010pow n ++ [false,true,true] =
    [true,false,false] ++ setupD100pow n ++ [true,true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [setupD010pow, setupD100pow, List.append_assoc]
      change [true,false,false] ++
          ([true,false] ++ setupD010pow n ++ [false,true,true]) =
        [true,false,false] ++
          ([true,false,false] ++ setupD100pow n ++ [true,true])
      rw [ih]

theorem setupShift11 (n : Nat) :
    [true,true] ++ setupD010pow n ++ [false,true,true] =
    [true,true,false] ++ setupD100pow n ++ [true,true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [setupD010pow, setupD100pow, List.append_assoc]
      change [true,true,false] ++
          ([true,false] ++ setupD010pow n ++ [false,true,true]) =
        [true,true,false] ++
          ([true,false,false] ++ setupD100pow n ++ [true,true])
      rw [setupShift10_short n]

theorem setupShift10_long (n : Nat) :
    [true,false] ++ setupD010pow n ++
        [false,true,true,true,false,true,true,true] =
    [true,false,false] ++ setupD100pow n ++
        [true,true,true,false,true,true,true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [setupD010pow, setupD100pow, List.append_assoc]
      change [true,false,false] ++
          ([true,false] ++ setupD010pow n ++
            [false,true,true,true,false,true,true,true]) =
        [true,false,false] ++
          ([true,false,false] ++ setupD100pow n ++
            [true,true,true,false,true,true,true])
      rw [ih]

/-- The original checkpoint-dossier word
11 ++ (010)^(A+1) ++ 011 ++ 110 ++ (010)^L ++ 011 ++ 101 ++ 11. -/
/-- Pointwise pattern of the physical-order 100 block power. -/
theorem sideBit_setupD100pow_pattern (n i : Nat) (hi : i<3*n) :
    sideBit (setupD100pow n) i = decide (i%3=0) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [setupD100pow, sideBit]
      | succ i =>
          cases i with
          | zero => simp [setupD100pow, sideBit]
          | succ i =>
              cases i with
              | zero => simp [setupD100pow, sideBit]
              | succ i =>
                  have hi' : i<3*n := by omega
                  have hmod : (i+3)%3=i%3 := by omega
                  simpa [setupD100pow, sideBit, hmod] using ih i hi'

/-- A counted right sweep, read backwards from three cells before its
final head, is exactly the physical-order 100 block power. The two zero
cells immediately to the left of the sweep complete its final block. -/
theorem sweptRight_leftFacing_d100pow (n : Nat) (T : Int → Bool)
    (h : Int) (hon : rightOnes T h n)
    (hleft1 : T (h-1)=false) (hleft2 : T (h-2)=false) :
    ∀ i : Nat, i<3*n →
      sweptRight n T h (h+3*(n:Int)-3-(i:Int)) =
        sideBit (setupD100pow n) i := by
  intro i hi
  have hmod : i%3=0 ∨ i%3=1 ∨ i%3=2 := by omega
  rcases hmod with h0|h1|h2
  · let q : Nat := i/3
    let j : Nat := n-q-1
    have hiq : i=3*q := by dsimp [q]; omega
    have hj : j<n := by dsimp [j]; omega
    have hcoord :
        h+3*(n:Int)-3-(i:Int)=h+3*(j:Int) := by
      dsimp [j]
      rw [hiq]
      omega
    rw [hcoord, sweptRight_preserves_block_start n T h j hj]
    rw [sideBit_setupD100pow_pattern n i hi]
    simp [h0]
    exact (hon j hj).1
  · let q : Nat := i/3
    let j : Nat := n-q-1
    have hiq : i=3*q+1 := by dsimp [q]; omega
    have hj : j<n := by dsimp [j]; omega
    have hcoord :
        h+3*(n:Int)-3-(i:Int)=h+3*(j:Int)-1 := by
      dsimp [j]
      rw [hiq]
      omega
    rw [hcoord, sideBit_setupD100pow_pattern n i hi]
    simp [h1]
    by_cases hj0 : j=0
    · subst j
      have hp := sweptRight_preserves_before n T h (h-1) (by omega)
      rw [hp]
      exact hleft1
    · let k : Nat := j-1
      have hk : k<n := by dsimp [k]; omega
      have hcoord2 : h+3*(j:Int)-1=h+3*(k:Int)+2 := by
        dsimp [k]
        omega
      rw [hcoord2]
      exact sweptRight_clears_third n T h k hk
  · let q : Nat := i/3
    let j : Nat := n-q-1
    have hiq : i=3*q+2 := by dsimp [q]; omega
    have hj : j<n := by dsimp [j]; omega
    have hcoord :
        h+3*(n:Int)-3-(i:Int)=h+3*(j:Int)-2 := by
      dsimp [j]
      rw [hiq]
      omega
    rw [hcoord, sideBit_setupD100pow_pattern n i hi]
    simp [h2]
    by_cases hj0 : j=0
    · subst j
      have hp := sweptRight_preserves_before n T h (h-2) (by omega)
      rw [hp]
      exact hleft2
    · let k : Nat := j-1
      have hk : k<n := by dsimp [k]; omega
      have hcoord2 : h+3*(j:Int)-2=h+3*(k:Int)+1 := by
        dsimp [k]
        omega
      rw [hcoord2]
      exact sweptRight_clears_second n T h k hk

def setupEll1 (A L : Nat) : List Bool :=
  [true,true] ++ setupD010pow (A+1) ++
  [false,true,true,true,true,false] ++ setupD010pow L ++
  [false,true,true,true,false,true,true,true]

/-- Agent 24's 110/100 presentation is exactly the same residual word. -/
theorem setupEll1_eq_setupL2 (A L : Nat) :
    setupEll1 A L = setupL2 A L := by
  unfold setupEll1 setupL2
  simp only [List.append_assoc]
  calc
    [true,true] ++ setupD010pow (A+1) ++
        ([false,true,true] ++ [true,true,false]) ++
        setupD010pow L ++ [false,true,true,true,false,true,true,true]
      =
        ([true,true] ++ setupD010pow (A+1) ++ [false,true,true]) ++
        ([true,true,false] ++ setupD010pow L ++
          [false,true,true,true,false,true,true,true]) := by
            simp [List.append_assoc]
    _ =
        ([true,true,false] ++ setupD100pow (A+1) ++ [true,true]) ++
        ([true,true,false] ++ setupD010pow L ++
          [false,true,true,true,false,true,true,true]) := by
            rw [setupShift11 (A+1)]
    _ =
        [true,true,false] ++ setupD100pow (A+1) ++ [true,true,true] ++
        ([true,false] ++ setupD010pow L ++
          [false,true,true,true,false,true,true,true]) := by
            simp [List.append_assoc]
    _ =
        [true,true,false] ++ setupD100pow (A+1) ++ [true,true,true] ++
        ([true,false,false] ++ setupD100pow L ++
          [true,true,true,false,true,true,true]) := by
            rw [setupShift10_long L]
    _ = setupL2 A L := by
          simp [setupD100pow, List.append_assoc]

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
theorem setupD100pow_length (n : Nat) :
    (setupD100pow n).length=3*n := by
  induction n with
  | zero => simp [setupD100pow]
  | succ n ih => simp [setupD100pow, ih]

/-- Exact piecewise tape-side indexing for the five pieces of setupL2. -/
theorem setupL2_sideBit (A L i : Nat) :
    sideBit (setupL2 A L) i =
      if i<3 then sideBit [true,true,false] i
      else if i-3<3*(A+1) then
        sideBit (setupD100pow (A+1)) (i-3)
      else if i-3-3*(A+1)<3 then
        sideBit [true,true,true] (i-3-3*(A+1))
      else if i-3-3*(A+1)-3<3*(L+1) then
        sideBit (setupD100pow (L+1)) (i-3-3*(A+1)-3)
      else
        sideBit [true,true,true,false,true,true,true]
          (i-3-3*(A+1)-3-3*(L+1)) := by
  simp [setupL2, setup_sideBit_append, setupD100pow_length]

theorem setupB6Config_preserves_before (T : Int → Bool) (h : Int)
    (A L : Nat) (x : Int)
    (hx : x < h+13+3*(L:Int)+3*(A:Int)-1) :
    (setupB6Config T h L A).tape x =
      (setupAConfig T h L A).tape x := by
  rw [setupB6Config, q4FrameAt_tape]
  have hnot : setupB6Inside
      (x-(h+13+3*(L:Int)+3*(A:Int)))=false := by
    simp [setupB6Inside]
    omega
  simp [hnot]

theorem setupAConfig_preserves_before (T : Int → Bool) (h : Int)
    (A L : Nat) (x : Int)
    (hx : x < h+10+3*(L:Int)) :
    (setupAConfig T h L A).tape x =
      (setupB9Config T h L).tape x := by
  simp only [setupAConfig]
  exact sweptRight_preserves_before (A+1)
    (setupB9Config T h L).tape (h+10+3*(L:Int)) x hx

theorem setupB9Config_preserves_before (T : Int → Bool) (h : Int)
    (L : Nat) (x : Int)
    (hx : x < h+7+3*(L:Int)-2) :
    (setupB9Config T h L).tape x =
      (setupLConfig T h L).tape x := by
  rw [setupB9Config, q4FrameAt_tape]
  have hnot : setupB9Inside (x-(h+7+3*(L:Int)))=false := by
    simp [setupB9Inside]
    omega
  simp [hnot]

theorem setupLConfig_preserves_before (T : Int → Bool) (h : Int)
    (L : Nat) (x : Int) (hx : x<h+4) :
    (setupLConfig T h L).tape x =
      (setupB20Config T h).tape x := by
  simp only [setupLConfig]
  exact sweptRight_preserves_before (L+1)
    (setupB20Config T h).tape (h+4) x hx

theorem setupB6Config_eq_setupB9Config_before_A
    (T : Int → Bool) (h : Int) (A L : Nat) (x : Int)
    (hx : x<h+10+3*(L:Int)) :
    (setupB6Config T h L A).tape x =
      (setupB9Config T h L).tape x := by
  rw [setupB6Config_preserves_before T h A L x (by omega)]
  exact setupAConfig_preserves_before T h A L x hx

theorem setupB6Config_eq_setupLConfig_before_L
    (T : Int → Bool) (h : Int) (A L : Nat) (x : Int)
    (hx : x<h+7+3*(L:Int)-2) :
    (setupB6Config T h L A).tape x =
      (setupLConfig T h L).tape x := by
  rw [setupB6Config_preserves_before T h A L x (by omega)]
  rw [setupAConfig_preserves_before T h A L x (by omega)]
  exact setupB9Config_preserves_before T h L x hx

theorem setupB6Config_eq_setupB20Config_before_L
    (T : Int → Bool) (h : Int) (A L : Nat) (x : Int)
    (hx : x<h+4) :
    (setupB6Config T h L A).tape x =
      (setupB20Config T h).tape x := by
  rw [setupB6Config_preserves_before T h A L x (by omega)]
  rw [setupAConfig_preserves_before T h A L x (by omega)]
  rw [setupB9Config_preserves_before T h L x (by omega)]
  exact setupLConfig_preserves_before T h L x hx

theorem setupB20Config_endBits (T : Int → Bool) (h : Int) :
    (setupB20Config T h).tape (h+3)=false ∧
    (setupB20Config T h).tape (h+2)=false ∧
    (setupB20Config T h).tape (h+1)=true ∧
    (setupB20Config T h).tape h=true ∧
    (setupB20Config T h).tape (h-1)=true ∧
    (setupB20Config T h).tape (h-2)=false ∧
    (setupB20Config T h).tape (h-3)=true ∧
    (setupB20Config T h).tape (h-4)=true ∧
    (setupB20Config T h).tape (h-5)=true := by
  simp [setupB20Config, q4FrameAt_tape, setupB20Inside, setupB20End]

theorem setupB9Config_endBits (T : Int → Bool) (h : Int) (L : Nat) :
    (setupB9Config T h L).tape (h+7+3*(L:Int)+2)=false ∧
    (setupB9Config T h L).tape (h+7+3*(L:Int)+1)=false ∧
    (setupB9Config T h L).tape (h+7+3*(L:Int))=true ∧
    (setupB9Config T h L).tape (h+7+3*(L:Int)-1)=true ∧
    (setupB9Config T h L).tape (h+7+3*(L:Int)-2)=true := by
  simp [setupB9Config, q4FrameAt_tape, setupB9Inside, setupB9End]

theorem setupB6Config_prefixBits (T : Int → Bool) (h : Int)
    (A L : Nat) :
    (setupB6Config T h L A).tape
      (h+13+3*(L:Int)+3*(A:Int))=true ∧
    (setupB6Config T h L A).tape
      (h+13+3*(L:Int)+3*(A:Int)-1)=true := by
  simp [setupB6Config, q4FrameAt_tape, setupB6Inside, setupB6End]

/-- Blank left tail inherited from the S0 prefix before B20. -/
def SetupPrefixLeftBlank (T : Int → Bool) (h : Int) : Prop :=
  ∀ x : Int, x<h-5 → T x=false

theorem setupB20Config_preserves_before (T : Int → Bool) (h x : Int)
    (hx : x<h-5) :
    (setupB20Config T h).tape x = T x := by
  rw [setupB20Config, q4FrameAt_tape]
  have hnot : setupB20Inside (x-h)=false := by
    simp [setupB20Inside]
    omega
  simp [hnot]

theorem setupB6Config_preserves_prefix_blank (T : Int → Bool)
    (h : Int) (A L : Nat) (x : Int)
    (hx : x<h-5) :
    (setupB6Config T h L A).tape x = T x := by
  rw [setupB6Config_eq_setupB20Config_before_L T h A L x (by omega)]
  exact setupB20Config_preserves_before T h x hx

/-- The complete B6 left tail follows from the suffix guards and the
blank prefix tail before B20. The two counted sweeps supply the two 100
powers; B9 supplies the middle 111; B20 supplies the final 1110111. -/
theorem setupB6LeftTail_of_guards_and_blank (T : Int → Bool) (h : Int)
    (A L z : Nat) (g : SetupSuffixGuards T h A L z)
    (hblank : SetupPrefixLeftBlank T h) :
    SetupB6LeftTail T h A L := by
  intro i
  let b6 : Int := h+13+3*(L:Int)+3*(A:Int)
  let hA : Int := h+10+3*(L:Int)
  let hB9 : Int := h+7+3*(L:Int)
  let hL : Int := h+4
  rw [setupL2_sideBit]
  have hb6 := setupB6Config_prefixBits T h A L
  have hb9 := setupB9Config_endBits T h L
  have hb20 := setupB20Config_endBits T h
  rcases hb6 with ⟨hb6zero,hb6m1⟩
  rcases hb9 with ⟨hb9p2,hb9p1,hb9zero,hb9m1,hb9m2⟩
  rcases hb20 with ⟨hb20p3,hb20p2,hb20p1,hb20zero,hb20m1,
    hb20m2,hb20m3,hb20m4,hb20m5⟩
  have hAleft1 : (setupB9Config T h L).tape (hA-1)=false := by
    have heq : hA-1=hB9+2 := by dsimp [hA,hB9]; omega
    rw [heq]
    exact hb9p2
  have hAleft2 : (setupB9Config T h L).tape (hA-2)=false := by
    have heq : hA-2=hB9+1 := by dsimp [hA,hB9]; omega
    rw [heq]
    exact hb9p1
  have hLleft1 : (setupB20Config T h).tape (hL-1)=false := by
    have heq : hL-1=h+3 := by dsimp [hL]; omega
    rw [heq]
    exact hb20p3
  have hLleft2 : (setupB20Config T h).tape (hL-2)=false := by
    have heq : hL-2=h+2 := by dsimp [hL]; omega
    rw [heq]
    exact hb20p2
  have hAstream : ∀ j : Nat, j<3*(A+1) →
      (setupAConfig T h L A).tape (b6-3-(j:Int)) =
        sideBit (setupD100pow (A+1)) j := by
    intro j hj
    have hs := sweptRight_leftFacing_d100pow (A+1)
      (setupB9Config T h L).tape hA g.aRun hAleft1 hAleft2 j hj
    have heq : hA+3*((A+1):Int)-3-(j:Int)=b6-3-(j:Int) := by
      dsimp [hA,b6]
      omega
    rw [← heq]
    simpa [setupAConfig,hA] using hs
  have hLstream : ∀ j : Nat, j<3*(L+1) →
      (setupLConfig T h L).tape (hB9-3-(j:Int)) =
        sideBit (setupD100pow (L+1)) j := by
    intro j hj
    have hs := sweptRight_leftFacing_d100pow (L+1)
      (setupB20Config T h).tape hL g.lRun hLleft1 hLleft2 j hj
    have heq : hL+3*((L+1):Int)-3-(j:Int)=hB9-3-(j:Int) := by
      dsimp [hL,hB9]
      omega
    rw [← heq]
    simpa [setupLConfig,hL] using hs
  by_cases hi0 : i<3
  · simp [hi0]
    interval_cases i
    · simpa [sideBit,b6] using hb6zero
    · simpa [sideBit,b6] using hb6m1
    · have hpres := setupB6Config_preserves_before T h A L (b6-2) (by omega)
      rw [hpres]
      have heq : b6-2=hA+3*(A:Int)+1 := by
        dsimp [b6,hA]
        omega
      rw [heq]
      have hclear := sweptRight_clears_second (A+1)
        (setupB9Config T h L).tape hA A (by omega)
      simpa [setupAConfig,hA] using hclear
  · simp [hi0]
    by_cases hi1 : i-3<3*(A+1)
    · simp [hi1]
      let j : Nat := i-3
      have hj : j<3*(A+1) := by dsimp [j]; omega
      have heq : b6-(i:Int)=b6-3-(j:Int) := by
        dsimp [j]
        omega
      rw [heq]
      rw [setupB6Config_preserves_before T h A L (b6-3-(j:Int)) (by omega)]
      exact hAstream j hj
    · simp [hi1]
      by_cases hi2 : i-3-3*(A+1)<3
      · simp [hi2]
        let k : Nat := i-3-3*(A+1)
        have hk : k<3 := by dsimp [k]; omega
        have heq : b6-(i:Int)=hB9-(k:Int) := by
          dsimp [k,b6,hB9]
          omega
        rw [heq]
        rw [setupB6Config_eq_setupB9Config_before_A T h A L
          (hB9-(k:Int)) (by dsimp [hA,hB9]; omega)]
        interval_cases k
        · simpa [sideBit] using hb9zero
        · simpa [sideBit] using hb9m1
        · simpa [sideBit] using hb9m2
      · simp [hi2]
        by_cases hi3 : i-3-3*(A+1)-3<3*(L+1)
        · simp [hi3]
          let j : Nat := i-3-3*(A+1)-3
          have hj : j<3*(L+1) := by dsimp [j]; omega
          have heq : b6-(i:Int)=hB9-3-(j:Int) := by
            dsimp [j,b6,hB9]
            omega
          rw [heq]
          rw [setupB6Config_eq_setupLConfig_before_L T h A L
            (hB9-3-(j:Int)) (by omega)]
          exact hLstream j hj
        · simp [hi3]
          let k : Nat := i-3-3*(A+1)-3-3*(L+1)
          have heq : b6-(i:Int)=h+1-(k:Int) := by
            dsimp [k,b6]
            omega
          rw [heq]
          have hpres := setupB6Config_eq_setupB20Config_before_L T h A L
            (h+1-(k:Int)) (by omega)
          rw [hpres]
          by_cases hk7 : k<7
          · interval_cases k
            · simpa [sideBit] using hb20p1
            · simpa [sideBit] using hb20zero
            · simpa [sideBit] using hb20m1
            · simpa [sideBit] using hb20m2
            · simpa [sideBit] using hb20m3
            · simpa [sideBit] using hb20m4
            · simpa [sideBit] using hb20m5
          · have hx : h+1-(k:Int)<h-5 := by omega
            rw [setupB20Config_preserves_before T h (h+1-(k:Int)) hx]
            exact hblank (h+1-(k:Int)) hx

/-- Blank right tail beyond the last cell of the incoming z counter. -/
def SetupPrefixRightBlank (T : Int → Bool) (h : Int)
    (A L z : Nat) : Prop :=
  ∀ x : Int,
    h+17+3*(L:Int)+3*(A:Int)+3*(z:Int)<x → T x=false

def setupRightWord : List Bool :=
  [false,true,true,true,false,false,true,true,true]

theorem setupZConfig_preserves_after (T : Int → Bool) (h : Int)
    (A L z : Nat) (x : Int)
    (hx : h+17+3*(L:Int)+3*(A:Int)+3*(z:Int)≤x) :
    (setupZConfig T h L A z).tape x =
      (setupB6Config T h L A).tape x := by
  simp only [setupZConfig]
  exact sweptRight_preserves_after z
    (setupB6Config T h L A).tape
    (h+17+3*(L:Int)+3*(A:Int)) x (by omega)

theorem setupB30Config_rightFacing (T : Int → Bool) (h : Int)
    (A L z : Nat) (hblank : SetupPrefixRightBlank T h A L z) :
    ∀ i : Nat,
      (setupB30Config T h L A z).tape
        (h+13+3*(L:Int)+3*(A:Int)+3*(z:Int)+1-(i:Int)) =
      sideBit setupRightWord i := by
  intro i
  let hb : Int := h+17+3*(L:Int)+3*(A:Int)+3*(z:Int)
  have hfinal : h+13+3*(L:Int)+3*(A:Int)+3*(z:Int)=hb-4 := by
    dsimp [hb]
    omega
  by_cases hi : i<9
  · interval_cases i
    all_goals
      rw [show h+13+3*(L:Int)+3*(A:Int)+3*(z:Int)+1-(i:Int)
        = hb-3+(i:Int) by dsimp [hb]; omega]
      simp [setupB30Config, q4FrameAt_tape, setupB30Inside,
        setupB30End, setupRightWord, sideBit, hb]
  · have hge : 9≤i := by omega
    have hx : hb<x := by
      dsimp [hb]
      omega
    have hcoord :
        h+13+3*(L:Int)+3*(A:Int)+3*(z:Int)+1-(i:Int)=
          hb-3+(i:Int) := by
      dsimp [hb]
      omega
    rw [hcoord]
    rw [setupB30Config, q4FrameAt_tape]
    have hnot : setupB30Inside (hb-3+(i:Int)-hb)=false := by
      simp [setupB30Inside]
      omega
    simp [hnot]
    rw [setupZConfig_preserves_after T h A L z
      (hb-3+(i:Int)) (by omega)]
    exact hblank (hb-3+(i:Int)) hx

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
