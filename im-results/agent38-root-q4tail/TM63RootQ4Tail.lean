import TM63RootSecondQ4Frame
import PositiveZFirstCycleToSecondPrefix
import FirstQ4P1Arithmetic
import Lean.Elab.Tactic.Omega

/-!
# Authentic blank-root continuation through the second q4 prefix

Agent 48's root theorem reaches the output of the positive-z first q4 cycle.
Agent 24's theorem proves the first-cycle plus second-prefix run from the
canonical first q4 checkpoint.  Determinism and `run_append` let us extract
the second-prefix suffix from those two exact runs, without repeating its
private tape-guard proof.  Translation invariance then transports that
suffix to the authentic blank-root trajectory.

This is an intermediate source composition, not yet a compiled theorem or
a BB(6) halting proof.
-/

namespace BB6Coverage.Agent38RootQ4Tail

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent42FirstQ4P1Arithmetic
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent44TM63RootMiddle34
open BB6Coverage.Agent48RootFirstQ4Checkpoint
open BB6Coverage.Agent48RootSecondQ4Frame
open BB6Coverage.Agent48PositiveZFirstCycleEndpoint
open BB6Coverage.Agent48PositiveZSecondCycle
open BB6Coverage.Agent24PositiveZSecondPrefix

/-- Cost of the second q4 prefix after Agent 48's second q4 frame. -/
def rootSecondQ4TailPrefixCost : Nat :=
  34 + (3*2^rootMarker1Z+3*rootMarker1Z+7) + 2 +
    3*(2^(2^rootMarker1Z-1)) + 29

/-- The exact q4Tail frame reached after the second q4 prefix, in coordinates
relative to the authentic marker-1 S0 head. -/
def rootSecondQ4TailFrame : Config :=
  let z := rootMarker1Z
  let m := 3*2^z+3*z+7
  let n := 2^(2^z-1)
  let T1 := (frameAt rootSecondQ4Frame.tape 1
    secondCyclePrefix34Inside secondCyclePrefix34End).tape
  let h1 : Int := 1+4+(m:Int)
  let T2 := afterFirstCycleTwoZero T1 h1
  let h2 : Int := h1+2
  let T3 := d0Sweep n T2 h2
  let g : Int := h2+3*(n:Int)
  frameAt T3 g q4TailInside q4TailEnd

/-- The P1 value at the authentic root has odd parity.  Here A is at least
two because the marker-1 width is exponent + right + 2. -/
private theorem rootP1Value_odd :
    firstQ4P1Value tm63Length1 rootMarker1A % 2 = 1 := by
  have hA2 : 2 ≤ rootMarker1A := by
    dsimp [rootMarker1A]
    omega
  let k : Nat :=
    2^(rootMarker1A-2) * (2^(tm63Length1+2)-1)
  have hC : 0 < 2^(tm63Length1+2)-1 := by
    have hp : 2 ≤ 2^(tm63Length1+2) := by
      have h := Nat.pow_le_pow_right (by decide : 0 < 2)
        (show 1 ≤ tm63Length1+2 by omega)
      simpa using h
    omega
  have hk : 0 < k := by
    dsimp [k]
    exact Nat.mul_pos (Nat.pow_pos (by decide)) hC
  have hpow :
      2^(rootMarker1A-1) = 2*2^(rootMarker1A-2) := by
    rw [show rootMarker1A-1 = (rootMarker1A-2)+1 by omega,
      Nat.pow_succ]
    omega
  have hprod :
      2^(rootMarker1A-1) * (2^(tm63Length1+2)-1) = 2*k := by
    calc
      2^(rootMarker1A-1) * (2^(tm63Length1+2)-1) =
          (2*2^(rootMarker1A-2)) * (2^(tm63Length1+2)-1) := by
            rw [hpow]
      _ = 2 * (2^(rootMarker1A-2) * (2^(tm63Length1+2)-1)) := by
            rw [Nat.mul_assoc]
      _ = 2*k := by rfl
  have hq :
      firstQ4P1Value tm63Length1 rootMarker1A = 2*(k-1)+1 := by
    unfold firstQ4P1Value
    rw [hprod]
    omega
  rw [hq]
  omega

/-- The authentic root's first-q4 P1 value satisfies the odd-q hypothesis
of Agent 24's second-prefix composition. -/
theorem rootP1Value_odd_public :
    firstQ4P1Value tm63Length1 rootMarker1A % 2 = 1 :=
  rootP1Value_odd

/-- Extend the authentic blank-root trajectory through the second q4 prefix
to the q4Tail frame.  The second-prefix suffix is extracted from Agent 24's
full first-cycle-plus-second-prefix theorem using the already available
first-cycle run; no local tape guards are reproved here. -/
theorem tm63_blank_reaches_second_q4_tail :
    run tm2
      (rootToSecondQ4Cost + rootSecondQ4TailPrefixCost)
      blank =
    some (shiftConfig rootMarker1Head rootSecondQ4TailFrame) := by
  let z : Nat := rootMarker1Z
  let w : Nat := firstQ4P1Width tm63Length1 rootMarker1A
  let q : Nat := firstQ4P1Value tm63Length1 rootMarker1A
  let a : Nat := 2^z-1
  let m : Nat := 3*2^z+3*z+7
  let n : Nat := 2^a
  let C1 : Nat :=
    (3*2^z+3*z+58) +
      ((6*4^a+42*2^a-12*a-48)+(9*2^z+9*z+16))
  let C2 : Nat := 34+m+2+3*n+29
  let c : Config := ⟨4,1,firstCycleCheckpointTape z w q⟩
  let V : Config := rootSecondQ4Frame
  let F : Config := rootSecondQ4TailFrame

  have hz : 1 ≤ z := by
    dsimp [z]
    exact le_trans (by decide) rootMarker1Z_ge_three
  have hqBound : q < 2^w := by
    dsimp [q,w]
    exact firstQ4P1Value_lt tm63Length1 rootMarker1A rootMarker1A_pos
  have hqOdd : q % 2 = 1 := by
    exact rootP1Value_odd

  have hfirst :
      run tm2 C1 c = some V := by
    have h := positiveZFirstCycle_from_checkpoint z w q hz hqBound
    simpa [C1,c,V,z,w,q,a,rootSecondQ4Frame] using h

  have hfull :
      run tm2 (C1+C2) c = some F := by
    have h := positiveZFirstCycle_then_secondCyclePrefix
      z w q hz hqBound hqOdd
    simpa [C1,C2,c,F,z,w,q,a,m,n,rootSecondQ4TailFrame,
      rootSecondQ4Frame] using h

  have hsplit :
      run tm2 (C1+C2) c = run tm2 C2 V := by
    rw [run_append,hfirst]
    simp only [Option.bind_some]

  have hsecond :
      run tm2 C2 V = some F := by
    rw [← hsplit]
    exact hfull

  have hsecondShift :
      run tm2 C2 (shiftConfig rootMarker1Head V) =
        some (shiftConfig rootMarker1Head F) := by
    calc
      run tm2 C2 (shiftConfig rootMarker1Head V) =
          (run tm2 C2 V).map (shiftConfig rootMarker1Head) := by
            exact shift_run rootMarker1Head tm2 V C2
      _ = some (shiftConfig rootMarker1Head F) := by
            rw [hsecond]

  have hroot :
      run tm2 rootToSecondQ4Cost blank =
        some (shiftConfig rootMarker1Head V) := by
    simpa [V] using tm63_blank_reaches_second_q4_frame

  have hcost : rootSecondQ4TailPrefixCost = C2 := by
    simp [rootSecondQ4TailPrefixCost,C2,z,m,n,a]

  calc
    run tm2 (rootToSecondQ4Cost+rootSecondQ4TailPrefixCost) blank =
        (run tm2 rootToSecondQ4Cost blank).bind
          (fun d => run tm2 rootSecondQ4TailPrefixCost d) := by
            rw [run_append]
    _ = run tm2 rootSecondQ4TailPrefixCost
          (shiftConfig rootMarker1Head V) := by
            rw [hroot]
            simp only [Option.bind_some]
    _ = some (shiftConfig rootMarker1Head F) := by
          rw [hcost]
          exact hsecondShift

#print axioms rootP1Value_odd_public
#print axioms tm63_blank_reaches_second_q4_tail

end BB6Coverage.Agent38RootQ4Tail
