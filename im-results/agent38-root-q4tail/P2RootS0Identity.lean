import P2RootS0FrameIdentity
import Q4TailToNextQ4Tail
import Lean.Elab.Tactic.Omega

/-!
# One further q4Tail recurrence from the authentic S0 frame

The source-side frame identity is isolated in P2RootS0FrameIdentity.lean.
Direct terminal compositions should import that frame-only module rather
than this recurrence wrapper, avoiding the unrelated P2 next-tail path.
-/ 

namespace BB6Coverage.Agent38RootQ4TailS0

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent48PositiveZFirstCycle
open BB6Coverage.Agent48PositiveZSecondCyclePrefix
open BB6Coverage.Agent42PositiveZFirstCycleS0Input
open BB6Coverage.Agent42Q4S0Drain
open BB6Coverage.Agent42Q4TailToS0Frame
open BB6Coverage.Agent42Q4TailToNextQ4Tail
open BB6Coverage.Agent44P2Postlude
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent48RootSecondQ4Frame
open BB6Coverage.Agent38RootQ4Tail


set_option maxHeartbeats 5000000

/-- The next q4Tail frame obtained by the generic S0 postlude and first
positive-z prefix. -/
def q4TailS0NextFrame (z w q : Nat) : Config :=
  let a := 2^z-1
  let n := 2^a
  let m := 3*2^z+3*z+7
  let H := m+2+3*n
  let tail := q4TailS0Tail w q
  let P := p2PostludeFrame m n tail
  let T1 := (frameAt P.tape 1
    firstCyclePrefix22Inside firstCyclePrefix22End).tape
  let h1 : Int := 1+4+(H:Int)
  let T2 := afterFirstCycleTwoZero T1 h1
  let h2 : Int := h1+2
  let nNext := 2^(n-1)
  let T3 := d0Sweep nNext T2 h2
  let g : Int := h2+3*(nNext:Int)
  frameAt T3 g q4TailInside q4TailEnd

/-- Exact cost of one generic q4Tail-to-q4Tail recurrence after the
authentic second-cycle residual has been identified. -/
def q4TailS0NextCost (z : Nat) : Nat :=
  let a := 2^z-1
  let n := 2^a
  let m := 3*2^z+3*z+7
  let H := m+2+3*n
  let nNext := 2^(n-1)
  (6*4^(n-1)+42*2^(n-1)-12*(n-1)-48) +
    (3*H-5) + (22+H+2+3*nNext+29)


/-- One full source-level q4Tail-to-q4Tail recurrence from the authentic
second q4Tail frame. -/
theorem q4TailS0Frame_to_nextQ4Tail
    (z w q : Nat) (hz : 1≤z) :
    run tm2 (q4TailS0NextCost z) (q4TailS0Frame z w q) =
      some (q4TailS0NextFrame z w q) := by
  let a : Nat := 2^z-1
  let n : Nat := 2^a
  let m : Nat := 3*2^z+3*z+7
  let h : Int := m+7
  let tail := q4TailS0Tail w q
  let T := q4TailS0InputTape z w q
  have hg := q4TailS0SourceGuards z w q hz
  have hn : 2≤n := by
    have hp := Nat.pow_le_pow_right (by decide : 0<2)
      (show 1≤a by dsimp [a]; omega)
    simpa [n] using hp
  have hhead : h=(m:Int)+7 := by rfl
  have hstep := q4Tail_to_next_q4Tail m n tail T h
    hn hg.1 hg.2.1 hg.2.2.1 hhead
    hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2
  simpa [q4TailS0NextCost,q4TailS0Frame,q4TailS0NextFrame,
    q4TailS0InputTape,a,n,m,h,tail,T] using hstep

/-- The authentic blank-root TM63 trajectory reaches one further q4Tail
frame after the generic S0 drain/postlude and next prefix. -/
theorem tm63_blank_reaches_next_q4Tail :
    let w := firstQ4P1Width tm63Length1 rootMarker1A
    let q := firstQ4P1Value tm63Length1 rootMarker1A
    run tm2
      (rootToSecondQ4Cost + rootSecondQ4TailPrefixCost +
        q4TailS0NextCost rootMarker1Z) blank =
      some (shiftConfig rootMarker1Head
        (q4TailS0NextFrame rootMarker1Z w q)) := by
  let w := firstQ4P1Width tm63Length1 rootMarker1A
  let q := firstQ4P1Value tm63Length1 rootMarker1A
  have hz : 1≤rootMarker1Z :=
    le_trans (by decide) rootMarker1Z_ge_three
  have hroot := tm63_blank_reaches_second_q4_tail
  have hframe := tm63_root_second_q4Tail_eq_q4TailS0Frame
  have hstep := q4TailS0Frame_to_nextQ4Tail rootMarker1Z w q hz
  have hstepRoot :
      run tm2 (q4TailS0NextCost rootMarker1Z) rootSecondQ4TailFrame =
        some (q4TailS0NextFrame rootMarker1Z w q) := by
    simpa [w,q,← hframe] using hstep
  have hstepShift :
      run tm2 (q4TailS0NextCost rootMarker1Z)
        (shiftConfig rootMarker1Head rootSecondQ4TailFrame) =
      some (shiftConfig rootMarker1Head
        (q4TailS0NextFrame rootMarker1Z w q)) := by
    calc
      run tm2 (q4TailS0NextCost rootMarker1Z)
          (shiftConfig rootMarker1Head rootSecondQ4TailFrame) =
        (run tm2 (q4TailS0NextCost rootMarker1Z)
          rootSecondQ4TailFrame).map (shiftConfig rootMarker1Head) := by
            exact shift_run rootMarker1Head tm2 rootSecondQ4TailFrame
              (q4TailS0NextCost rootMarker1Z)
      _ = some (shiftConfig rootMarker1Head
          (q4TailS0NextFrame rootMarker1Z w q)) := by
            rw [hstepRoot]
  have htotal :
      rootToSecondQ4Cost + rootSecondQ4TailPrefixCost +
        q4TailS0NextCost rootMarker1Z =
      (rootToSecondQ4Cost + rootSecondQ4TailPrefixCost) +
        q4TailS0NextCost rootMarker1Z := by omega
  rw [htotal,run_append]
  rw [hroot]
  simp only [Option.bind_some]
  exact hstepShift

#print axioms q4TailS0SourceGuards
#print axioms q4TailS0Frame_eq_s0Config
#print axioms q4TailS0Frame_to_nextQ4Tail
#print axioms tm63_blank_reaches_next_q4Tail

end BB6Coverage.Agent38RootQ4TailS0
