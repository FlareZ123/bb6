import Q0148FirstHopTrain
import Q0148FirstMarkerReturn
import Q0148RightMarkerWord
import Lean.Elab.Tactic.Omega

/-!
# Exact original boundary reset connects to arbitrary source marker train

Agent5's original-table a=1/a=3 E1 return macros are now composed
with the full right-marker source grammar (not inferred tape vectors).
This identifies the first E1 after a blank right turn as the input of
the all-depth high/low marked-hop source induction. No bounded test
assumption and no abstract TM transition replacement.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- The source A0-to-E1 sweep's alternating left output completes
    one final A when the first untouched cell is a blank zero. -/
theorem first_e1_left_word (n : Nat) (L : List Bool) :
    [true,false,true] ++ rep [false,true] (2*n+1) ++
      [false,true,false] ++ L =
    [true,false] ++ inputBits (aRun ((2*n+1)+2)) ++ L := by
  have h := stagger01 (2*n+1)
  have hn : (2*n+1)+2 = (2*n+2)+1 := by omega
  have hrep : rep [true,false] ((2*n+1)+2) =
      [true,false] ++ rep [true,false] (2*n+2) := by
    rw [hn]
    rfl
  simpa [input_aRun,rep,List.append_assoc] using
    congrArg
      (fun x : List Bool => x ++ [false,true,false] ++ L) h

def a1FutureMarkers (us : List Nat) : List Nat :=
  us.map (fun u => 2*u) ++ [0]

def a3FutureMarkers (us : List Nat) : List Nat :=
  us.map (fun u => 2*u) ++ [0,0,0]

/-- No unproved assumption about the physical tape: the original
    qE source output after TWO blank turns and A0-to-E1 is exactly
    the generic first E1 source marker-train state, for arbitrary
    interior source gap sequence `us` and untouched outer tails. -/
theorem a1_reset_to_train (us : List Nat) (n : Nat)
    (L R : List Bool) :
    let ps := a1FutureMarkers us
    run0 p (a1FirstTime us.reverse n + (2*(2*n)+6))
      ⟨4,[true,false] ++ inputBits (a1Input us.reverse n) ++
          [false,false,false,false] ++ leftPad ps.length ++ L,
         [false,true,false,false,false] ++ R⟩ =
    some (firstMarkerState (2*n+1) ps L
       ([true,false] ++ R)) := by
  dsimp only
  have h := a1_first_e1_source us.reverse n
    ([false] ++ leftPad (a1FutureMarkers us).length ++ L) R
  have hr := a1_reset_right_markers us
  have hl := first_e1_left_word n
    (leftPad (a1FutureMarkers us).length ++ L)
  simpa [a1FutureMarkers,firstMarkerState,
    List.append_assoc,hl,hr] using h

/-- THREE blank-turn rounds in the a=3 case, followed by the same
    exact A0-to-E1, produce THREE short right-end markers. -/
theorem a3_reset_to_train (us : List Nat) (n : Nat)
    (L R : List Bool) :
    let ps := a3FutureMarkers us
    run0 p
      (((a3FirstTime (us.reverse ++ [n]) +
          a3SecondTime (us.reverse ++ [n])) +
          a3ThirdTime (us.reverse ++ [n])) + (2*(2*n)+6))
      ⟨4,[true,false] ++ inputBits (a3Input (us.reverse ++ [n])) ++
           [false,false,false,false,false,false,false,false] ++
              leftPad ps.length ++ L,
         [false,true,false,false,false,false,false,false] ++ R⟩ =
    some (firstMarkerState (2*n+1) ps L
      ([true,false,false] ++ R)) := by
  dsimp only
  have h := a3_first_e1_source us.reverse n
    ([false] ++ leftPad (a3FutureMarkers us).length ++ L) R
  have hr := a3_reset_right_markers us
  have hl := first_e1_left_word n
    (leftPad (a3FutureMarkers us).length ++ L)
  simpa [a3FutureMarkers,firstMarkerState,
    List.append_assoc,hl,hr] using h

/-- Both source-reset channels have a nonempty list of future 110
    markers (one extra for a1, three for a3). -/
theorem a1_future_nonempty (us : List Nat) :
    (a1FutureMarkers us).length > 0 := by
  simp [a1FutureMarkers]

theorem a3_future_nonempty (us : List Nat) :
    (a3FutureMarkers us).length ≥ 3 := by
  simp [a3FutureMarkers]

#print axioms first_e1_left_word
#print axioms a1_reset_to_train
#print axioms a3_reset_to_train
#print axioms a1_future_nonempty
#print axioms a3_future_nonempty

end BB6.Agent39Q0148Carry
