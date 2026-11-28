import Q0148ResetToTrain
import Lean.Elab.Tactic.Omega

/-!
# Whole high/low source boundary epoch, connecting exact reset to
# the arbitrary marker-train source induction

No abstract F assumption: every asserted TM transition is a
composition of the original F1-open partial machine's run0 theorem.
The remaining paper/Lean bridge is the algebraic identification of
the initial physical stable boundary word and the final output gaps.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- Actual qE high-branch source return, given ANY certified source
    reset into its first E1 state. No limit on right-marker count. -/
theorem high_from_reset (t : Nat) (start : Z0)
    (first : Nat) (rest : List Nat) (L R : List Bool)
    (hreset : run0 p t start =
        some (firstMarkerState (rest.length+1) (first::rest) L R)) :
    run0 p
      (t + (firstHopCost (rest.length+1) first +
        trainCost (firstIndex (rest.length+1) first) rest))
      start =
    some (markerState (trainEnd
      (firstIndex (rest.length+1) first) rest) [] L R) := by
  have h := highTrainFromFirst_source first rest L R
  dsimp only at h
  simpa only [Nat.add_assoc] using join0 hreset h

/-- The extra two right markers of the low branch have to be
    passed as a *suffix* to the ordinary prefix; both source
    configurations are literally identical. -/
theorem twoPad_append (a b : Nat) :
    twoPad (a+b) = twoPad a ++ twoPad b := by
  induction a with
  | zero => rfl
  | succ a ih =>
      simp [twoPad,ih,List.append_assoc,Nat.succ_add]

theorem low_first_state_split (j first : Nat) (prefix : List Nat)
    (u v : Nat) (L R : List Bool) :
    firstMarkerState j (first :: (prefix ++ [u,v])) L R =
    firstMarkerState j (first::prefix)
       (twoPad 2 ++ L) (rightMarkers [u,v] R) := by
  have hlen : (first :: (prefix ++ [u,v])).length =
      (first::prefix).length + 2 := by simp
  have ht :
      leftPad ((first :: (prefix ++ [u,v])).length) ++ L =
      leftPad (first::prefix).length ++ twoPad 2 ++ L := by
    rw [hlen]
    simp [leftPad,twoPad_append,List.append_assoc]
  have hr := rightMarkers_append (first::prefix) [u,v] R
  simpa only [firstMarkerState,List.append_assoc,
    rightMarkers_append,ht] using congrArg
      (fun v : List Bool =>
        ([true,false] ++ inputBits (aRun (j+2)) ++ v))
      ht

/-- Source low-branch epoch: arbitrary number of ordinary middle
    hops and the final two exceptional low-end hops, all exact. -/
theorem low_from_reset (t : Nat) (start : Z0)
    (first : Nat) (prefix : List Nat) (u v : Nat)
    (L R : List Bool)
    (hreset : run0 p t start =
      some (firstMarkerState (prefix.length+1)
        (first::(prefix++[u,v])) L R)) :
    let ix := firstIndex (prefix.length+1) first
    let ix' := trainEnd ix prefix
    run0 p
      (t + ((firstHopCost (prefix.length+1) first +
          trainCost ix prefix + markerCost ix' u) +
          shortCost u (ix'.j::ix'.prior) v))
      start =
    some (lowTerminal v (u::ix'.j::ix'.prior) L R) := by
  dsimp only
  have hs := low_first_state_split
    (prefix.length+1) first prefix u v L R
  rw [hs] at hreset
  have h := lowTrainFromFirst_source
    first prefix u v L R
  dsimp only at h
  simpa [Nat.add_assoc] using join0 hreset h

/-- Source return in the a=1 HIGH case, where the next source
    reset has g1 equal to the TOTAL number of forthcoming markers. -/
theorem a1_high_epoch_source (us : List Nat) (n first : Nat)
    (rest : List Nat) (L R : List Bool)
    (hps : a1FutureMarkers us = first::rest)
    (hj : 2*n+1 = rest.length+1) :
    run0 p
      ((a1FirstTime us.reverse n + (2*(2*n)+6)) +
        (firstHopCost (rest.length+1) first +
          trainCost (firstIndex (rest.length+1) first) rest))
      ⟨4,[true,false] ++ inputBits (a1Input us.reverse n) ++
          [false,false,false,false] ++
            leftPad (a1FutureMarkers us).length ++ L,
         [false,true,false,false,false] ++ R⟩ =
    some (markerState (trainEnd
      (firstIndex (rest.length+1) first) rest)
      [] L ([true,false] ++ R)) := by
  have hreset := a1_reset_to_train us n L R
  dsimp only at hreset
  rw [hps,hj] at hreset
  have h := high_from_reset
    (a1FirstTime us.reverse n + (2*(2*n)+6))
    ⟨4,[true,false] ++ inputBits (a1Input us.reverse n) ++
         [false,false,false,false] ++
           leftPad (first::rest).length ++ L,
        [false,true,false,false,false] ++ R⟩
    first rest L ([true,false] ++ R) hreset
  simpa [hps, Nat.add_assoc] using h

/-- Source return in the a=3 HIGH case; three extra right-end
    marker gaps are supported with no change in the proof. -/
theorem a3_high_epoch_source (us : List Nat) (n first : Nat)
    (rest : List Nat) (L R : List Bool)
    (hps : a3FutureMarkers us = first::rest)
    (hj : 2*n+1 = rest.length+1) :
    run0 p
      (((((a3FirstTime (us.reverse ++ [n]) +
          a3SecondTime (us.reverse ++ [n])) +
          a3ThirdTime (us.reverse ++ [n])) + (2*(2*n)+6))) +
        (firstHopCost (rest.length+1) first +
          trainCost (firstIndex (rest.length+1) first) rest))
      ⟨4,[true,false] ++ inputBits (a3Input (us.reverse ++ [n])) ++
          [false,false,false,false,false,false,false,false] ++
            leftPad (a3FutureMarkers us).length ++ L,
         [false,true,false,false,false,false,false,false] ++ R⟩ =
    some (markerState (trainEnd
      (firstIndex (rest.length+1) first) rest)
      [] L ([true,false,false] ++ R)) := by
  have hreset := a3_reset_to_train us n L R
  dsimp only at hreset
  rw [hps,hj] at hreset
  have h := high_from_reset
    (((a3FirstTime (us.reverse ++ [n]) +
          a3SecondTime (us.reverse ++ [n])) +
          a3ThirdTime (us.reverse ++ [n])) + (2*(2*n)+6))
    ⟨4,[true,false] ++ inputBits (a3Input (us.reverse ++ [n])) ++
          [false,false,false,false,false,false,false,false] ++
            leftPad (first::rest).length ++ L,
         [false,true,false,false,false,false,false,false] ++ R⟩
    first rest L ([true,false,false] ++ R) hreset
  simpa [hps,Nat.add_assoc] using h

#print axioms high_from_reset
#print axioms twoPad_append
#print axioms low_first_state_split
#print axioms low_from_reset
#print axioms a1_high_epoch_source
#print axioms a3_high_epoch_source

end BB6.Agent39Q0148Carry
