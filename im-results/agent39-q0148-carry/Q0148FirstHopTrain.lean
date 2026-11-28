import Q0148RightMarkerWord
import Q0148LowMarkerTrain
import Lean.Elab.Tactic.Omega

/-!
# Exact source from FIRST next E1 to the FAR-RIGHT boundary E1

For an arbitrary finite right-marker list, the original F1-open
Raw11 q0-148 table has a positive first marked hop from a leftmost
group, then the general high/low arbitrary train. The head-height
constraint j0 = (number of remaining markers)+1 (high) or
j0 = (number of ordinary pre hops)+1 (low) is the same as the
abstract P invariant after the blank reset. No finite simulation,
source semantics replacement, or source unverified abstract F step.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

def firstIndex (j n : Nat) : HopIndex := ⟨n,[],j-1⟩

def firstHopCost (j n : Nat) : Nat :=
  (4 + 4*scanCost (aRun (j+2))) + (13+2*n)

/-- Source qE first marker, no previously crossed left markers,
    and an arbitrary finite right-marker list starting with n.
    Exactly two left blanks per future E1 hop are explicitly reserved. -/
def firstMarkerState (j : Nat) (ns : List Nat)
    (L R : List Bool) : Z0 :=
  ⟨4,[true,false] ++ inputBits (aRun (j+2)) ++
       leftPad ns.length ++ L,
     [false] ++ rightMarkers ns R⟩

/-- First E1 marked hop inserts the far-left marker and produces the
    ordinary train frame, provided the active index is >=3 (j>=1).
    All original-source tape tails remain explicit. -/
theorem firstIntoTrain_source (j n : Nat) (ns : List Nat)
    (L R : List Bool) (hj : 1 ≤ j) :
    run0 p (firstHopCost j n)
      (firstMarkerState j (n::ns) L R) =
    some (markerState (firstIndex j n) ns L R) := by
  cases j with
  | zero => omega
  | succ j =>
      have h := first_hop_source n (j+1)
        (twoPad ns.length ++ L) (rightMarkers ns R)
      simpa [firstMarkerState,firstIndex,firstHopCost,
        markerState,rightMarkers,leftPad,twoPad,gapChain,
        rep,List.append_assoc,Nat.succ_eq_add_one,
        Nat.add_assoc] using h

/-- High head-height: far-left debt equals the remaining marker
    count. Every distant source hop is ordinary. The complete
    source run reaches the final boundary frame with far-left gap 3. -/
theorem highTrainFromFirst_source (n : Nat) (ns : List Nat)
    (L R : List Bool) :
    let j := ns.length + 1
    let ix := firstIndex j n
    run0 p (firstHopCost j n + trainCost ix ns)
      (firstMarkerState j (n::ns) L R) =
    some (markerState (trainEnd ix ns) [] L R) := by
  dsimp only
  have hj : 1 ≤ ns.length+1 := by omega
  have hz : ns.length ≤ (firstIndex (ns.length+1) n).far := by
    simp [firstIndex]
  have h0 := firstIntoTrain_source (ns.length+1) n ns L R hj
  have h1 := markerTrain_source
    (firstIndex (ns.length+1) n) ns L R hz
  simpa [Nat.add_assoc] using join0 h0 h1

/-- The high endpoint's far-left old-gap countdown is exactly zero,
    hence physical far-left gap THREE. -/
theorem highTrainEnd_far (n : Nat) (ns : List Nat) :
    (trainEnd (firstIndex (ns.length+1) n) ns).far = 0 := by
  rw [trainEnd_far]
  simp [firstIndex]

/-- Low head-height: initial debt is two below the total number of
    remaining markers. The ordinary pre plus the last two hops
    reaches the FINAL source boundary with far-left gap ONE. -/
theorem lowTrainFromFirst_source
    (n : Nat) (pre : List Nat) (u v : Nat)
    (L R : List Bool) :
    let j := pre.length+1
    let ix := firstIndex j n
    let ix' := trainEnd ix pre
    run0 p
      ((firstHopCost j n + trainCost ix pre +
           markerCost ix' u) +
        shortCost u (ix'.j :: ix'.prior) v)
      (firstMarkerState j (n::pre)
        (twoPad 2 ++ L) (rightMarkers [u,v] R)) =
    some (lowTerminal v (u::ix'.j::ix'.prior) L R) := by
  dsimp only
  have hj : 1 ≤ pre.length+1 := by omega
  have h0 := firstIntoTrain_source
    (pre.length+1) n pre
    (twoPad 2 ++ L) (rightMarkers [u,v] R) hj
  have hz : (firstIndex (pre.length+1) n).far =
      pre.length := by
    simp [firstIndex]
  have h1 := lowMarkerTrain_source
    (firstIndex (pre.length+1) n) pre u v L R hz
  have h := join0 h0 h1
  simpa [Nat.add_assoc] using h

#print axioms firstIntoTrain_source
#print axioms highTrainFromFirst_source
#print axioms highTrainEnd_far
#print axioms lowTrainFromFirst_source

end BB6.Agent39Q0148Carry
