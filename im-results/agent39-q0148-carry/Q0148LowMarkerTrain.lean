import Q0148MarkerTrain
import Lean.Elab.Tactic.Omega

/-!
# All-length LOW-branch original-table E1 marker train

For a short far-left debt equal to the number of distant markers minus
TWO, the first marker hops consume the debt, the penultimate hop
creates the exact M A short tail, and the final hop closes that to M.
This explicitly composes the original table all the way through the
LAST right-hand marker, with a final far-left gap ONE. It handles an
arbitrary finite intervening marker chain, all source step counts,
and untouched tape tails. Completing the entire q0-148 nonhalting
certificate still requires aligning these generic frames with the
blank-round E1 checkpoint and proving the boundary P closure.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- The far-left countdown decreases exactly once per ordinary
    original-source marked hop, with no syntactic restriction. -/
theorem trainEnd_far (ix : HopIndex) (ns : List Nat) :
    (trainEnd ix ns).far = ix.far - ns.length := by
  induction ns generalizing ix with
  | nil => rfl
  | cons n ns ih =>
      have h := ih (nextIndex ix n)
      simpa [trainEnd,nextIndex,Nat.sub_sub,List.length_cons,
        Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

/-- The penultimate qE state, whose far-left gap is exactly two. -/
def shortState (j : Nat) (rs : List Nat) (ns : List Nat)
    (L R : List Bool) : Z0 :=
  ⟨4,[true,false] ++
       inputBits (aRun (j+2) ++ gapChain rs ++
          [.separatedMarker,.alternating]) ++
         leftPad ns.length ++ L,
     [false] ++ rightMarkers ns R⟩

/-- The terminal low qE state after ALL distant markers have been
    processed, with exactly one far-left A pair. -/
def lowTerminal (j : Nat) (rs : List Nat)
    (L R : List Bool) : Z0 :=
  ⟨4,[true,false] ++
       inputBits (aRun (j+2) ++ gapChain rs ++ [.separatedMarker]) ++
         leftPad 0 ++ L,
     [false] ++ R⟩

def shortCost (j : Nat) (rs : List Nat) (n : Nat) : Nat :=
  (4 + 4*scanCost
      (aRun (j+2) ++ gapChain rs ++
        [.separatedMarker,.alternating])) +
    (13 + 2*n)

/-- The ordinary hop starting at far debt ZERO produces the unique
    exceptional M A ending. Source time is the usual marked-hop time. -/
theorem shortPreparation_source (ix : HopIndex) (n m : Nat)
    (L R : List Bool) (hz : ix.far = 0) :
    run0 p (markerCost ix n)
      (markerState ix [n,m] L R) =
    some (shortState n (ix.j :: ix.prior) [m] L R) := by
  rcases ix with ⟨j,rs,z⟩
  subst z
  have h := prepare_two_hop_source n j rs
    (twoPad 1 ++ L) (rightMarkers [m] R)
  simpa [markerCost,markerState,shortState,gapChain,
    rightMarkers,leftPad,twoPad,rep,List.append_assoc] using h

/-- The final exceptional step closes T into a new far-left gap one
    and lands in the E1 boundary frame at the end of the marker list. -/
theorem shortFinal_source (j n : Nat) (rs : List Nat)
    (L R : List Bool) :
    run0 p (shortCost j rs n)
      (shortState j rs [n] L R) =
    some (lowTerminal n (j::rs) L R) := by
  have h := final_two_hop_source n j rs L R
  simpa [shortCost,shortState,lowTerminal,
    rightMarkers,leftPad,twoPad,gapChain,rep,
    List.append_assoc] using h

/-- The final TWO original-source hops, from far gap THREE to TWO
    to ONE, with arbitrary earlier crossed markers. -/
theorem lastTwo_source (ix : HopIndex) (n m : Nat)
    (L R : List Bool) (hz : ix.far = 0) :
    run0 p
      (markerCost ix n + shortCost n (ix.j::ix.prior) m)
      (markerState ix [n,m] L R) =
    some (lowTerminal m (n::ix.j::ix.prior) L R) := by
  have h1 := shortPreparation_source ix n m L R hz
  have h2 := shortFinal_source n m (ix.j::ix.prior) L R
  simpa [Nat.add_assoc] using join0 h1 h2

/-- Arbitrarily many preceding ordinary source hops followed by the
    final two exceptional transitions. The initial far debt equals
    the number of ordinary hops; no marker bound is assumed. -/
theorem lowMarkerTrain_source (ix : HopIndex) (prefix : List Nat)
    (n m : Nat) (L R : List Bool)
    (hz : ix.far = prefix.length) :
    let ix' := trainEnd ix prefix
    run0 p
      ((trainCost ix prefix + markerCost ix' n) +
        shortCost n (ix'.j::ix'.prior) m)
      (markerState ix prefix (twoPad 2 ++ L)
        (rightMarkers [n,m] R)) =
    some (lowTerminal m (n::ix'.j::ix'.prior) L R) := by
  dsimp only
  have hz' : prefix.length ≤ ix.far := by omega
  have h0 := markerTrain_source ix prefix
      (twoPad 2 ++ L) (rightMarkers [n,m] R) hz'
  have he : (trainEnd ix prefix).far = 0 := by
    rw [trainEnd_far,hz]
    simp
  have h1 := lastTwo_source (trainEnd ix prefix) n m L R he
  have h0' : run0 p (trainCost ix prefix)
      (markerState ix prefix (twoPad 2 ++ L)
        (rightMarkers [n,m] R)) =
    some (markerState (trainEnd ix prefix) [n,m] L R) := by
      simpa [markerState,rightMarkers,leftPad,twoPad,
        List.append_assoc] using h0
  have h := join0 h0' h1
  simpa [Nat.add_assoc] using h

#print axioms trainEnd_far
#print axioms shortPreparation_source
#print axioms shortFinal_source
#print axioms lastTwo_source
#print axioms lowMarkerTrain_source

end BB6.Agent39Q0148Carry
