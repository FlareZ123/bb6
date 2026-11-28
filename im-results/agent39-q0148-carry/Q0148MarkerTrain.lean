import Q0148ExceptionalSourceHop
import Lean.Elab.Tactic.Omega

/-!
# Arbitrarily long source-defined train of marked E1 hops (high branch)

This is a source-level composition of the EXACT original Raw11 q0-148
partial table, not an inferred diagram. The head passes through any
finite list of future right-side 110 markers, with arbitrarily large
untouched gaps and arbitrary old left gaps >=3. The far-left gap has
a finite "debt" z: each hop decreases it by one. If z is at least
the number of future markers, no terminal exception occurs and the
whole train is an explicitly defined, strictly positive run.
The low branch needs the exceptional gap-two splice separately.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- Exactly 2n blank zeros reserved for n more source marker hops. -/
def twoPad : Nat → List Bool
  | 0 => []
  | n+1 => [false,false] ++ twoPad n

/-- Always at least one blank left-end bit, with two more per hop. -/
def leftPad (n : Nat) : List Bool := [false] ++ twoPad n

/-- Arbitrary distant right-side 110 markers; the n-th gap is n+1
    alternating 10 pairs. A right-suffix R is completely untouched. -/
def rightMarkers : List Nat → List Bool → List Bool
  | [],R => R
  | n::ns,R =>
      rep [true,false] (n+1) ++ [true,true,false] ++
        rightMarkers ns R

theorem rightMarkers_append (xs ys : List Nat) (R : List Bool) :
    rightMarkers (xs ++ ys) R =
      rightMarkers xs (rightMarkers ys R) := by
  induction xs with
  | nil => rfl
  | cons n xs ih =>
      simp [rightMarkers,ih,List.append_assoc]

structure HopIndex where
  j : Nat
  prior : List Nat
  far : Nat
  deriving DecidableEq, Repr

def markerState (ix : HopIndex) (ns : List Nat)
    (L R : List Bool) : Z0 :=
  ⟨4,[true,false] ++
      inputBits (aRun (ix.j+2) ++ gapChain (ix.prior ++ [ix.far])) ++
        leftPad ns.length ++ L,
     [false] ++ rightMarkers ns R⟩

def markerCost (ix : HopIndex) (n : Nat) : Nat :=
  (4 + 4*scanCost
     (aRun (ix.j+2) ++ gapChain (ix.prior ++ [ix.far]))) +
    (13 + 2*n)

def nextIndex (ix : HopIndex) (n : Nat) : HopIndex :=
  ⟨n, ix.j :: ix.prior, ix.far-1⟩

/-- Source macro join for one step in the marker train. Positive
    far debt ensures the new left boundary remains >=3 and can
    re-enter the same source theorem at the next marker. -/
theorem markerStep (ix : HopIndex) (n : Nat) (ns : List Nat)
    (L R : List Bool) (hfar : ix.far > 0) :
    run0 p (markerCost ix n)
       (markerState ix (n::ns) L R) =
      some (markerState (nextIndex ix n) ns L R) := by
  rcases ix with ⟨j,rs,z⟩
  cases z with
  | zero => omega
  | succ z =>
      have h := ordinary_hop_source n j rs (z+1)
        (twoPad ns.length ++ L) (rightMarkers ns R)
      simpa [markerState,markerCost,nextIndex,rightMarkers,
        leftPad,twoPad,gapChain,rep,List.append_assoc,
        Nat.succ_eq_add_one,Nat.add_assoc] using h

/-- Exact total source time over a finite remaining marker train. -/
def trainCost (ix : HopIndex) : List Nat → Nat
  | [] => 0
  | n::ns => markerCost ix n + trainCost (nextIndex ix n) ns

/-- Final syntactic index after passing an arbitrary finite train. -/
def trainEnd (ix : HopIndex) : List Nat → HopIndex
  | [] => ix
  | n::ns => trainEnd (nextIndex ix n) ns

/-- Whole train of original-machine E1 marker hops, with its exact
    source time and explicitly constructed final head/tape state.
    No bound on the number of markers, gap lengths, or external tails.
    The proof is mathematical induction over the marker list. -/
theorem markerTrain_source (ix : HopIndex) (ns : List Nat)
    (L R : List Bool) (hfar : ns.length ≤ ix.far) :
    run0 p (trainCost ix ns) (markerState ix ns L R) =
      some (markerState (trainEnd ix ns) [] L R) := by
  induction ns generalizing ix with
  | nil =>
      simp [trainCost,trainEnd,run0]
  | cons n ns ih =>
      have hp : ix.far > 0 := by
        simpa only [List.length_cons] at hfar
        omega
      have hn : ns.length ≤ (nextIndex ix n).far := by
        simp only [nextIndex]
        simpa only [List.length_cons] at hfar
        omega
      have h1 := markerStep ix n ns L R hp
      have h2 := ih (nextIndex ix n) hn
      have h := join0 h1 h2
      simpa [trainCost,trainEnd,Nat.add_assoc] using h

/-- Every nonempty marker train executes strictly more than one
    original transition, so it is a genuine progress witness. -/
theorem markerTrain_positive (ix : HopIndex) (n : Nat) (ns : List Nat) :
    0 < trainCost ix (n::ns) := by
  simp [trainCost,markerCost]
  omega

#print axioms rightMarkers_append
#print axioms markerStep
#print axioms markerTrain_source
#print axioms markerTrain_positive

end BB6.Agent39Q0148Carry
