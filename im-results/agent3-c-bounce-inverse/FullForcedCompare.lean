import FullForcedFilter
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3Compare
open BB6.Agent3

/-- The pre-extension three-sector normalizer, retained here as a finite
    comparison baseline. The four-sector normalizer itself is imported from
    the source-certified FullForcedFilter/FullForcedNormalize modules. -/
def fullForcedNormalizeThree (x y : Nat) : Nat × Nat :=
  if h : oddLowGate x y then
    fullForcedNormalizeThree ((x+y-4)/2) ((x+3*y-10)/4)
  else if he : evenSevenGate x y then
    fullForcedNormalizeThree ((x+y-5)/2) ((x+3*y-9)/4)
  else if hf : evenAffineGate x y then
    fullForcedNormalizeThree (x+y-2) ((y-2)/2)
  else (x,y)
termination_by x+2*y
decreasing_by
  all_goals
    simp_wf
    simp only [oddLowGate,evenSevenGate,evenAffineGate] at *
    omega

def oldExcluded (j m : Nat) : Bool :=
  let p := fullForcedNormalizeThree (2*j+3)
    (2^(2*m+2)*(j+3)-(j+3*m+5))
  decide (5≤p.2 ∧ p.2%2=1 ∧
    ((p.1+p.2)%4=1 ∨ (p.1+p.2)%4=2))

/-- This calls the actual four-sector source normalizer and sound filter. -/
def newExcluded (j m : Nat) : Bool :=
  fullForcedExcluded (2*j+3)
    (2^(2*m+2)*(j+3)-(j+3*m+5))

def parameterPairs : List (Nat × Nat) :=
  (List.range 33).flatMap fun mi =>
    (List.range 256).map fun j => (j,mi+3)

def oldCount : Nat :=
  (parameterPairs.filter fun (j,m) => oldExcluded j m).length

def newCount : Nat :=
  (parameterPairs.filter fun (j,m) => newExcluded j m).length

def addedCount : Nat :=
  (parameterPairs.filter fun (j,m) =>
    newExcluded j m && !oldExcluded j m).length

def addedExamples : List (Nat × Nat) :=
  (parameterPairs.filter fun (j,m) =>
    newExcluded j m && !oldExcluded j m).take 20

#eval s!"targets={parameterPairs.length}"
#eval s!"three-sector excluded={oldCount}"
#eval s!"four-sector excluded={newCount}"
#eval s!"additional exclusions={addedCount}"
#eval s!"first additional (j,m) pairs={addedExamples}"

-- Regression guards for the exact finite enumeration. These are not a
-- universal nonreachability theorem; the sound theorem is
-- fullForcedExcluded_sound in FullForcedFilter.lean.
#guard parameterPairs.length == 8448
#guard oldCount == 3208
#guard newCount == 4517
#guard addedCount == 1309

end BB6.Agent3Compare
