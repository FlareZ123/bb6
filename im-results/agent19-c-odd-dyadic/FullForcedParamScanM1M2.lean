import FullForcedParamScan

namespace BB6.Agent19ParamScan
open BB6.Agent3FullForcedScan

/-- Candidate j values by fixed m, reusing the exact finite scan and its
    prior-sieve admission predicate. This is a discovery diagnostic only. -/
def jsFor (m : Nat) : List Nat :=
  (additionalPairs.filter fun p => p.2=m).map Prod.fst

/-- Terminal states after the exact four-sector normalizer for each
    candidate in a fixed m row. -/
def normalizedFor (m : Nat) : List (Nat × Nat × Nat) :=
  (additionalPairs.filter fun p => p.2=m).map fun (j,_) =>
    let p := BB6.Agent3.fullForcedNormalize
      (BB6.Agent3FullForcedResidual.highTargetX j)
      (BB6.Agent3FullForcedResidual.highTargetY j m)
    (j,p.1,p.2)

/-- The seven simple m=0 progressions already formalized. -/
def knownM0Family (j : Nat) : Bool :=
  j%8==3 ||
  (j%16==2 && decide (18≤j)) ||
  j%32==6 ||
  j%64==58 ||
  j%32==21 ||
  j%32==15 ||
  j%128==71 ||
  (j%128==5 && decide (128≤j)) ||
  j%512==357 ||
  j%512==406 ||
  j%512==191

def uncoveredM0 : List Nat :=
  (jsFor 0).filter fun j => !(knownM0Family j)

def uncoveredM0Normalized : List (Nat × Nat × Nat) :=
  (normalizedFor 0).filter fun p => !(knownM0Family p.1)

#eval s!"m=0 uncovered j ({uncoveredM0.length}) = {uncoveredM0}"
#eval s!"m=0 uncovered normalized = {uncoveredM0Normalized}"
#eval s!"m=1 j candidates ({(jsFor 1).length}) = {jsFor 1}"
#eval s!"m=2 j candidates ({(jsFor 2).length}) = {jsFor 2}"
#eval s!"m=3 j candidates ({(jsFor 3).length}) = {jsFor 3}"
#eval s!"m=4 j candidates ({(jsFor 4).length}) = {jsFor 4}"
#eval s!"m=5 j candidates ({(jsFor 5).length}) = {jsFor 5}"
#eval s!"m=1 normalized = {(normalizedFor 1).take 80}"
#eval s!"m=2 normalized = {(normalizedFor 2).take 80}"
#eval s!"m=4 normalized = {(normalizedFor 4).take 80}"

end BB6.Agent19ParamScan
