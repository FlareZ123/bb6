import FullForcedEvenChildExtension

namespace BB6.Agent4EvenChildScan

open BB6.Agent3FullForcedResidual
open BB6.Agent4EvenChildExtension

def gatePairs : List (Nat × Nat) :=
  (highPairs 2000 20).filter (fun (j,m) =>
    highAllowedC23WithEvenRightBool j m &&
      evenChildGate (highTargetX j) (highTargetY j m))

def fifthOnlyPairs : List (Nat × Nat) :=
  (highPairs 2000 20).filter (fun (j,m) =>
    highAllowedC23WithEvenRightBool j m &&
      !(BB6.Agent3.fullForcedExcluded (highTargetX j) (highTargetY j m)) &&
      evenChildGate (highTargetX j) (highTargetY j m) &&
      BB6.Agent3.fullForcedExcluded
        (evenChildParent (highTargetX j) (highTargetY j m)).1
        (evenChildParent (highTargetX j) (highTargetY j m)).2)

def gateParentOpenPairs : List (Nat × Nat) :=
  gatePairs.filter (fun (j,m) =>
    !(BB6.Agent3.fullForcedExcluded
      (evenChildParent (highTargetX j) (highTargetY j m)).1
      (evenChildParent (highTargetX j) (highTargetY j m)).2))

def evenChildAB (j m : Nat) : Bool :=
  let x := highTargetX j
  let y := highTargetY j m
  (x%16==3 && y%32==16) || (x%16==11 && y%32==0)

def abPairs : List (Nat × Nat) :=
  (highPairs 2000 20).filter (fun (j,m) =>
    highAllowedC23WithEvenRightBool j m &&
      evenChildAB j m &&
      !(BB6.Agent3.fullForcedExcluded (highTargetX j) (highTargetY j m)))

def countByM (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  (List.range 21).map (fun m =>
    (m,(xs.filter (fun p => p.2==m)).length))

def countByMResidue32 (xs : List (Nat × Nat)) : List (Nat × List Nat) :=
  (List.range 21).map (fun m =>
    (m,(List.range 32).map (fun r =>
      (xs.filter (fun p => p.2==m && p.1%32==r)).length)))

def normalizedExamples : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  (fifthOnlyPairs.take 80).map (fun (j,m) =>
    let x := highTargetX j
    let y := highTargetY j m
    let p := evenChildParent x y
    (j,m,x,y,p.1,p.2))

def agent19M1Pairs : List (Nat × Nat) :=
  (highPairs 2000 20).filter (fun (j,m) =>
    m==1 && j%32==24 && highAllowedC23WithEvenRightBool j m)

def agent19M2Pairs : List (Nat × Nat) :=
  (highPairs 2000 20).filter (fun (j,m) =>
    m==2 && j%32==9 && highAllowedC23WithEvenRightBool j m)

#eval s!"old high-sieve candidates = {((highPairs 2000 20).filter (fun (j,m) => highAllowedC23WithEvenRightBool j m)).length}"
#eval s!"even-child gate candidates = {gatePairs.length}"
#eval s!"fifth-only new exclusions = {fifthOnlyPairs.length}"
#eval s!"gate candidates with open parent = {gateParentOpenPairs.length}"
#eval s!"existing EvenChild A/B rectangle candidates = {abPairs.length}"
#eval s!"fifth-only count by m = {countByM fifthOnlyPairs}"
#eval s!"fifth-only count by (m,j mod 32) = {countByMResidue32 fifthOnlyPairs}"
#eval s!"fifth-only normalized examples = {normalizedExamples}"
#eval s!"Agent19 M1 family survivors = {agent19M1Pairs.length}"
#eval s!"Agent19 M2 family survivors = {agent19M2Pairs.length}"

end BB6.Agent4EvenChildScan
