import HighEvenRightC23FullForcedResidual

namespace BB6.Agent3FullForcedScan
open BB6.Agent3FullForcedResidual

/-- A parameter pair surviving the previous C70+C23+all-phase+even-right
    sieve but rejected by the source-exact full forced normalizer. -/
def additional (j m : Nat) : Bool :=
  highAllowedC23WithEvenRightBool j m &&
    BB6.Agent3.fullForcedExcluded (highTargetX j) (highTargetY j m)

def additionalPairs : List (Nat × Nat) :=
  (highPairs 2000 20).filter fun (j,m) => additional j m

/-- Exact finite count by the stopping parameter m. -/
def countByM : List (Nat × Nat) :=
  (List.range 21).map fun m =>
    (m, ((List.range 2001).filter fun j => additional j m).length)

/-- Exact finite count by m and j modulo 16. This is a diagnostic census,
    not a universal residue theorem. -/
def countByMResidue16 : List (Nat × List Nat) :=
  (List.range 21).map fun m =>
    (m, (List.range 16).map fun r =>
      ((List.range 2001).filter fun j =>
        additional j m && (j % 16 == r)).length)

/-- Preserve representative normalized endpoints so that a later symbolic
    proof can identify which forced inverse sequence causes each exclusion. -/
def normalizedExamples : List (Nat × Nat × Nat × Nat) :=
  (additionalPairs.take 60).map fun (j,m) =>
    let p := BB6.Agent3.fullForcedNormalize (highTargetX j) (highTargetY j m)
    (j,m,p.1,p.2)

#eval s!"additional candidates = {additionalPairs.length}"
#eval countByM
#eval countByMResidue16
#eval normalizedExamples

end BB6.Agent3FullForcedScan
