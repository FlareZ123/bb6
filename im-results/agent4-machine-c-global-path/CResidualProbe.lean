import FastFullBoolean
import HighEvenRightC23Residual
import ValSixMixedNormalize

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent4CResidualProbe

/-- Executable low predicate after the C70 source exclusion. -/
def lowAllowedC70Bool (m : Nat) : Bool :=
  BB6.Agent27FullBool.lowAllowedFullBool m && decide (m % 128 ≠ 18)

theorem lowAllowedC70Bool_iff (m : Nat) :
    lowAllowedC70Bool m = true ↔ BB6.Agent20C70.lowAllowedC70 m := by
  simp [lowAllowedC70Bool, BB6.Agent20C70.lowAllowedC70,
    BB6.Agent27FullBool.lowAllowedFullBool_iff]

/-- Executable high predicate after the all-phase, C70, C23/sum-seven,
    and even-right source exclusions. -/
def highAllowedC23WithEvenRightBool (j m : Nat) : Bool :=
  BB6.Agent27FastBool.fastHighAllowedFullBool j m &&
  decide (¬((j % 128 = 63 ∧ m % 128 = 82) ∨
            (j % 128 = 127 ∧ m % 128 = 18))) &&
  decide (¬(2 ≤ m ∧ j % 4 = 0 ∧ (j+7) % 32 = (3*m) % 32)) &&
  decide (¬(3 ≤ m ∧ m % 4 = 3 ∧ j % 8 = (m+3) % 8))

theorem highAllowedC23WithEvenRightBool_iff (j m : Nat) :
    highAllowedC23WithEvenRightBool j m = true ↔
      BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight j m := by
  simp [highAllowedC23WithEvenRightBool,
    BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight,
    BB6.Agent20C23.highAllowedC23,
    BB6.Agent20C70.highAllowedC70,
    BB6.Agent27FastBool.fastHighAllowedFullBool_iff]

/-- The strongest currently integrated exact Machine C halting
    equivalence, with both parameter filters represented by executable
    Booleans and the fixed-target root decision left exact. -/
theorem blank_halts_iff_final_booleans :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedC70Bool m = true ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4)) = true) ∨
      (∃ j m, highAllowedC23WithEvenRightBool j m = true ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5)) = true) := by
  rw [BB6.Agent19HighEvenRight.blank_halts_iff_c23_and_even_right]
  constructor
  · rintro (⟨m,hm,hroot⟩ | ⟨j,m,hh,hroot⟩)
    · exact Or.inl ⟨m,(lowAllowedC70Bool_iff m).mpr hm,hroot⟩
    · exact Or.inr ⟨j,m,(highAllowedC23WithEvenRightBool_iff j m).mpr hh,hroot⟩
  · rintro (⟨m,hm,hroot⟩ | ⟨j,m,hh,hroot⟩)
    · exact Or.inl ⟨m,(lowAllowedC70Bool_iff m).mp hm,hroot⟩
    · exact Or.inr ⟨j,m,(highAllowedC23WithEvenRightBool_iff j m).mp hh,hroot⟩

#print axioms lowAllowedC70Bool_iff
#print axioms highAllowedC23WithEvenRightBool_iff
#print axioms blank_halts_iff_final_booleans

theorem normalizedRootDecision_eq (x y : Nat) :
    BB6.Agent11Fast.backwardFastFuel
      (((BB6.Agent3ValSix.valSixMixedNormalize x y).1 +
        2*(BB6.Agent3ValSix.valSixMixedNormalize x y).2)/2)
      (BB6.Agent3ValSix.valSixMixedNormalize x y) =
    BB6.Agent3ValSix.valSixMixedRootDecision x y := rfl

structure ProbeResult where
  family : String
  j : Nat
  m : Nat
  x : Nat
  y : Nat
  normalizedX : Nat
  normalizedY : Nat
  rawMass : Nat
  normalizedMass : Nat
  fuel : Nat
  status : String
  root : Option Bool
  deriving Repr

/-- These caps bound the experiment. A skipped row is not a negative
    reachability result. The raw-mass cap bounds normalization work using
    its proven strict mass decrease; the fuel cap bounds the backward search. -/
def rawMassLimit : Nat := 2000
def rootFuelLimit : Nat := 256

def evaluateTarget (family : String) (j m x y : Nat) : ProbeResult :=
  let rawMass := x + 2*y
  if rawMass ≤ rawMassLimit then
    let p := BB6.Agent3ValSix.valSixMixedNormalize x y
    let mass := p.1 + 2*p.2
    let fuel := mass/2
    if fuel ≤ rootFuelLimit then
      let root := BB6.Agent11Fast.backwardFastFuel fuel p
      { family := family, j := j, m := m, x := x, y := y,
        normalizedX := p.1, normalizedY := p.2, rawMass := rawMass,
        normalizedMass := mass, fuel := fuel, status := "evaluated",
        root := some root }
    else
      { family := family, j := j, m := m, x := x, y := y,
        normalizedX := p.1, normalizedY := p.2, rawMass := rawMass,
        normalizedMass := mass, fuel := fuel, status := "root-fuel-cap",
        root := none }
  else
    { family := family, j := j, m := m, x := x, y := y,
      normalizedX := x, normalizedY := y, rawMass := rawMass,
      normalizedMass := rawMass, fuel := rawMass/2,
      status := "raw-mass-cap", root := none }

def lowProbe (m : Nat) : ProbeResult :=
  evaluateTarget "low" 0 m 1 (2^(2*m+3)-(3*m+4))

def highProbe (j m : Nat) : ProbeResult :=
  evaluateTarget "high" j m (2*j+3)
    (2^(2*m+2)*(j+3)-(j+3*m+5))

def highCandidatesFor (jMax m : Nat) : List Nat :=
  (List.range (jMax+1)).filter (fun j =>
    highAllowedC23WithEvenRightBool j m)

def highCounts (jMax mMax : Nat) : List (Nat × Nat) :=
  (List.range (mMax+1)).map fun m =>
    (m, (highCandidatesFor jMax m).length)

def highSample (jMax mMax perRow : Nat) : List (Nat × Nat) :=
  (List.range (mMax+1)).flatMap fun m =>
    ((highCandidatesFor jMax m).take perRow).map fun j => (j,m)

def renderCounts (counts : List (Nat × Nat)) : String :=
  String.intercalate "\n" (counts.map fun (m,n) => s!"m={m}: {n}")

def renderResult (r : ProbeResult) : String :=
  s!"{r.family} j={r.j} m={r.m} target=({r.x},{r.y}) normalized=({r.normalizedX},{r.normalizedY}) rawMass={r.rawMass} normalizedMass={r.normalizedMass} fuel={r.fuel} status={r.status} root={r.root}"

def main : IO Unit := do
  let lowMax := 20
  let highJMax := 2000
  let highMMax := 20
  let perRow := 2
  let lowIndices := (List.range (lowMax+1)).filter lowAllowedC70Bool
  let lowResults := lowIndices.map lowProbe
  let counts := highCounts highJMax highMMax
  let pairs := highSample highJMax highMMax perRow
  let highResults := pairs.map (fun (j,m) => highProbe j m)
  let results := lowResults ++ highResults
  let tested := results.filter (fun r => r.root.isSome)
  let hits := tested.filter (fun r => r.root == some true)
  IO.println "Machine C final-residual exact-root probe"
  IO.println s!"Low domain: m=0..{lowMax}; allowed={lowIndices.length}"
  IO.println s!"High filter domain: j=0..{highJMax}, m=0..{highMMax}"
  IO.println s!"High allowed counts by m:\n{renderCounts counts}"
  IO.println s!"High exact-root samples: first {perRow} allowed j values per m; total={pairs.length}"
  IO.println s!"Raw-mass limit={rawMassLimit}; root-fuel limit={rootFuelLimit}; tested={tested.length}; skipped={results.length-tested.length}; hits={hits.length}"
  IO.println "Probe records:"
  for r in results do
    IO.println (renderResult r)
  if !hits.isEmpty then
    IO.println "HALTING ROOT CANDIDATE(S) FOUND:"
    for r in hits do
      IO.println (renderResult r)

end BB6.Agent4CResidualProbe

def main : IO Unit := BB6.Agent4CResidualProbe.main
