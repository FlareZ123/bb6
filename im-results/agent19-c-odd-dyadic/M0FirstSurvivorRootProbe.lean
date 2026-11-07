import CResidualMass2000

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent19M0RootProbe

open BB6.Agent4CResidualMass2000

/-- The first m=0 high parameters beyond the mass-2000 cutoff that survive
    the exact high filter and the four-sector full-forced exclusion. -/
def sampleJ : List Nat :=
  [249]

def main : IO Unit := do
  IO.println "Exact massStopRoot decisions for the first surviving m=0 high targets"
  for j in sampleJ do
    let x := 2*j+3
    let y := 3*j+7
    let b := massStopRoot x y
    IO.println s!"j={j}, rawMass={8*j+17}, target=({x},{y}), root={b}"

end BB6.Agent19M0RootProbe

def main : IO Unit := BB6.Agent19M0RootProbe.main
