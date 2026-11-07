import CResidualMass2000

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent19M0RootProbe

open BB6.Agent4CResidualMass2000

/-- The first high stopping targets above raw mass 2000, across m=0 and m=1. -/
def sampleMJ : List (Nat × Nat) :=
  [(0,248),(0,249),(1,60)]

def main : IO Unit := do
  IO.println "Exact massStopRoot decisions for the first high targets beyond raw mass 2000"
  for (m,j) in sampleMJ do
    let x := 2*j+3
    let y := 2^(2*m+2)*(j+3)-(j+3*m+5)
    let b := massStopRoot x y
    IO.println s!"m={m}, j={j}, rawMass={x+2*y}, target=({x},{y}), root={b}"

end BB6.Agent19M0RootProbe

def main : IO Unit := BB6.Agent19M0RootProbe.main
