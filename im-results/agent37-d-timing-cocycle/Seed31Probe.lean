import Lean.Elab.Tactic.Omega
import BlankThirtiethRejoin
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2ThirtyFirstProbe

open DRegular BB6.Agent2ThirtiethRoot

/-- Locate the first exceptional state within a short block. -/
def firstStopAux : Nat → Nat → DRegular.L → Nat × DRegular.L
  | 0, n, s => (n, s)
  | fuel+1, n, s =>
      match DRegular.next s with
      | none => (n, s)
      | some t => firstStopAux fuel (n+1) t

/-- Search in residue-reduced 512-step blocks, then inspect the first
    failing block one transition at a time. -/
def firstStopBlocks : Nat → Nat → DRegular.L → Nat × DRegular.L
  | 0, n, s => (n, s)
  | fuel+1, n, s =>
      match BB6.Agent2Fast64.fastRun 512 s with
      | none => firstStopAux 512 n s
      | some t => firstStopBlocks fuel (n+512) t

def firstExceptionFromSeed31 : Nat × DRegular.L :=
  firstStopBlocks 2000 0 seed31

/-- Diagnostic projection only: a returned count below 1,024,000 means
    the second component is the first exceptional state. -/
#eval
  let (n, s) := firstExceptionFromSeed31
  (n, s.a % 59049, s.q, s.b, (DRegular.next s).isNone)

end BB6.Agent2ThirtyFirstProbe
