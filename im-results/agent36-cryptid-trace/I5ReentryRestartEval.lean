import I5ExceptionalRejoin
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 180000
set_option maxHeartbeats 0

namespace BB6.Agent36.I5ReentryRestartEval

open BB6.Agent35I5Exceptional

def restartSeed : DRegular.L := pureReentry t5

theorem restartSeed_canon : DRegular.Canon restartSeed := by
  constructor
  · norm_num [restartSeed, pureReentry, DRegular.Canon]
  · exact Or.inr rfl

def firstStop : Nat → DRegular.L → Option Nat
  | 0, _ => none
  | fuel + 1, s =>
      match DRegular.next s with
      | none => some 0
      | some s' => (firstStop fuel s').map Nat.succ

#eval restartSeed.a % 9
#eval restartSeed.a % 3
#eval DRegular.next restartSeed
#eval (DRegular.run 10 restartSeed).map (fun s => (s.a, s.q, s.b))
#eval firstStop 1711 restartSeed
#eval (DRegular.run 1711 restartSeed).map (fun s => (s.a, s.q, s.b))
#eval DRegular.accumulated 1711 restartSeed

#print axioms restartSeed_canon

end BB6.Agent36.I5ReentryRestartEval
