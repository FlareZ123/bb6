import CanonicalTwoParentRosterOnly
import F0SiblingIntegrationExtended

open BB6Coverage

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6Canonical76Export

def slots : List Slot :=
  (List.finRange 6).flatMap fun q => [(q, false), (q, true)]

def stateChar (q : Fin 6) : String :=
  String.singleton (Char.ofNat (65 + q.val))

def encodeMove (m : Move) : String :=
  String.singleton (if m.write then '1' else '0') ++
  String.singleton (if m.dir then 'R' else 'L') ++
  stateChar m.next

def encodeEntry : Option (Option Move) → String
  | none => "---"
  | some none => "HHH"
  | some (some m) => encodeMove m

def encodeTable (p : PartialMachine) : String :=
  String.intercalate "_" (slots.map fun s => encodeEntry (p s))

def encodeAddress (address : List Move) : String :=
  if address.isEmpty then "-" else String.intercalate "," (address.map encodeMove)

def emit (kind : String) (address : List Move) (p : PartialMachine) : IO Unit := do
  IO.println s!"{kind}\t{encodeAddress address}\t{encodeTable p}"

def main : IO Unit := do
  IO.println "kind\taddress\ttable"
  for e in BB6.Agent47CanonicalTwoParent.roster76 do
    emit "BASE76" e.1 e.2
  for e in BB6.Agent41F0Extended.remainingExtended do
    emit "REMAINING112"
      (BB6.Agent31ChampionParentIntegration.championResidualAddress ++ e.1) e.2

end BB6.Agent6Canonical76Export

def main : IO Unit := BB6.Agent6Canonical76Export.main
