import Lean
import Canonical58Raw113Graft
import Canonical57Raw112Graft

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Lean
open BB6Coverage

/-- Encode the finite transition cell exactly as the repository's six-row RLE. -/
def encodeRosterCell : Option (Option Move) → String
  | none => "---"
  | some none => "HHH"
  | some (some mv) =>
      String.singleton (if mv.write then '1' else '0') ++
      String.singleton (if mv.right then 'R' else 'L') ++
      String.singleton (Char.ofNat (65 + mv.next.val))

/-- Encode state A through F, with symbol 0 then symbol 1 in each row. -/
def encodeRosterTable (m : PartialMachine) : String :=
  String.intercalate "_" <|
    (List.finRange 6).map fun state =>
      encodeRosterCell (m (state, false)) ++
      encodeRosterCell (m (state, true))

/-- The raw residual index and exact 12-cell partial table of a Lean roster entry. -/
def encodeRosterManifest (xs : List (Nat × PartialMachine)) : Json :=
  Json.arr <| (xs.map fun e =>
    Json.mkObj [
      ("raw_residual_index", toJson e.1),
      ("table_rle", toJson (encodeRosterTable e.2))
    ]).toArray

/-- Export the actual accepted Canonical58 roster and its accepted Canonical57 successor. -/
#eval do
  let dir ← IO.getEnv "ROSTER_EXPORT_DIR"
  let dir := dir.getD "/tmp"
  let roster58 := encodeRosterManifest BB6.Agent31Canonical58Raw113Graft.roster58
  let roster57 := encodeRosterManifest BB6.Agent17Canonical57Raw112Graft.roster57
  IO.FS.writeFile (dir ++ "/canonical58-lean-roster.json")
    (Json.compress roster58 ++ "\n")
  IO.FS.writeFile (dir ++ "/canonical57-lean-roster.json")
    (Json.compress roster57 ++ "\n")
