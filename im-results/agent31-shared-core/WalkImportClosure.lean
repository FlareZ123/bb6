import Lean
open Lean

/-- Enumerate precisely the project objects reachable from designated roots.
Duplicate copies are all emitted, allowing the strict linker to compare them.
Imports absent from the input closure must exist in the pinned standard library.
No project declaration is modified or synthesized. -/
partial def visit (dirs : List System.FilePath) (stdlib : System.FilePath)
    (seen : IO.Ref (Std.HashSet String)) (mod : String) : IO Unit := do
  if (← seen.get).contains mod then return
  seen.modify (·.insert mod)
  let rel := mod.replace "." "/" ++ ".olean"
  let mut hits : Array System.FilePath := #[]
  for d in dirs do
    let file := d / rel
    if ← file.pathExists then
      hits := hits.push file
  if hits.isEmpty then
    unless ← (stdlib / rel).pathExists do
      throw (IO.userError s!"missing import {mod}")
    return
  for file in hits do
    IO.println file.toString
  let (data, _) ← readModuleData hits[0]!
  for imp in data.imports do
    visit dirs stdlib seen imp.module.toString

def main (args : List String) : IO Unit := do
  match args with
  | stdlib :: n :: rest =>
    let some count := n.toNat? | throw (IO.userError "invalid directory count")
    let dirs := (rest.take count).map System.FilePath.mk
    let roots := rest.drop count
    unless dirs.length == count && !roots.isEmpty do
      throw (IO.userError "expected directories and project root modules")
    let seen ← IO.mkRef ({} : Std.HashSet String)
    for root in roots do
      visit dirs (System.FilePath.mk stdlib) seen root
  | _ => throw (IO.userError "expected stdlib, directory count, directories, and root modules")
