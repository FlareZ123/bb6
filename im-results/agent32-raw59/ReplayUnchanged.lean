import Lean
import Lean.Replay
open Lean

/-- Recheck unchanged single-part producer objects against their actual isolated
    imports. All arguments must have the same import descriptors. No declaration
    is patched. This is a kernel replay, not a source elaboration. -/
unsafe def main (args : List String) : IO Unit := do
  let first :: _ := args | throw (IO.userError "expected one or more single-part olean paths")
  initSearchPath (← findSysroot)
  let (header, _) ← readModuleData first
  let (_, state) ← importModulesCore header.imports |>.run
  let env ← finalizeImport state header.imports {} 0 false false (isModule := true)
  for path in args do
    let (mod, _) ← readModuleData path
    unless mod.imports == header.imports do
      throw (IO.userError s!"different imports: {path}")
    let mut newConstants : Std.HashMap Name ConstantInfo := {}
    for c in mod.constants do
      if c.isUnsafe || c.isPartial then
        throw (IO.userError s!"unsafe or partial: {c.name}")
      if (env.toKernelEnv.find? c.name).isSome then
        throw (IO.userError s!"duplicate declaration: {c.name}")
      newConstants := newConstants.insert c.name c
    unless newConstants.size == mod.constants.size do
      throw (IO.userError "duplicate local declarations")
    IO.println s!"Replaying {path}: {newConstants.size} constants"
    discard <| env.toKernelEnv.replay newConstants
    IO.println s!"PASS {path}: checked by Lean kernel"
  env.freeRegions
