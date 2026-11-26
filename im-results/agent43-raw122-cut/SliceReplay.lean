import Lean.Util.Path
import Lean.Util.FoldConsts
import Lean.Replay
open Lean

/-- Reconstruct an importable theorem slice using the actual kernel replay API.
Every missing declaration is recursively collected and sent to the kernel.
No missing axiom, unsafe or partial declaration is introduced. -/
def collectSlice (source base : Environment) (roots : Array Name) : IO (Std.HashMap Name ConstantInfo) := do
  let mut seen : NameSet := {}
  let mut needed : Std.HashMap Name ConstantInfo := {}
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := source.find? n | throw (IO.userError s!"missing source constant {n}")
    if let some bi := base.find? n then
      if ci.type != bi.type || ci.levelParams != bi.levelParams then
        throw (IO.userError s!"base/source type mismatch {n}")
      match ci, bi with
      | .thmInfo _, .thmInfo _ => pure () -- proof irrelevance
      | .inductInfo c, .inductInfo b => if c != b then throw (IO.userError s!"inductive mismatch {n}")
      | .ctorInfo c, .ctorInfo b => if c != b then throw (IO.userError s!"ctor mismatch {n}")
      | .recInfo c, .recInfo b => if c != b then throw (IO.userError s!"recursor mismatch {n}")
      | _, _ => if ci.value? (allowOpaque := true) != bi.value? (allowOpaque := true) then
                    throw (IO.userError s!"base/source value mismatch {n}")
      continue
    if ci.isUnsafe || ci.isPartial then throw (IO.userError s!"unsafe or partial dependency {n}")
    if let .axiomInfo _ := ci then throw (IO.userError s!"unexpected non-base axiom {n}")
    needed := needed.insert n ci
    for dep in ci.getUsedConstantsAsSet do todo := todo.push dep
    match ci with
    | .inductInfo v => todo := todo ++ v.all.toArray
    | .ctorInfo v => todo := todo.push v.induct
    | _ => pure ()
  return needed

def main (args : List String) : IO Unit := do
  let baseMod :: srcMod :: outMod :: roots := args | throw (IO.userError "base source output roots...")
  if roots.isEmpty then throw (IO.userError "no roots")
  initSearchPath (← findSysroot)
  let opts : Options := {}
  let base ← importModules #[{module := baseMod.toName}] opts (trustLevel := 0) (loadExts := false)
  IO.println s!"base imported {baseMod}"
  let src ← importModules #[{module := srcMod.toName}] opts (trustLevel := 0) (loadExts := false)
  IO.println s!"source imported {srcMod}"
  let slice ← collectSlice src base (roots.toArray.map String.toName)
  IO.println s!"selected {slice.size} declarations"
  let checked ← base.toKernelEnv.replay slice
  let out := (Environment.ofKernelEnv checked).setMainModule outMod.toName
  for root in roots do
    unless out.contains root.toName do throw (IO.userError s!"missing replayed root {root}")
  IO.println "kernel replay passed; exporting"
  writeModule out (System.FilePath.mk (outMod ++ ".olean")) (writeIR := false)
  IO.println s!"wrote {outMod}.olean"
