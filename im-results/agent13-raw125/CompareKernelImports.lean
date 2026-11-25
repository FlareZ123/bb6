import Lean
open Lean

/-- Compare the kernel-relevant data of two single-part object files. This does
not compare opaque elaborator extension payloads or replace source provenance. -/
def compareKernelImports (x y : System.FilePath) : IO Unit := do
  let (a, _) ← readModuleData x
  let (b, _) ← readModuleData y
  unless a.isModule == b.isModule && a.imports == b.imports &&
      a.constNames == b.constNames && a.constants == b.constants &&
      a.extraConstNames == b.extraConstNames do
    throw (IO.userError s!"kernel data differs: {x} {y}")
  IO.println s!"PASS {x}: {a.constants.size} identical kernel declarations and import descriptors"

def main (args : List String) : IO Unit := do
  match args with
  | [x, y] => compareKernelImports x y
  | _ => throw (IO.userError "expected two single-part .olean paths")
