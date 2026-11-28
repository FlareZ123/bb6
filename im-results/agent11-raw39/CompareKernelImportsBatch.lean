import Lean
open Lean

/-!
A *batch*, read-only version of CompareKernelImports.lean. Each tab-separated
line is one pair of original .olean paths. Output is exactly one E (same kernel
data, imports and declarations) or D (different) for each input pair, in order.
No equivalence is accepted merely from a matching module name or hash.
The predicate intentionally matches the independently used single-pair tool.
-/

def kernelDataEqual (x y : System.FilePath) : IO Bool := do
  let (a, _) ← readModuleData x
  let (b, _) ← readModuleData y
  pure <| a.isModule == b.isModule && a.imports == b.imports &&
    a.constNames == b.constNames && a.constants == b.constants &&
    a.extraConstNames == b.extraConstNames

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
      let data ← IO.FS.readFile path
      for line in data.splitOn "\n" do
        if line != "" then
          match line.splitOn "\t" with
          | [a, b] =>
              let eq ← kernelDataEqual a b
              IO.println (if eq then "E" else "D")
          | _ => throw (IO.userError "expected tab-separated original object pairs")
  | _ => throw (IO.userError "usage: lean --run CompareKernelImportsBatch.lean pairs.tsv")
