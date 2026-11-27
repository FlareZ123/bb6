import Lean
open Lean

/-- Structural identity of a Name: numeric and string components are distinct,
    even when a display printer would give ambiguous text. -/
def nameKey (n : Name) : Json :=
  .arr <| n.components.toArray.map fun
    | .str _ s => toJson s
    | .num _ k => toJson k
    | .anonymous => .null

def kind (c : ConstantInfo) : String :=
  match c with
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | _ => "other"

def main (args : List String) : IO Unit := do
  for path in args do
    let (data, _) ← readModuleData ⟨path⟩
    unless data.constNames.size == data.constants.size do
      throw (IO.userError s!"malformed constant arrays: {path}")
    let decls := data.constants.map fun c =>
      Json.arr #[nameKey c.name, toJson c.name.toString, toJson (kind c)]
    IO.println <| Json.compress <| Json.arr #[toJson path, Json.arr decls]
