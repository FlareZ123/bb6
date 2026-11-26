import Lean
import Lean.Replay
import Lean.Util.FoldConsts

open Lean

abbrev InfoMap := Std.HashMap Name ConstantInfo
abbrev AdjMap := Std.HashMap Name (Array Name)

private def fail (s : String) : IO α := throw (IO.userError s)

private def appendEdge (g : AdjMap) (a b : Name) : AdjMap :=
  g.insert a ((g[a]?.getD #[]).push b)

private def groupMembers (c : ConstantInfo) : List Name :=
  match c with
  | .inductInfo v => v.all
  | .ctorInfo v => [v.induct]
  | .recInfo v => v.all
  | _ => []

private def deps (c : ConstantInfo) (groups : AdjMap) : Array Name := Id.run do
  let mut ds := c.getUsedConstantsAsSet.toArray
  ds := ds ++ (groups[c.name]?.getD #[])
  match c with
  | .inductInfo v => ds := ds ++ v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => ds := ds.push v.induct
  | .recInfo v =>
    ds := ds ++ v.all.toArray
    for r in v.rules do
      ds := (ds.push r.ctor) ++ r.rhs.getUsedConstants
  | .defnInfo v => ds := ds ++ v.all.toArray
  | .thmInfo v => ds := ds ++ v.all.toArray
  | .opaqueInfo v => ds := ds ++ v.all.toArray
  | _ => pure ()
  return ds

private partial def renameExpr (rn : Name → Name) (e : Expr) : Expr :=
  e.replace fun t => match t with
  | .const n ls => if rn n == n then none else some (.const (rn n) ls)
  | .proj n i b => if rn n == n then none else some (.proj (rn n) i (renameExpr rn b))
  | _ => none

private def renameInfo (rn : Name → Name) (c : ConstantInfo) : ConstantInfo :=
  let re := renameExpr rn
  match c with
  | .defnInfo v => .defnInfo { v with name := rn v.name, type := re v.type, value := re v.value, all := v.all.map rn }
  | .thmInfo v => .thmInfo { v with name := rn v.name, type := re v.type, value := re v.value, all := v.all.map rn }
  | .opaqueInfo v => .opaqueInfo { v with name := rn v.name, type := re v.type, value := re v.value, all := v.all.map rn }
  | .inductInfo v => .inductInfo { v with name := rn v.name, type := re v.type, all := v.all.map rn, ctors := v.ctors.map rn }
  | .ctorInfo v => .ctorInfo { v with name := rn v.name, type := re v.type, induct := rn v.induct }
  | .recInfo v => .recInfo { v with name := rn v.name, type := re v.type, all := v.all.map rn, rules := v.rules.map (fun r => {r with ctor := rn r.ctor, rhs := re r.rhs}) }
  | other => other

private def lines (path : String) : IO (Array String) := do
  return (← IO.FS.readFile path).splitOn "\n" |>.toArray.filter (· != "")

private def stdModule (n : Name) : Bool :=
  [`Init, `Lean, `Std].any (·.isPrefixOf n)

unsafe def replayStage (args : List String) : IO Unit := do
  let [baseList, relocationList, objectList, moduleName, prefixName, out] := args |
    fail "usage: KernelStage base-list relocation-list object-list module prefix output.olean"
  initSearchPath (← findSysroot)
  let imports : Array Import := (← lines baseList).map (fun s => { module := s.toName })
  let base ← importModules imports {} 0
  let kbase := base.toKernelEnv
  let relocate : NameSet := (← lines relocationList).foldl (fun a s => a.insert s.toName) {}
  let pre := prefixName.toName
  let rn := fun n => if relocate.contains n then pre ++ n else n
  let mut selected : InfoMap := {}
  for path in ← lines objectList do
    let (data, _) ← readModuleData path
    if data.isModule then fail s!"split/module-system object not supported: {path}"
    for c in data.constants do
      if !relocate.contains c.name then continue
      if c.isUnsafe || c.isPartial || (c matches .axiomInfo _ | .quotInfo _) then
        fail s!"invalid relocation candidate {c.name}"
      let renamed := renameInfo rn c
      if let some old := kbase.find? renamed.name then
        unless old == renamed do fail s!"base relocation mismatch {renamed.name}"
      else if let some old := selected[renamed.name]? then
        unless old == renamed do fail s!"duplicate relocation mismatch {renamed.name}"
      else
        selected := selected.insert renamed.name renamed
  IO.println s!"Stage {moduleName}: replay {selected.size} selected declarations"
  let checked ← kbase.replay selected
  for (n,c) in selected.toList do
    unless checked.find? n == some c do fail s!"replayed declaration differs: {n}"
  let constants := checked.constants.foldStage2 (fun acc _ ci => acc.push ci) #[]
  for c in constants do
    if (kbase.find? c.name).isSome then fail s!"base declaration exported: {c.name}"
    if c.isUnsafe || c.isPartial || (c matches .axiomInfo _) then
      fail s!"unexpected generated declaration {c.name}"
  saveModuleData out moduleName.toName {
    isModule := false, imports, constNames := constants.map (·.name), constants,
    extraConstNames := #[], entries := #[] }
  IO.println s!"PASS: saved {constants.size} kernel-checked declarations to {out}"

/-- Index direct imports and declaration names from actual producer objects. -/
unsafe def moduleIndex (objects : String) : IO Unit := do
  for path in ← lines objects do
    let (data, _) ← readModuleData path
    if data.isModule then fail s!"split/module-system object not supported: {path}"
    IO.println <| Json.compress <| Json.mkObj [
      ("path", toJson path), ("imports", toJson (data.imports.map fun i => i.module.toString)),
      ("declarations", toJson data.constants.size)]

/-- The affected modules form an upward-closed import cone. Dependencies outside
    that cone are imported unchanged from accepted compatible producer objects.
    Only reached constants inside the cone must be relocated and replayed. -/
unsafe def affectedPlan (objects roots out : String) : IO Unit := do
  let mut producer : InfoMap := {}
  let mut groups : AdjMap := {}
  for path in ← lines objects do
    let (data, _) ← readModuleData path
    if data.isModule then fail s!"split/module-system object not supported: {path}"
    for c in data.constants do
      if let some old := producer[c.name]? then
        unless old == c do fail s!"different affected producer constants: {c.name}"
      else
        producer := producer.insert c.name c
        for i in groupMembers c do
          groups := appendEdge groups i c.name
          groups := appendEdge groups c.name i
  let mut reached : NameSet := {}
  let mut queue := (← lines roots).map String.toName
  let mut pos := 0
  for n in queue do
    unless producer.contains n do fail s!"missing affected root {n}"
  while pos < queue.size do
    let n := queue[pos]!
    pos := pos + 1
    if reached.contains n then continue
    let some c := producer[n]? | continue
    reached := reached.insert n
    if c.isUnsafe || c.isPartial || (c matches .axiomInfo _ | .quotInfo _) then
      fail s!"invalid affected dependency {n}"
    for dep in deps c groups do
      if producer.contains dep && !reached.contains dep then queue := queue.push dep
  let mut names : Array String := #[]
  for n in reached do
    let s := n.toString
    unless s.toName == n do fail s!"non-roundtrippable declaration name {n}"
    names := names.push s
  IO.FS.writeFile out (String.intercalate "\n" names.toList ++ "\n")
  IO.println s!"PLAN: {reached.size} reached affected declarations from {producer.size} indexed"

unsafe def main (args : List String) : IO Unit := do
  match args with
  | ["index", objects] => moduleIndex objects
  | ["plan", objects, roots, out] => affectedPlan objects roots out
  | _ => replayStage args
