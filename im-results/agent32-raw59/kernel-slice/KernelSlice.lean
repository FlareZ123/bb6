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

unsafe def main (args : List String) : IO Unit := do
  let [baseList, rootList, objectList, moduleName, prefixName, out] := args |
    fail "usage: KernelSlice base-list root-list object-list module prefix output.olean"
  initSearchPath (← findSysroot)
  let imports : Array Import := (← lines baseList).map (fun s => { module := s.toName })
  let roots := (← lines rootList).map String.toName
  let base ← importModules imports {} 0
  let kbase := base.toKernelEnv
  let mut producer : InfoMap := {}
  let mut groups : AdjMap := {}
  let mut count : Nat := 0
  for path in ← lines objectList do
    let (data, _) ← readModuleData path
    if data.isModule then fail s!"split/module-system object not supported: {path}"
    for c in data.constants do
      if let some old := producer[c.name]? then
        unless old == c do fail s!"different producer constants: {c.name}"
      else
        producer := producer.insert c.name c
        for i in groupMembers c do
          groups := appendEdge groups i c.name
          groups := appendEdge groups c.name i
    count := count + 1
  IO.println s!"Indexed {count} modules, {producer.size} unique kernel declarations"
  let mut reached : NameSet := {}
  let mut reverse : AdjMap := {}
  let mut relocate : NameSet := {}
  let mut queue := roots
  let mut pos := 0
  while pos < queue.size do
    let n := queue[pos]!
    pos := pos + 1
    if reached.contains n then continue
    reached := reached.insert n
    let some c := producer[n]? | do
      let some idx := base.getModuleIdxFor? n | fail s!"missing constant {n}"
      unless (kbase.find? n).isSome && stdModule base.allImportedModuleNames[idx]! do
        fail s!"producer lacks nonstandard dependency {n}"
      continue
    if c.isUnsafe || c.isPartial then fail s!"unsafe or partial dependency {n}"
    if (kbase.find? n) != some c then relocate := relocate.insert n
    for dep in deps c groups do
      reverse := appendEdge reverse dep n
      if !reached.contains dep then queue := queue.push dep
  IO.println s!"Reached {reached.size} constants; initially differing or absent {relocate.size}"
  queue := relocate.toArray
  pos := 0
  while pos < queue.size do
    let n := queue[pos]!
    pos := pos + 1
    for p in reverse[n]?.getD #[] do
      if !relocate.contains p then
        relocate := relocate.insert p
        queue := queue.push p
  let pre := prefixName.toName
  let rn := fun n => if relocate.contains n then pre ++ n else n
  let mut selected : InfoMap := {}
  let mut relocations : Array String := #[]
  for n in relocate do
    let c := producer[n]!
    if c matches .axiomInfo _ | .quotInfo _ then fail s!"would relocate axiom or quotient {n}"
    let renamed := renameInfo rn c
    unless renamed.name == rn n do fail s!"bad relocation {n}"
    if (kbase.find? renamed.name).isSome || selected.contains renamed.name then
      fail s!"relocation collision {renamed.name}"
    selected := selected.insert renamed.name renamed
    relocations := relocations.push s!"{n} -> {renamed.name}"
  IO.println s!"Kernel replay of {selected.size} relocated constants"
  IO.FS.writeFile (out ++ ".names") (String.intercalate "\n" relocations.toList ++ "\n")
  let checked ← kbase.replay selected
  for (n,c) in selected.toList do
    unless checked.find? n == some c do fail s!"replayed declaration differs: {n}"
  let constants := checked.constants.foldStage2 (fun acc _ ci => acc.push ci) #[]
  for c in constants do
    if (kbase.find? c.name).isSome then fail s!"base declaration exported: {c.name}"
    if c.isUnsafe || c.isPartial || (c matches .axiomInfo _) then
      fail s!"unexpected generated declaration {c.name}"
  for n in roots do
    unless (checked.find? (rn n)).isSome do fail s!"missing replayed root {rn n}"
    IO.println s!"ROOT {n} -> {rn n}"
  saveModuleData out moduleName.toName {
    isModule := false, imports, constNames := constants.map (·.name), constants,
    extraConstNames := #[], entries := #[] }
  IO.println s!"PASS: saved {constants.size} kernel-checked declarations to {out}"
