module
public meta import Lean
public meta section
open Lean Meta Elab Tactic

namespace CostWitness

/-- Instantiate an existential proposition at a candidate witness. -/
def atWitness (p w : Expr) : MetaM Expr := do
  let p ← whnf p
  unless p.isAppOfArity ``Exists 2 do throwError "not an existential: {p}"
  return (mkApp p.getAppArgs[1]! w).headBeta

/-- Lift ordinary congruence proofs between existential propositions to a fixed witness.
Unsupported logical equivalences are rejected rather than treated as witness-preserving. -/
partial def specializeEq (eq w : Expr) : MetaM Expr := do
  let eq := eq.consumeMData.headBeta
  let args := eq.getAppArgs
  let typ ← whnf (← inferType eq)
  unless typ.isAppOfArity ``Eq 3 do throwError "not an equality: {typ}"
  let lhs ← atWitness typ.getAppArgs[1]! w
  let rhs ← atWitness typ.getAppArgs[2]! w
  if ← isDefEq lhs rhs then return ← mkEqRefl lhs
  let .const name _ := eq.getAppFn | throwError "unsupported equality head: {eq}"
  if name == ``id then
    specializeEq args.back! w
  else if name == ``congrArg then
    let f := args[4]!
    let ft ← whnf (← inferType f)
    let .forallE nm dom _ bi := ft | throwError "congrArg function: {ft}"
    let g ← withLocalDecl nm bi dom fun x => do
      let y ← atWitness (mkApp f x) w
      mkLambdaFVars #[x] y
    mkAppM ``congrArg #[g, args.back!]
  else if name == ``Eq.trans then
    let h₁ ← specializeEq args[4]! w
    let h₂ ← specializeEq args[5]! w
    mkAppM ``Eq.trans #[h₁, h₂]
  else if name == ``Eq.symm then
    mkAppM ``Eq.symm #[← specializeEq args.back! w]
  else
    throwError "unsupported witness transport: {name}"

/-- A supplied counted induction hypothesis can replace an opaque uncounted subproof.
The replacement must elaborate at the same proposition and contain no unresolved metavariables. -/
def replacement? (e : Expr) (rs : Array Expr) : MetaM (Option Expr) := do
  if rs.isEmpty then return none
  let target ← inferType e
  for r in rs do
    let saved ← saveState
    let (xs, _, conclusion) ← forallMetaTelescopeReducing (← inferType r)
    if ← isDefEq target conclusion then
      let v ← instantiateMVars (mkAppN r xs)
      if !v.hasMVar && v != e then return some v
    saved.restore
  return none

/-- Expose constructor-headed proof terms. Explicit theorem unfolding is metaprogram-only;
the resulting proof must typecheck independently. -/
partial def expose (e : Expr) (rs : Array Expr := #[]) (fuel : Nat := 4096) : MetaM Expr := do
  if fuel == 0 then throwError "witness exposure fuel exhausted"
  let fuel := fuel - 1
  let e := e.consumeMData.headBeta
  let fn := e.getAppFn
  let args := e.getAppArgs
  if let .const name _ := fn then
    if (name == ``Eq.mp || name == ``Eq.mpr) && args.size == 4 then
      let target ← whnf (← inferType e)
      if target.isAppOfArity ``Exists 2 then
        let source ← expose args[3]! rs fuel
        unless source.isAppOfArity ``Exists.intro 4 do
          throwError "transport source is not an exposed existential: {source}"
        let w := source.getAppArgs[2]!
        let h ← specializeEq args[2]! w
        let p ← mkAppM name #[h, source.getAppArgs[3]!]
        return mkAppN (mkConst ``Exists.intro (source.getAppFn.constLevels!))
          #[target.getAppArgs[0]!, target.getAppArgs[1]!, w, p]
    if (name == ``Eq.rec || name == ``Eq.ndrec) && args.size == 6 then
      let target ← whnf (← inferType e)
      if target.isAppOfArity ``Exists 2 then
        let source ← expose args[3]! rs fuel
        unless source.isAppOfArity ``Exists.intro 4 do
          throwError "recursor source is not an exposed existential: {source}"
        let w := source.getAppArgs[2]!
        let motive := args[2]!
        let motive' ← withLocalDeclD `b args[0]! fun b => do
          if name == ``Eq.rec then
            let eqType ← mkEq args[1]! b
            withLocalDeclD `h eqType fun h => do
              let p ← atWitness (mkApp2 motive b h) w
              mkLambdaFVars #[b, h] p
          else
            let p ← atWitness (mkApp motive b) w
            mkLambdaFVars #[b] p
        let proof := mkAppN fn (args.set! 2 motive' |>.set! 3 source.getAppArgs[3]!)
        return mkAppN (mkConst ``Exists.intro (source.getAppFn.constLevels!))
          #[target.getAppArgs[0]!, target.getAppArgs[1]!, w, proof]
  let e' ← whnfCore e
  if e' != e then return ← expose e' rs fuel
  let fn := e.getAppFn
  let args := e.getAppArgs
  let .const name levels := fn | do
    if let some v ← replacement? e rs then return ← expose v #[] fuel
    return e
  let info ← getConstInfo name
  match info with
  | .thmInfo _ | .defnInfo _ =>
    let v ← instantiateValueLevelParams info levels true
    expose (mkAppN v args) rs fuel
  | .recInfo r =>
    let i := r.getMajorIdx
    if h : i < args.size then
      let major ← expose args[i] rs fuel
      if major == args[i] then
        if let some v ← replacement? e rs then
          return ← expose v #[] fuel
        return e
      expose (mkAppN fn (args.set i major)) rs fuel
    else return e
  | _ =>
    if let some v ← replacement? e rs then
      return ← expose v #[] fuel
    return e

/-- Return the fixed-witness evidence from a constructive existential proof. -/
elab "witness_proof% " p:term:max " using " "[" rs:term,* "]" : term => do
  let proof ← Elab.Term.elabTerm p none
  let proof ← instantiateMVars proof
  let replacements ← rs.getElems.mapM fun stx => do
    instantiateMVars (← Elab.Term.elabTerm stx none)
  let e ← expose proof replacements
  unless e.isAppOfArity ``Exists.intro 4 do
    throwError "failed to expose existential constructor: {e}"
  let args := e.getAppArgs
  let cost := args[2]!
  let evidence := args[3]!
  let wanted ← atWitness (← inferType proof) cost
  unless ← isDefEq (← inferType evidence) wanted do
    throwError "fixed-witness evidence has the wrong type"
  check evidence
  logInfo m!"extracted cost: {cost}"
  return evidence

/-- Generate a new counted theorem from an uncounted universal theorem. For a
    positive reachability proof the last conjunct is its fixed-cost reach equation. -/
elab "recover_count " source:ident " as " dest:ident positive:(" positive")? : command => do
  Elab.Command.liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo source
    let info ← getConstInfo name
    let newName := (← getCurrNamespace) ++ dest.getId
    let levels := info.levelParams.map Level.param
    forallTelescope info.type fun xs _ => do
      let original := mkAppN (mkConst name levels) xs
      let e ← expose original
      unless e.isAppOfArity ``Exists.intro 4 do
        throwError "failed to expose existential constructor: {e}"
      let args := e.getAppArgs
      let cost := args[2]!
      let proof := args[3]!
      let expected ← atWitness (← inferType original) cost
      unless ← isDefEq (← inferType proof) expected do
        throwError "fixed-witness evidence has the wrong type"
      let evidence ← if positive.isSome then mkAppM ``And.right #[proof] else pure proof
      let resultType ← if positive.isSome then do
        let p ← whnf expected
        unless p.isAppOfArity ``And 2 do throwError "positive proof is not a conjunction: {p}"
        pure p.getAppArgs[1]!
      else pure expected
      unless ← isDefEq (← inferType evidence) resultType do
        throwError "recovered proof has the wrong counted type"
      let type ← mkForallFVars xs resultType
      let value ← mkLambdaFVars xs evidence
      check value
      addDecl (.thmDecl {name := newName, levelParams := info.levelParams, type, value})
      logInfo m!"{newName}: recovered witness {cost}"

end CostWitness
