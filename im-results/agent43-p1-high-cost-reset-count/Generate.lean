import BlockMargin
open Lean Elab Command Term Meta
namespace BB6.Agent43Block
open BB6.Agent43CarryCert

/-- Proposal generation only. No proof is produced by this unsafe elaborator. -/
syntax (name := carryLiteral) "carry_literal " ident " := " term : command
syntax (name := carryBlock) "carry_block " ident " := " term:max num num ident : command

private def addLiteral (name : Name) (xs : List Nat) : CommandElabM Unit := do
  let type := mkApp (mkConst ``List [.zero]) (mkConst ``Nat)
  let nil := mkApp (mkConst ``List.nil [.zero]) (mkConst ``Nat)
  let cons := mkApp (mkConst ``List.cons [.zero]) (mkConst ``Nat)
  let value := xs.reverse.foldl (fun tail x => mkApp2 cons (.lit (.natVal x)) tail) nil
  liftCoreM <| addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe})

@[command_elab carryLiteral] unsafe def elabCarryLiteral : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[1].getId
  let xs ← liftTermElabM do
    let ty := mkApp (mkConst ``List [.zero]) (mkConst ``Nat)
    let e ← Term.elabTermEnsuringType stx[3] ty
    Term.synthesizeSyntheticMVarsNoPostponing
    Meta.evalExpr (List Nat) ty (← instantiateMVars e)
  addLiteral name xs

private partial def decode (e : Expr) (acc : List Nat := []) : Except String (List Nat) :=
  if e.isAppOfArity ``List.nil 1 then .ok acc.reverse
  else if e.isAppOfArity ``List.cons 3 then
    match e.getAppArgs[1]! with
    | .lit (.natVal n) => decode e.getAppArgs[2]! (n::acc)
    | _ => .error "carry list has nonliteral element"
  else .error "carry list is not a generated literal"

@[command_elab carryBlock] unsafe def elabCarryBlock : CommandElab := fun stx => do
  let ns ← getCurrNamespace
  let name := ns ++ stx[1].getId
  let Q ← liftTermElabM do
    let ty := Lean.mkConst ``Nat
    let e ← Term.elabTermEnsuringType stx[3] ty
    Term.synthesizeSyntheticMVarsNoPostponing
    Meta.evalExpr Nat ty (← instantiateMVars e)
  let j := stx[4].isNatLit?.getD 0
  let h := stx[5].isNatLit?.getD 0
  let old := ns ++ stx[6].getId
  let some (.defnInfo d) := (← getEnv).find? old | throwError "missing literal {old}"
  let .ok cs := decode d.value | throwError "cannot decode literal {old}"
  let ds := if j==0 && h==1 then step Q j cs else blockStep Q j h cs
  addLiteral name ds
end BB6.Agent43Block
