import Lean
import BusyBeaver.Basic

/-! A proof-producing extractor for finite constructive reachability derivations.
It reuses primitive step equalities and transports, and never trusts an inferred
cost unless Lean checks the generated indexed reachability term. -/
namespace BB6.WitnessExtract
open Lean Meta Elab Tactic

structure Witness where
  cost : Expr
  proof : Expr

structure ExtractContext where
  companions : List (Name × Name) := []
  inductionHyps : List (FVarId × Expr) := []

private def star := ``BusyBeaver.ReachesStar
private def plus := ``BusyBeaver.ReachesPlus
private def exactRel := ``BusyBeaver.ReachesIn

private def isReachName (n : Name) : Bool := n == star || n == plus

private def add (a b : Expr) : MetaM Expr := mkAppM ``HAdd.hAdd #[a,b]

/-- The last two arguments are the configurations, preceded by the machine and
its implicit type parameters. Insert the exact index before those endpoints. -/
private def exactType (rel : Expr) (cost : Expr) : MetaM Expr := do
  let rel := rel.consumeMData
  let .const nm us := rel.getAppFn | throwError "not reachability: {rel}; head={repr rel.getAppFn}"
  unless isReachName nm do throwError "not reachability: {rel}; name={nm}"
  let as := rel.getAppArgs
  let j := as.size-2
  return mkAppN (mkConst exactRel us) (as.extract 0 j ++ #[cost] ++ as.extract j as.size)

/-- Replace even *partially applied* reachability relations in equality
transports (simp generates congrArg Reach and congrFun, not just full apps).
The closure is built using the exact imported relation's binder types. -/
private def pin (cost : Expr) (e : Expr) : MetaM Expr := do
  let mut reps : Array (Expr × Expr) := #[]
  -- The casts normally contain just one universe instantiation; the generic
  -- traversal handles multiple ones, so no assumption about their number.
  let collect : StateT (List Expr) MetaM Unit := e.forEach fun x => do
    if let .const nm _ := x then
      if isReachName nm then modify fun es => if es.contains x then es else x::es
  let (_, cs) ← collect.run []
  for c in cs do
    let ty ← inferType c
    let v ← forallTelescope ty fun xs _ => do
      let rel := mkAppN c xs
      mkLambdaFVars xs (← exactType rel cost)
    reps := reps.push (c,v)
  return e.replace fun x => (reps.find? fun r => r.1 == x).map Prod.snd

private def annotate (p : Expr) (w : Witness) : MetaM Witness := do
  let ty ← inferType p
  let ty ← exactType ty w.cost
  let ht ← inferType w.proof
  unless ← withTransparency .all (isDefEq ht ty) do
    throwError "extracted proof has type {ht}, expected {ty}"
  return { w with proof := ← mkExpectedTypeHint w.proof ty }

private def shortName (n : Name) : Name :=
  (privateToUserName? n).getD n

private def fromExact (p : Expr) : MetaM Witness := do
  let ty := (← inferType p).consumeMData.headBeta
  unless ty.getAppFn.isConstOf exactRel do throwError "not exact reachability: {ty}"
  let args := ty.getAppArgs
  return ⟨args[args.size-3]!,p⟩

/-- Every call either preserves a kernel proof or constructs an application of
an imported exact-step theorem. Unsupported proof shapes fail closed. -/
partial def extract (p : Expr) (ctx : ExtractContext := {}) : MetaM Witness := do
  let p := p.consumeMData
  if let .letE _ _ v b _ := p then return ← extract (b.instantiate1 v) ctx
  let as := p.getAppArgs
  if p.getAppFn.isLambda then return ← extract (p.getAppFn.beta as) ctx
  if let .fvar f := p.getAppFn then
    if let some (_,h) := ctx.inductionHyps.find? (fun a => a.1 == f) then
      return ← fromExact (mkAppN h as)
  let .const raw us := p.getAppFn | throwError "unsupported reachability proof: {p}"
  if let some (_,dst) := ctx.companions.find? (fun a => a.1 == raw) then
    return ← fromExact (mkAppN (mkConst dst us) as)
  let nm := shortName raw
  let back := as.back?.getD (mkNatLit 0)
  let penult := as[as.size-2]?.getD (mkNatLit 0)
  let pre := as.extract 0 (as.size-2)
  if nm == ``Exists.intro then
    let n := as[2]!
    let h := as[3]!
    let ht ← whnf (← inferType h)
    if ht.isAppOfArity ``And 2 then
      return ⟨n, ← mkAppM ``And.right #[h]⟩
    return ⟨n,h⟩
  if nm == ``id then return ← extract back ctx
  if nm == ``Eq.mp || nm == ``Eq.mpr then
    let w ← extract back ctx
    -- Pin the complete cast including all inferred type arguments. This also
    -- handles proof transports across partially applied relations.
    let cast ← pin w.cost (mkAppN p.getAppFn (as.pop))
    let h := mkApp cast w.proof
    return ← annotate p ⟨w.cost,h⟩
  if nm == ``Eq.rec || nm == ``Eq.ndrec || nm == ``Eq.recOn || nm == ``Eq.ndrecOn then
    throwError "dependent equality recursor not yet supported: {nm}"
  if [``BusyBeaver.ReachesPlus.to_star, `BusyBeaver.stepPlus_stepStar, `BusyBeaver.stepPlus_to_stepStar].contains nm then
    return ← annotate p (← extract back ctx)
  if [`BusyBeaver.ReachesStar.head, `BusyBeaver.ReachesPlus.head, ``BusyBeaver.step_stepStar_stepPlus].contains nm then
    let w ← extract back ctx
    let n ← add w.cost (mkNatLit 1)
    let h := mkAppN (mkConst ``BusyBeaver.ReachesIn.step_left us) (pre ++ #[w.cost, penult, w.proof])
    return ← annotate p ⟨n,h⟩
  if [`BusyBeaver.ReachesStar.tail, `BusyBeaver.ReachesPlus.tail].contains nm then
    let w ← extract penult ctx
    let n ← add w.cost (mkNatLit 1)
    let h := mkAppN (mkConst `BusyBeaver.ReachesIn.step_right us) (pre ++ #[w.cost,w.proof,back])
    return ← annotate p ⟨n,h⟩
  if [``BusyBeaver.ReachesStar.trans, `BusyBeaver.ReachesPlus.trans, `BusyBeaver.ReachesPlus.trans_star,
      `BusyBeaver.ReachesStar.trans_plus, `BusyBeaver.stepStar_trans, `BusyBeaver.stepPlus_trans,
      `BusyBeaver.stepPlus_stepStar_stepPlus, `BusyBeaver.stepStar_stepPlus_stepPlus,
      `BusyBeaver.stepPlus_stepStar_trans, `BusyBeaver.stepStar_stepPlus_trans].contains nm then
    let w ← extract penult ctx
    let v ← extract back ctx
    let n ← add w.cost v.cost
    let h := mkAppN (mkConst ``BusyBeaver.ReachesIn.trans us) (pre ++ #[w.cost,v.cost,w.proof,v.proof])
    return ← annotate p ⟨n,h⟩
  if [`BusyBeaver.ReachesStar.single, `BusyBeaver.ReachesPlus.single, `BusyBeaver.step_stepStar,
      `BusyBeaver.step_stepPlus].contains nm then
    let h := mkAppN (mkConst ``BusyBeaver.ReachesIn.single us) as
    return ← annotate p ⟨mkNatLit 1,h⟩
  if [`BusyBeaver.ReachesStar.refl, `BusyBeaver.stepStar_refl].contains nm then
    let h := mkAppN (mkConst ``BusyBeaver.ReachesIn.zero us) as
    return ← annotate p ⟨mkNatLit 0,h⟩
  if [`BusyBeaver.ReachesIn.to_star, `BusyBeaver.stepStar_of_multiStep].contains nm then
    return ← annotate p ⟨as[as.size-4]!,back⟩
  if nm == `BusyBeaver.ReachesIn.to_plus then
    return ← annotate p ⟨as[as.size-5]!,back⟩
  let ci ← getConstInfo raw
  let some body := ci.value? true | throwError "proof body unavailable: {raw}"
  let body := body.instantiateLevelParams ci.levelParams us
  let body := body.beta as
  if body == p then throwError "opaque/unreducible proof body: {raw}"
  extract body ctx

private def closeExact (p : Expr) : TacticM Unit := do
  let w ← extract p
  let expected ← getMainTarget
  let actual ← inferType w.proof
  unless ← withTransparency .all (isDefEq actual expected) do
    throwError "extracted exact index does not match goal; actual {actual}; expected {expected}"
  logInfo m!"extracted primitive index: {w.cost}"
  closeMainGoal `extract_cost w.proof

/-- The user states the exact cost; the kernel checks the reconstructed proof.
For atomic `execute k` source derivations this is a short proof-term replay. -/
elab "extract_cost " p:term : tactic => withMainContext do
  closeExact (← elabTerm p none)

/-- Resolve the exact private source theorem by its unmangled user name. The
lookup rejects ambiguous names instead of choosing any matching proof. Use a
non-`module` importing file so private imported declaration bodies are available. -/
private def sourceName (nm : Name) : MetaM Name := do
  let env ← getEnv
  if env.contains nm then return nm
  let candidates := env.constants.fold (fun acc n _ =>
    if privateToUserName? n == some nm then n :: acc else acc) ([] : List Name)
  match candidates with
  | [n] => return n
  | [] => throwError "no imported private theorem named {nm}"
  | _ => throwError "ambiguous private source name {nm}: {candidates}"

elab "extract_cost_from " nm:str " using " "[" args:term,* "]" : tactic => withMainContext do
  let n ← sourceName nm.getString.toName
  let vals ← args.getElems.mapM (fun a => elabTerm a none)
  let p ← mkAppM n vals
  closeExact p

/-- Derive a new theorem with precisely the original source theorem's binders
and endpoint expressions, changing only existential reachability into the
stated exact index. No copied transition definitions or proof script. -/
elab "#extract_exact " src:str " as " dst:ident " cost " n:num : command =>
    Command.liftTermElabM do
  let name ← sourceName src.getString.toName
  let ci ← getConstInfo name
  let cn := mkConst name (ci.levelParams.map Level.param)
  let cost := mkNatLit n.getNat
  forallTelescope ci.type fun xs body => do
    let w ← extract (mkAppN cn xs)
    unless ← withTransparency .all (isDefEq w.cost cost) do
      throwError "expected fixed index {cost}, extracted {w.cost}"
    let type ← exactType body cost
    unless ← withTransparency .all (isDefEq (← inferType w.proof) type) do
      throwError "extracted proof does not have expected indexed type {type}"
    let declType ← instantiateMVars (← mkForallFVars xs type)
    let declValue ← instantiateMVars (← mkLambdaFVars xs w.proof)
    if declType.hasMVar || declValue.hasMVar || declValue.hasSorry then
      throwError "incomplete or sorry-containing extracted proof"
    let dstName := dst.getId
    addDecl (.thmDecl {
      name := dstName
      levelParams := ci.levelParams
      type := declType
      value := declValue })
    logInfo m!"generated {dstName}, exact index {cost}"

/-- Pin an indexed proof at an arithmetically equal cost. The equality is
proved by Lean's omega tactic if definitional reduction is insufficient. -/
private def recastCost (orig : Expr) (w : Witness) (cnt : Expr) : TermElabM Expr := do
  let ty ← exactType orig cnt
  if ← withTransparency .all (isDefEq w.cost cnt) then
    return ← mkExpectedTypeHint w.proof ty
  let eq ← mkEq w.cost cnt
  let he ← Term.elabTermEnsuringType (← `(by omega)) eq
  Term.synthesizeSyntheticMVarsNoPostponing
  let he ← instantiateMVars he
  let fam ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    mkLambdaFVars #[n] (← exactType orig n)
  let hc ← mkAppM ``congrArg #[fam,he]
  return ← mkAppM ``Eq.mp #[hc,w.proof]

/-- Replay a top-level Nat.rec/Nat.recAux proof, replacing the motive with
exact reachability at C(k). The source IH is mapped to the new indexed IH;
all primitive and composition witnesses are extracted from the original body. -/
private def extractNatRec (p costFn : Expr) : TermElabM Witness := do
  let p := p.consumeMData
  let args := p.getAppArgs
  let .const nm us := p.getAppFn | throwError "expected Nat induction, found {p}"
  unless nm == ``Nat.rec || nm == ``Nat.recAux do throwError "expected Nat induction, found {nm}"
  unless args.size >= 4 do throwError "incomplete Nat induction"
  let motive := args[0]!
  let base := args[1]!
  let step := args[2]!
  let index := args[3]!
  let tail := args.extract 4 args.size
  let newMotive ← withLocalDeclD `k (mkConst ``Nat) fun k => do
    let old := motive.beta #[k]
    mkLambdaFVars #[k] (← pin (costFn.beta #[k]) old)
  let z := mkNatLit 0
  let base' ← forallTelescope (motive.beta #[z]) fun xs orig => do
    let w ← extract (mkAppN base xs)
    let h ← recastCost orig w (costFn.beta #[z])
    mkLambdaFVars xs h
  let step' ← withLocalDeclD `k (mkConst ``Nat) fun k => do
    withLocalDeclD `ih (newMotive.beta #[k]) fun ih => do
      withLocalDeclD `oldIH (motive.beta #[k]) fun oldIH => do
        let succ := mkApp (mkConst ``Nat.succ) k
        forallTelescope (motive.beta #[succ]) fun xs orig => do
          let w ← extract (mkAppN step (#[k,oldIH] ++ xs)) {inductionHyps := [(oldIH.fvarId!, ih)]}
          let h ← recastCost orig w (costFn.beta #[succ])
          let h ← mkLambdaFVars xs h
          if h.containsFVar oldIH.fvarId! then throwError "old existential IH escaped indexed replay"
          mkLambdaFVars #[k,ih] h
  let h := mkAppN (mkConst nm us) (#[newMotive,base',step',index] ++ tail)
  return ← annotate p ⟨costFn.beta #[index], h⟩

/-- Lift a source induction theorem with one specified cost function of the
recursor index. The input theorem must have Nat.rec as its top-level proof. -/
elab "#extract_induction " src:str " as " dst:ident " cost_by " f:term : command =>
    Command.liftTermElabM do
  let name ← sourceName src.getString.toName
  let ci ← getConstInfo name
  let some body := ci.value? true | throwError "proof body unavailable for {name}"
  let costFn ← Term.elabTermEnsuringType f (← mkArrow (mkConst ``Nat) (mkConst ``Nat))
  forallTelescope ci.type fun xs orig => do
    let w ← extractNatRec (body.beta xs) costFn
    let ty ← exactType orig w.cost
    let declType ← instantiateMVars (← mkForallFVars xs ty)
    let declValue ← instantiateMVars (← mkLambdaFVars xs w.proof)
    if declType.hasMVar || declValue.hasMVar || declValue.hasSorry then
      throwError "incomplete or sorry-containing extracted proof"
    addDecl (.thmDecl {
      name := dst.getId
      levelParams := ci.levelParams
      type := declType
      value := declValue })
    logInfo m!"generated indexed induction {dst.getId}"

/-- Exact companions for previously extracted symbolic proofs. The caller
supplies the original name and the new theorem of identical binders. -/
declare_syntax_cat exactCompanion
syntax str "=>" ident : exactCompanion
elab "#extract_composed " src:str " as " dst:ident " using " "[" ps:exactCompanion,* "]" : command =>
    Command.liftTermElabM do
  let mut deps : List (Name × Name) := []
  for p in ps.getElems do
    match p with
    | `(exactCompanion| $s:str => $t:ident) =>
      deps := (← sourceName s.getString.toName, ← sourceName t.getId) :: deps
    | _ => throwError "invalid exact companion"
  let name ← sourceName src.getString.toName
  let ci ← getConstInfo name
  let cn := mkConst name (ci.levelParams.map Level.param)
  forallTelescope ci.type fun xs orig => do
    let w ← extract (mkAppN cn xs) {companions := deps}
    let ty ← exactType orig w.cost
    unless ← withTransparency .all (isDefEq (← inferType w.proof) ty) do
      throwError "composed proof does not have expected indexed type {ty}"
    let declType ← instantiateMVars (← mkForallFVars xs ty)
    let declValue ← instantiateMVars (← mkLambdaFVars xs w.proof)
    if declType.hasMVar || declValue.hasMVar || declValue.hasSorry then
      throwError "incomplete or sorry-containing extracted proof"
    addDecl (.thmDecl {
      name := dst.getId
      levelParams := ci.levelParams
      type := declType
      value := declValue })
    logInfo m!"generated composed exact theorem {dst.getId}, index {w.cost}"

end BB6.WitnessExtract
