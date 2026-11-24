module
public import SourceCostModel
public import Lean

@[expose] public section
open Lean Meta Elab Tactic BusyBeaver.SymRunEngine BB6.Agent11.SourceCost
namespace BB6.Agent26.SourceAffine
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- The stepwise proof keeps kernel reduction local to one transition. -/
theorem costIter_local (flag : Bool) (n : Nat) (s : SymState) (c : Nat) (s' : SymState) (rest : Nat)
    (hc : costPure flag s = c) (hs : stepPure s = s') (hr : costIter flag n s' = rest) :
    costIter flag (n+1) s = c + rest := by
  rw [costIter, hc, hs, hr]

/-- Reduce only constructor spines of state data, leaving natural parameters symbolic. -/
meta partial def normalizeStateData (e : Expr) : MetaM Expr := do
  let e ← whnf e
  let fn := e.getAppFn
  let args := e.getAppArgs
  let .const nm _ := fn | return e
  if nm == ``Prod.mk || nm == ``List.cons then
    let n := args.size
    return mkAppN fn (args.set! (n-2) (← normalizeStateData args[n-2]!) |>.set! (n-1) (← normalizeStateData args[n-1]!))
  else if nm == ``SymTok.item then
    return mkApp fn (← normalizeStateData args[0]!)
  else
    return e

/-- Construct a checked equality one symbolic transition at a time, then leave
    a pure Nat arithmetic goal. No global simplification of costIter is needed. -/
elab "normalize_cost" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← g.getType
    let eqArgs := target.getAppArgs
    let costIterExpr := eqArgs[1]!
    let args := costIterExpr.getAppArgs
    let some n ← getNatValue? args[1]! | throwError "not literal"
    let flag := args[0]!
    let mut s := args[2]!
    let mut steps : Array (Expr × Expr × Expr) := #[]
    for _ in [0:n] do
      let c ← whnf (mkApp2 (mkConst ``BB6.Agent11.SourceCost.costPure) flag s)
      let s' ← normalizeStateData (mkApp (mkConst ``BusyBeaver.SymRunEngine.stepPure) s)
      steps := steps.push (s,c,s')
      s := s'
    let mut total := mkNatLit 0
    let mut proof ← mkEqRefl total
    for i in [0:n] do
      let (cur,c,s') := steps[n-i-1]!
      let hc ← mkEqRefl c
      let hs ← mkEqRefl s'
      proof := mkAppN (mkConst ``costIter_local) #[flag,mkNatLit i,cur,c,s',total,hc,hs,proof]
      total := mkApp2 (mkConst ``Nat.add) c total
    let rhs := eqArgs[2]!
    let arithTy ← mkEq total rhs
    let arith ← mkFreshExprSyntheticOpaqueMVar arithTy
    let result := mkAppN (mkConst ``Eq.trans [Level.one]) #[mkConst ``Nat,costIterExpr,total,rhs,proof,arith]
    g.assign result
    replaceMainGoal [arith.mvarId!]

theorem a0_true (k d : Nat) (R_tail : List SymTok) :
    costIter true 46 (stateA0 (k+1) (d+6) R_tail) = 32*k + 314 := by
  normalize_cost
  simp only [Nat.add_eq, Nat.mul_eq, fcost, Bool.false_eq_true, ite_false, ite_true]
  omega

#print axioms a0_true

theorem a0_false (k d : Nat) (R_tail : List SymTok) :
    costIter false 46 (stateA0 (k+1) (d+6) R_tail) = 28*k + 284 := by
  normalize_cost
  simp only [Nat.add_eq, Nat.mul_eq, fcost, Bool.false_eq_true, ite_false, ite_true]
  omega

#print axioms a0_false

theorem a_true (m k d : Nat) (R_tail : List SymTok) :
    costIter true 66 (stateA m (k+1) (d+6) R_tail) = 140*m+32*k+454 := by
  normalize_cost
  simp only [Nat.add_eq, Nat.mul_eq, fcost, Bool.false_eq_true, ite_false, ite_true]
  omega

#print axioms a_true

theorem a_false (m k d : Nat) (R_tail : List SymTok) :
    costIter false 66 (stateA m (k+1) (d+6) R_tail) = 124*m+28*k+408 := by
  normalize_cost
  simp only [Nat.add_eq, Nat.mul_eq, fcost, Bool.false_eq_true, ite_false, ite_true]
  omega

#print axioms a_false

theorem c_true (p k d : Nat) (R_tail : List SymTok) :
    costIter true 46 (stateC (p+3) (k+1) d R_tail) = 76*p+64*k+486 := by
  normalize_cost
  simp only [Nat.add_eq, Nat.mul_eq, fcost, Bool.false_eq_true, ite_false, ite_true]
  omega

#print axioms c_true

theorem c_false (p k d : Nat) (R_tail : List SymTok) :
    costIter false 46 (stateC (p+3) (k+1) d R_tail) = 68*p+56*k+434 := by
  normalize_cost
  simp only [Nat.add_eq, Nat.mul_eq, fcost, Bool.false_eq_true, ite_false, ite_true]
  omega

#print axioms c_false

theorem bAA_true (p m k d : Nat) (R_tail : List SymTok) :
    costIter true 126 (stateB sep3A sep3A (p+1) (m+2) (k+1) d R_tail) = 152*p+140*m+32*k+1048 := by
  normalize_cost
  simp only [Nat.add_eq, Nat.mul_eq, fcost, Bool.false_eq_true, ite_false, ite_true]
  omega

#print axioms bAA_true

theorem bAA_false (p m k d : Nat) (R_tail : List SymTok) :
    costIter false 126 (stateB sep3A sep3A (p+1) (m+2) (k+1) d R_tail) = 136*p+124*m+28*k+942 := by
  normalize_cost
  simp only [Nat.add_eq, Nat.mul_eq, fcost, Bool.false_eq_true, ite_false, ite_true]
  omega

#print axioms bAA_false

theorem bAB_true (p m k d : Nat) (R_tail : List SymTok) :
    costIter true 118 (stateB sep3A sep3B (p+1) (m+2) (k+1) d R_tail) = 152*p+140*m+32*k+978 := by
  normalize_cost
  simp only [Nat.add_eq, Nat.mul_eq, fcost, Bool.false_eq_true, ite_false, ite_true]
  omega

#print axioms bAB_true

theorem bAB_false (p m k d : Nat) (R_tail : List SymTok) :
    costIter false 118 (stateB sep3A sep3B (p+1) (m+2) (k+1) d R_tail) = 136*p+124*m+28*k+880 := by
  normalize_cost
  simp only [Nat.add_eq, Nat.mul_eq, fcost, Bool.false_eq_true, ite_false, ite_true]
  omega

#print axioms bAB_false

theorem bBA_true (p m k d : Nat) (R_tail : List SymTok) :
    costIter true 106 (stateB sep3B sep3A (p+1) (m+2) (k+1) d R_tail) = 152*p+140*m+32*k+896 := by
  normalize_cost
  simp only [Nat.add_eq, Nat.mul_eq, fcost, Bool.false_eq_true, ite_false, ite_true]
  omega

#print axioms bBA_true

theorem bBA_false (p m k d : Nat) (R_tail : List SymTok) :
    costIter false 106 (stateB sep3B sep3A (p+1) (m+2) (k+1) d R_tail) = 136*p+124*m+28*k+806 := by
  normalize_cost
  simp only [Nat.add_eq, Nat.mul_eq, fcost, Bool.false_eq_true, ite_false, ite_true]
  omega

#print axioms bBA_false

theorem bBB_true (p m k d : Nat) (R_tail : List SymTok) :
    costIter true 98 (stateB sep3B sep3B (p+1) (m+2) (k+1) d R_tail) = 152*p+140*m+32*k+826 := by
  normalize_cost
  simp only [Nat.add_eq, Nat.mul_eq, fcost, Bool.false_eq_true, ite_false, ite_true]
  omega

#print axioms bBB_true

theorem bBB_false (p m k d : Nat) (R_tail : List SymTok) :
    costIter false 98 (stateB sep3B sep3B (p+1) (m+2) (k+1) d R_tail) = 136*p+124*m+28*k+744 := by
  normalize_cost
  simp only [Nat.add_eq, Nat.mul_eq, fcost, Bool.false_eq_true, ite_false, ite_true]
  omega

#print axioms bBB_false

end BB6.Agent26.SourceAffine

end
