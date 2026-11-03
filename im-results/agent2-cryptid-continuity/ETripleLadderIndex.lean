import Lean.Elab.Tactic.Omega
import ETripleLadderSource

namespace BB6.ETripleLadderIndex
open CryptidBoundary
open BB6.ETripleLadderSource
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem index_plus_one (m u : Nat) :
    kIndex m u + 1 = 3^m * (u+1) := by
  induction m with
  | zero => simp [kIndex]
  | succ m ih =>
    change 3*kIndex m u + 2 + 1 = 3^(m+1)*(u+1)
    calc
      _ = 3*(kIndex m u+1) := by omega
      _ = 3*(3^m*(u+1)) := congrArg (fun z : Nat => 3*z) ih
      _ = _ := by rw [Nat.pow_succ']; simp [Nat.mul_assoc]

theorem end_plus_one (m u : Nat) :
    endU m u+1=8^m*(u+1) := by
  induction m generalizing u with
  | zero => simp [endU]
  | succ m ih =>
    simp only [endU]
    rw [ih]
    have ha : 8*u+7+1=8*(u+1) := by omega
    rw [ha, Nat.pow_succ']
    simp only [Nat.mul_assoc]
    ac_rfl

theorem input_unary_length (m u : Nat) :
    3*kIndex m u+4 = 3^(m+1)*(u+1)+1 := by
  have h := congrArg (fun z : Nat => 3*z+1) (index_plus_one m u)
  have heq : 3*kIndex m u+4=3*(kIndex m u+1)+1 := by omega
  rw [heq, h, Nat.pow_succ']
  ac_rfl

theorem output_unary_length (m u : Nat) :
    3*endU m u+4 = 3*8^m*(u+1)+1 := by
  have h := congrArg (fun z : Nat => 3*z+1) (end_plus_one m u)
  have heq : 3*endU m u+4=3*(endU m u+1)+1 := by omega
  rw [heq, h]
  ac_rfl

def physicalSection (n q p : Nat) (ys : List Bool) : Cfg :=
  ⟨[],false,List.replicate n true ++
    (false::(pairs q ++ (List.replicate (3*p+3) true ++ false::ys))),5⟩

theorem level_eq_section (m u q : Nat) (ys : List Bool) :
    level m u q ys = physicalSection (3^(m+1)*(u+1)+1) q m ys := by
  simp only [level,stage,init,physicalSection, Cfg.mk.injEq,
    true_and, and_true]
  rw [← input_unary_length m u]
  have hr : List.replicate (3*kIndex m u+4) true =
      [true,true] ++ List.replicate (3*kIndex m u+2) true := by
    rw [show 3*kIndex m u+4=2+(3*kIndex m u+2) by omega,
      ←List.replicate_append_replicate]
    rfl
  rw [hr]
  simp only [List.cons_append, List.nil_append, List.append_assoc]


/-- A closed-form statement, in the actual original Turing-machine step function,
    of arbitrary-depth exceptional first-return ladder endpoints. -/
theorem power_ladder_source (m u q : Nat) (ys : List Bool) :
    run (totalCost m u q)
      (physicalSection (3^(m+1)*(u+1)+1) q m ys) =
    physicalSection (3*8^m*(u+1)+1) (q+2*m) 0 ys := by
  calc
    _ = level 0 (endU m u) (q+2*m) ys := by
      rw [←level_eq_section m u q ys]
      exact level_run m u q ys
    _ = physicalSection (3^(0+1)*(endU m u+1)+1) (q+2*m) 0 ys :=
      level_eq_section 0 (endU m u) (q+2*m) ys
    _ = _ := by
      have hh : 3^(0+1)*(endU m u+1)+1=3*8^m*(u+1)+1 := by
        simp only [Nat.zero_add, Nat.pow_one]
        rw [end_plus_one]
        ac_rfl
      rw [hh]

#print axioms power_ladder_source
#print axioms index_plus_one
#print axioms end_plus_one
#print axioms input_unary_length
#print axioms output_unary_length
#print axioms level_eq_section
end BB6.ETripleLadderIndex
