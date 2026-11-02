import Lean.Elab.Tactic.Omega
import Boundary
import TokenCode

set_option maxHeartbeats 3000000
namespace BB6.Agent35

/-- Convert Agent 31's configuration representation to Agent 25's. -/
def toA : CryptidBoundary.Cfg → CryptidA.Cfg
  | ⟨l,h,r,st⟩ => ⟨l,h,r,st⟩

theorem toA_injective : Function.Injective toA := by
  intro x y heq
  cases x with
  | mk l h r st =>
    cases y with
    | mk l' h' r' st' =>
      simp only [toA, CryptidA.Cfg.mk.injEq] at heq
      rcases heq with ⟨h1,h2,h3,h4⟩
      simp [h1,h2,h3,h4]

/-- One raw six-state transition is exactly the same in the two sources. -/
theorem toA_step (s : CryptidBoundary.Cfg) :
    toA (CryptidBoundary.step s) = CryptidA.step (toA s) := by
  rcases s with ⟨l,h,r,st⟩
  cases st with
  | zero => cases h <;> cases r <;> rfl
  | succ st =>
    cases st with
    | zero => cases h <;> cases l <;> cases r <;> rfl
    | succ st =>
      cases st with
      | zero => cases h <;> cases l <;> rfl
      | succ st =>
        cases st with
        | zero => cases h <;> cases l <;> rfl
        | succ st =>
          cases st with
          | zero => cases h <;> cases l <;> rfl
          | succ st =>
            cases st with
            | zero => cases h <;> cases l <;> rfl
            | succ st => cases h <;> rfl

/-- Raw-time simulation commutes with the source conversion, for all steps. -/
theorem toA_run (n : Nat) (s : CryptidBoundary.Cfg) :
    toA (CryptidBoundary.run n s) = CryptidA.run n (toA s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [CryptidBoundary.run_add n 1, CryptidA.run_add n 1]
    change toA (CryptidBoundary.step (CryptidBoundary.run n s)) =
      CryptidA.step (CryptidA.run n (toA s))
    rw [toA_step, ih]

theorem pairs_pat (m : Nat) :
    CryptidBoundary.pairs m = CryptidA.pat m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [CryptidBoundary.pairs, CryptidA.pat, ih]

def aBoundary (m : Nat) (ys : List Bool) : CryptidBoundary.Cfg :=
  ⟨false::CryptidBoundary.pairs m ++ [true,true], false, ys, 0⟩

theorem toA_aBoundary (m : Nat) (ys : List Bool) :
    toA (aBoundary m ys) = CryptidA.ab m ys := by
  simp [aBoundary, toA, CryptidA.ab, pairs_pat]

theorem code_then_zero (m : Nat) (ws ys : List Bool) :
  CryptidA.run (CryptidA.wordCost m ws +
      (2*(m+CryptidA.wordInc ws)+6))
    (CryptidA.ab m (CryptidA.wordCode ws ++ (false::ys))) =
      CryptidA.finish (2*(m+CryptidA.wordInc ws)+5) ys := by
  rw [CryptidA.run_add, CryptidA.consume_code]
  exact CryptidA.close_double_zero _ _

/-- An exact original-machine F-to-F return for every finite coded combination
    of 10 and 111 symbols, followed by a zero and an arbitrary suffix. -/
theorem full_A_code (k : Nat) (ws ys : List Bool) :
  CryptidBoundary.run
    ((12*k*k+41*k+32) +
       (CryptidA.wordCost (4*k+3) ws +
         (2*((4*k+3)+CryptidA.wordInc ws)+6)))
    (CryptidBoundary.init
      (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode ws ++ (false::ys)))) =
    ⟨[], false,
      List.replicate (2*((4*k+3)+CryptidA.wordInc ws)+5) true ++ ys, 5⟩ := by
  rw [CryptidBoundary.run_add, CryptidBoundary.prefix_A]
  change CryptidBoundary.run
    (CryptidA.wordCost (4*k+3) ws +
      (2*((4*k+3)+CryptidA.wordInc ws)+6))
    (aBoundary (4*k+3)
      (CryptidA.wordCode ws ++ (false::ys))) = _
  apply toA_injective
  rw [toA_run, toA_aBoundary]
  change CryptidA.run _ (CryptidA.ab (4*k+3)
    (CryptidA.wordCode ws ++ (false::ys))) =
    CryptidA.finish (2*((4*k+3)+CryptidA.wordInc ws)+5) ys
  exact code_then_zero (4*k+3) ws ys

#print axioms toA_step
#print axioms toA_run
#print axioms full_A_code
end BB6.Agent35
