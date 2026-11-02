import Lean.Elab.Tactic.Omega
import Boundary
import TokenCode

set_option maxHeartbeats 3000000
namespace BB6.Agent35

/-- Identify the original machine's terminal state 6 with the other
    interpreter's frozen F-on-1 terminal configuration. -/
def toA : CryptidBoundary.Cfg → CryptidA.Cfg
  | ⟨l,h,r,st⟩ => if st = 6 then ⟨l,true,r,5⟩ else ⟨l,h,r,st⟩

/-- An F-on-0 output uniquely identifies the original (nonterminal) source state. -/
theorem toA_finish (s : CryptidBoundary.Cfg) (r : List Bool)
    (h : toA s = (⟨[],false,r,5⟩ : CryptidA.Cfg)) :
    s = (⟨[],false,r,5⟩ : CryptidBoundary.Cfg) := by
  rcases s with ⟨l,hd,rs,st⟩
  by_cases hs : st = 6
  · simp [toA, hs] at h
  · simp [toA, hs] at h
    rcases h with ⟨h1,h2,h3,h4⟩
    simp [h1,h2,h3,h4]

/-- All raw transitions commute, including the differently represented halt. -/
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
            | succ st =>
              cases st with
              | zero => cases h <;> rfl
              | succ st => cases h <;> simp [toA, CryptidBoundary.step, CryptidA.step]

/-- All finite runs commute with the encoding, without a nonhalting hypothesis. -/
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

/-- A converted A-on-zero section uniquely identifies its source state. -/
theorem toA_aBoundary_converse (s : CryptidBoundary.Cfg)
    (m : Nat) (ys : List Bool)
    (h : toA s = CryptidA.ab m ys) : s = aBoundary m ys := by
  rcases s with ⟨l,hd,rs,st⟩
  by_cases hs : st = 6
  · simp [toA, hs, CryptidA.ab] at h
  · simp [toA, hs, CryptidA.ab] at h
    rcases h with ⟨h1,h2,h3,h4⟩
    simp [aBoundary, pairs_pat, h1,h2,h3,h4]

/-- An arbitrary encoded word is consumed by the exact original-machine
    interpreter in the same number of primitive transitions. -/
theorem a_code_return (m : Nat) (ws ys : List Bool) :
    CryptidBoundary.run (CryptidA.wordCost m ws)
      (aBoundary m (CryptidA.wordCode ws ++ ys)) =
      aBoundary (m+CryptidA.wordInc ws) ys := by
  apply toA_aBoundary_converse
  rw [toA_run, toA_aBoundary]
  exact CryptidA.consume_code m ws ys

theorem code_then_zero (m : Nat) (ws ys : List Bool) :
  CryptidA.run (CryptidA.wordCost m ws +
      (2*(m+CryptidA.wordInc ws)+6))
    (CryptidA.ab m (CryptidA.wordCode ws ++ (false::ys))) =
      CryptidA.finish (2*(m+CryptidA.wordInc ws)+5) ys := by
  rw [CryptidA.run_add, CryptidA.consume_code]
  exact CryptidA.close_double_zero _ _

/-- Uniform original-machine F-to-F return for any finite coded combination
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
  apply toA_finish
  rw [toA_run, toA_aBoundary]
  change CryptidA.run _ (CryptidA.ab (4*k+3)
    (CryptidA.wordCode ws ++ (false::ys))) =
    CryptidA.finish (2*((4*k+3)+CryptidA.wordInc ws)+5) ys
  exact code_then_zero (4*k+3) ws ys

#print axioms toA_step
#print axioms toA_run
#print axioms a_code_return
#print axioms full_A_code
end BB6.Agent35
