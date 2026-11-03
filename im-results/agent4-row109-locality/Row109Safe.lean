import Row109Rules

namespace BB6.Row109Locality

-- State 6 records the first query of the missing B/1 transition.
theorem step_halt_sticky (c : Cfg) (h : c.st = 6) : (step c).st = 6 := by
  simp [step, action, h]

theorem run_halt_sticky (n : Nat) (c : Cfg) (h : c.st = 6) :
    (run n c).st = 6 := by
  induction n with
  | zero => exact h
  | succ n ih => exact step_halt_sticky _ ih

theorem run_add (m n : Nat) (c : Cfg) :
    run (m + n) c = run n (run m c) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    calc
      run (m + (n+1)) c = step (run (m+n) c) := by rw [Nat.add_succ]; rfl
      _ = step (run n (run m c)) := congrArg step ih
      _ = run (n+1) (run m c) := rfl

theorem accepted_no_halt (r : Certificate)
    (hcert : accepted r = true)
    (hfinal : r.finalState < 6)
    (t : Int → Bool)
    (ht : ∀ p, InWindow r.lo r.hi p → t p = wordTape r.beforeBits p)
    (k : Nat) (hk : k ≤ r.steps) :
    (run k { st := r.initialState, h := r.initialHead, tape := t }).st ≠ 6 := by
  let c : Cfg := { st := r.initialState, h := r.initialHead, tape := t }
  have hf : (run r.steps c).st = r.finalState := (accepted_sound r hcert t ht).1
  intro hb
  have heq : k + (r.steps - k) = r.steps := by omega
  have hst := run_halt_sticky (r.steps-k) (run k c) hb
  rw [← heq, run_add] at hf
  rw [hst] at hf
  omega

theorem all_rules_final_states :
    allRules.all (fun r => decide (r.finalState < 6)) = true := by decide

theorem all_rules_no_halt (r : Certificate) (hr : r ∈ allRules)
    (t : Int → Bool)
    (ht : ∀ p, InWindow r.lo r.hi p → t p = wordTape r.beforeBits p)
    (k : Nat) (hk : k ≤ r.steps) :
    (run k { st := r.initialState, h := r.initialHead, tape := t }).st ≠ 6 := by
  have hcert : accepted r = true := (List.all_eq_true.mp all_valid) r hr
  have hf : r.finalState < 6 :=
    decide_eq_true_eq.mp ((List.all_eq_true.mp all_rules_final_states) r hr)
  exact accepted_no_halt r hcert hf t ht k hk

#print axioms all_rules_no_halt
end BB6.Row109Locality
