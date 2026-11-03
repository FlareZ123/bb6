import DRegular

namespace DRegular

/-- The derived right-section return map is a deterministic transition
    relation. Predicates inductive under it propagate to each finite iterate
    on which the regular-language expression remains defined. -/
theorem closed_through_run (P : L → Prop)
    (hclosed : ∀ s t, P s → next s = some t → P t)
    (n : Nat) (s t : L) (hstart : P s)
    (hr : run n s = some t) : P t := by
  induction n generalizing s with
  | zero =>
    simp only [run] at hr
    cases hr
    exact hstart
  | succ n ih =>
    cases hstep : next s with
    | none => simp [run, hstep] at hr
    | some u =>
      have ht : run n u = some t := by simpa [run, hstep] using hr
      exact ih u (hclosed s u hstart hstep) ht

/-- The recurrence admits right-associated composition. -/
theorem run_succ_right (n : Nat) (s : L) :
    run (n+1) s = (run n s).bind next := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    change (next s).bind (run (n+1)) =
      ((next s).bind (run n)).bind next
    cases h : next s with
    | none => simp
    | some u => simp [ih]

/-- No assertion solely on the regular language can simultaneously contain
    the modeled seed5, remain inductively closed, and guarantee that the next
    modeled return stays in this language forever. This is a finite model
    obstruction, not a proof that the real machine reaches the exceptional gate. -/
theorem no_safe_closed_regular_seed5
    (P : L → Prop) (hseed : P seed5)
    (hclosed : ∀ s t, P s → next s = some t → P t)
    (hsafe : ∀ s, P s → (next s).isSome = true) : False := by
  have hlen := seed5_survives_1711
  have hs : run 1711 seed5 = some terminal5 := by
    cases h : run 1711 seed5 with
    | none => simp [h] at hlen
    | some u => simp [terminal5, h]
  have hp : P terminal5 := closed_through_run P hclosed 1711
    seed5 terminal5 hseed hs
  have hn : next terminal5 = none := by
    have hterm := seed5_exact_exception.2.2.2
    rw [show 1712 = 1711+1 by decide, run_succ_right, hs] at hterm
    simpa using hterm
  have hh := hsafe terminal5 hp
  simp [hn] at hh

#print axioms closed_through_run
#print axioms run_succ_right
#print axioms no_safe_closed_regular_seed5

end DRegular
