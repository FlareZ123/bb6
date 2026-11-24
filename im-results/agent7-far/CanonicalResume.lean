import CanonicalAudit
namespace BB6Coverage.Canonical

/-- A refinement policy may supply any independently checked audit for a residual leaf. -/
abbrev Policy (bound : Nat) := ∀ (k : Nat) (p : PartialMachine), Scoped k p →
  (0<k ∧ k≤6) → Audit bound p k

def Audit.resume {bound : Nat} (policy : Policy bound) {p : PartialMachine} {k : Nat}
    (a : Audit bound p k) (hp : Scoped k p) (hk : 0<k ∧ k≤6) : Audit bound p k :=
  match a with
  | .certified p k c => .certified p k c
  | .unresolved p k => policy k p hp hk
  | .branch p k s fresh scope hs hks kids =>
      .branch p k s fresh scope hs hks (fun t ht =>
        (kids t ht).resume policy (scoped_refine k p s t scope hs) (nextK_bounds k t hks))

/-- Resumption cannot reopen a machine whose canonical path already ended at a certificate. -/
theorem Audit.resume_open_subset {bound : Nat} (policy : Policy bound) {p : PartialMachine} {k : Nat}
    (a : Audit bound p k) (hp : Scoped k p) (hk : 0<k ∧ k≤6) (m : Machine) :
    (a.resume policy hp hk).open m → a.open m := by
  induction a generalizing m with
  | certified p k cert => simp [Audit.resume, Audit.open]
  | unresolved p k => simp [Audit.open]
  | branch p k s fresh scope hs hks kids ih =>
      intro h
      exact ih (normalize k m s s) (normalize_choice k m s hs)
        (scoped_refine k p s _ scope hs) (nextK_bounds k _ hks) (normalize k m s) h

private theorem fold_snd (xs : List (Nat × Nat)) (a b : Nat) :
    (xs.foldl addPair (a,b)).2 = b+(xs.map Prod.snd).sum := by
  induction xs generalizing a b with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons,List.map_cons,List.sum_cons]
    rw [show addPair (a,b) hd = (a+hd.1,b+hd.2) by rfl, ih]
    omega

/-- Resumption is monotonically improving in the exact weighted mass report. -/
theorem Audit.resume_mass_le {bound : Nat} (policy : Policy bound) {p : PartialMachine} {k : Nat}
    (a : Audit bound p k) (hp : Scoped k p) (hk : 0<k ∧ k≤6) :
    (a.resume policy hp hk).report.2 ≤ a.report.2 := by
  induction a with
  | certified p k c => exact Nat.le_refl _
  | unresolved p k =>
      have h := (policy k p hp hk).conserves
      simp only [Audit.resume,Audit.report]
      omega
  | branch p k s fresh scope hs hks kids ih =>
      simp only [Audit.resume, Audit.report, fold_snd, Nat.zero_add]
      let ts := (canonChoices k).attach
      change ((ts.map fun t => scalePair (weight k t.val)
          ((kids t.val t.property).resume policy (scoped_refine k p s t.val scope hs)
             (nextK_bounds k t.val hks)).report).map Prod.snd).sum ≤
        ((ts.map fun t => scalePair (weight k t.val) (kids t.val t.property).report).map Prod.snd).sum
      induction ts with
      | nil => simp
      | cons hd tl iht =>
          simp only [List.map_cons,List.sum_cons,scalePair]
          exact Nat.add_le_add (Nat.mul_le_mul_left _ (ih hd.val hd.property
            (scoped_refine k p s hd.val scope hs) (nextK_bounds k hd.val hks))) iht

/-- Raw transition choices actually represented by each canonical child. -/
def normTransition (k : Nat) (t : Transition) : Transition :=
  t.map (renameMove (normPerm k t))

def fiberSize (k : Nat) (t : Transition) : Nat :=
  (choices.filter (fun u => decide (normTransition k u = t))).length

theorem fiber_weight (k : Nat) (t : Transition) (hk : 0<k ∧ k≤6)
    (ht : t ∈ canonChoices k) : fiberSize k t = weight k t := by
  have h : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 := by omega
  have hcheck (j : Nat) (hj : j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6) :
      ((canonChoices j).all fun v => decide (fiberSize j v = weight j v)) = true := by
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact of_decide_eq_true (List.all_eq_true.mp (hcheck k h) t ht)

#print axioms Audit.resume_open_subset
#print axioms Audit.resume_mass_le
#print axioms fiber_weight
end BB6Coverage.Canonical
