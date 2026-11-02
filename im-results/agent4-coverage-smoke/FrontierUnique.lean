import FrontierExtract
namespace BB6Coverage

/-- Every exported leaf path includes all decisions on the branch that led
to it. -/
theorem FrontierAudit.terminal_extends {good : Machine → Prop}
    {p : PartialMachine} (audit : FrontierAudit good p) (path : List (Slot × Transition))
    (term : AuditTerminal) (ht : term ∈ audit.terminals path) :
    ∀ s t, (s,t) ∈ path → (s,t) ∈ term.path := by
  induction audit generalizing path term with
  | certified p proof =>
      have he : term = ⟨path,true,cylinderMass p⟩ := by
        simpa [FrontierAudit.terminals] using ht
      subst term
      exact fun _ _ h => h
  | unresolved p =>
      have he : term = ⟨path,false,cylinderMass p⟩ := by
        simpa [FrontierAudit.terminals] using ht
      subst term
      exact fun _ _ h => h
  | branch p slot fresh children ih =>
      simp only [FrontierAudit.terminals] at ht
      obtain ⟨x, hmem, hx⟩ := List.mem_flatMap.mp ht
      have hsub := ih x.val x.property (path ++ [(slot,x.val)]) term hx
      intro s t hs
      exact hsub s t (List.mem_append.mpr (Or.inl hs))

def AuditTerminal.matches (term : AuditTerminal) (m : Machine) : Prop :=
  ∀ s t, (s,t) ∈ term.path → m s = t

/-- No one full machine matches two distinct manifest leaves, regardless
of the shape of the search. This formalizes disjointness of the *actual*
reported cylinders, including halting transitions and multi-level branches. -/
theorem FrontierAudit.terminals_unique {good : Machine → Prop}
    {p : PartialMachine} (audit : FrontierAudit good p)
    (path : List (Slot × Transition)) (m : Machine)
    (x y : AuditTerminal) (hx : x ∈ audit.terminals path)
    (hy : y ∈ audit.terminals path)
    (hxm : x.matches m) (hym : y.matches m) : x = y := by
  induction audit generalizing path x y with
  | certified p proof =>
      have h1 : x = ⟨path,true,cylinderMass p⟩ := by
        simpa [FrontierAudit.terminals] using hx
      have h2 : y = ⟨path,true,cylinderMass p⟩ := by
        simpa [FrontierAudit.terminals] using hy
      exact h1.trans h2.symm
  | unresolved p =>
      have h1 : x = ⟨path,false,cylinderMass p⟩ := by
        simpa [FrontierAudit.terminals] using hx
      have h2 : y = ⟨path,false,cylinderMass p⟩ := by
        simpa [FrontierAudit.terminals] using hy
      exact h1.trans h2.symm
  | branch p slot fresh children ih =>
      simp only [FrontierAudit.terminals] at hx hy
      obtain ⟨u, hum, hu⟩ := List.mem_flatMap.mp hx
      obtain ⟨v, hvm, hv⟩ := List.mem_flatMap.mp hy
      have hxu := (children u.val u.property).terminal_extends
        (path ++ [(slot,u.val)]) x hu slot u.val
        (List.mem_append.mpr (Or.inr (by simp)))
      have hyv := (children v.val v.property).terminal_extends
        (path ++ [(slot,v.val)]) y hv slot v.val
        (List.mem_append.mpr (Or.inr (by simp)))
      have hequ : m slot = u.val := hxm slot u.val hxu
      have heqv : m slot = v.val := hym slot v.val hyv
      have huv : u = v := by
        apply Subtype.ext
        exact hequ.symm.trans heqv
      subst v
      exact ih u.val u.property (path ++ [(slot,u.val)]) x y hu hv hxm hym

/-- A full table has one uniquely determined corresponding terminal in a
proof-carrying report. Completeness and uniqueness are kernel theorems. -/
theorem FrontierAudit.unique_actual_terminal {good : Machine → Prop}
    {p : PartialMachine} (audit : FrontierAudit good p)
    (m : Machine) (hm : compatible p m) :
    ∃ term : AuditTerminal, term ∈ audit.terminals ∧ term.matches m ∧
      (∀ other : AuditTerminal, other ∈ audit.terminals →
        other.matches m → other = term) := by
  obtain ⟨term, hmem, hcorrect⟩ := audit.has_actual_terminal m hm
  refine ⟨term, hmem, hcorrect, ?_⟩
  intro other homem hocorrect
  exact audit.terminals_unique [] m other term homem hmem hocorrect hcorrect

#print axioms FrontierAudit.terminal_extends
#print axioms FrontierAudit.terminals_unique
#print axioms FrontierAudit.unique_actual_terminal
end BB6Coverage
