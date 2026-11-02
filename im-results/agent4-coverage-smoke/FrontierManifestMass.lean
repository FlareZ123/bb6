import FrontierExtract
namespace BB6Coverage

def AuditTerminal.certMass (a : AuditTerminal) : Nat :=
  if a.certified then a.weight else 0

def AuditTerminal.openMass (a : AuditTerminal) : Nat :=
  if a.certified then 0 else a.weight

private theorem sum_map_flatMap {α β : Type} (xs : List α) (f : α → List β)
    (w : β → Nat) :
    ((xs.flatMap f).map w).sum =
      (xs.map (fun x => ((f x).map w).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

private theorem foldl_first (xs : List (Nat × Nat)) (a b : Nat) :
    (xs.foldl (fun acc x => (acc.1+x.1, acc.2+x.2)) (a,b)).1 =
      a + (xs.map Prod.fst).sum := by
  induction xs generalizing a b with
  | nil => simp
  | cons hd xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    omega

private theorem foldl_second (xs : List (Nat × Nat)) (a b : Nat) :
    (xs.foldl (fun acc x => (acc.1+x.1, acc.2+x.2)) (a,b)).2 =
      b + (xs.map Prod.snd).sum := by
  induction xs generalizing a b with
  | nil => simp
  | cons hd xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    omega

/-- The sum of certified weights in every emitted manifest is *exactly*
the independently proof-checked report's certified-mass coordinate. -/
theorem FrontierAudit.terminals_certMass {good : Machine → Prop}
    {p : PartialMachine} (audit : FrontierAudit good p)
    (path : List (Slot × Transition)) :
    ((audit.terminals path).map AuditTerminal.certMass).sum = audit.report.1 := by
  induction audit generalizing path with
  | certified p proof =>
      simp [FrontierAudit.terminals, FrontierAudit.report, AuditTerminal.certMass]
  | unresolved p =>
      simp [FrontierAudit.terminals, FrontierAudit.report, AuditTerminal.certMass]
  | branch p slot fresh children ih =>
      simp only [FrontierAudit.terminals, FrontierAudit.report]
      rw [sum_map_flatMap]
      rw [foldl_first]
      simp only [Nat.zero_add]
      simp only [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro x hx
      exact ih x.val x.property (path ++ [(slot,x.val)])

/-- The sum of unresolved weights in every emitted manifest is *exactly*
the independently proof-checked report's open-mass coordinate. -/
theorem FrontierAudit.terminals_openMass {good : Machine → Prop}
    {p : PartialMachine} (audit : FrontierAudit good p)
    (path : List (Slot × Transition)) :
    ((audit.terminals path).map AuditTerminal.openMass).sum = audit.report.2 := by
  induction audit generalizing path with
  | certified p proof =>
      simp [FrontierAudit.terminals, FrontierAudit.report, AuditTerminal.openMass]
  | unresolved p =>
      simp [FrontierAudit.terminals, FrontierAudit.report, AuditTerminal.openMass]
  | branch p slot fresh children ih =>
      simp only [FrontierAudit.terminals, FrontierAudit.report]
      rw [sum_map_flatMap]
      rw [foldl_second]
      simp only [Nat.zero_add]
      simp only [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro x hx
      exact ih x.val x.property (path ++ [(slot,x.val)])

theorem FrontierAudit.terminalMass_conserves {good : Machine → Prop}
    {p : PartialMachine} (audit : FrontierAudit good p) :
    ((audit.terminals).map AuditTerminal.certMass).sum +
      ((audit.terminals).map AuditTerminal.openMass).sum =
        cylinderMass p := by
  rw [audit.terminals_certMass [], audit.terminals_openMass []]
  exact audit.report_conserves

#print axioms FrontierAudit.terminals_certMass
#print axioms FrontierAudit.terminals_openMass
#print axioms FrontierAudit.terminalMass_conserves
end BB6Coverage
