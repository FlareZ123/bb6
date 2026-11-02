import FrontierAudit

namespace BB6Coverage

structure AuditTerminal where
  path : List (Slot × Transition)
  certified : Bool
  weight : Nat

/-- A complete machine-readable manifest of every leaf in a finite audit:
its actual split decisions, certified/open flag, and exact full-table mass. -/
def FrontierAudit.terminals {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p) (path : List (Slot × Transition) := []) :
    List AuditTerminal :=
  match audit with
  | .certified p _ => [{path := path, certified := true, weight := cylinderMass p}]
  | .unresolved p => [{path := path, certified := false, weight := cylinderMass p}]
  | .branch _ slot _ children =>
      choices.attach.flatMap (fun t =>
        (children t.val t.property).terminals (path ++ [(slot, t.val)]))

def FrontierAudit.terminalCount {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p) : Nat := (audit.terminals).length

/-- Every compatible total machine is represented by an actual manifest
terminal. Its entire decision path agrees with the machine's transitions. -/
theorem FrontierAudit.has_terminal {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p) (m : Machine) (hm : compatible p m)
    (path : List (Slot × Transition))
    (hpath : ∀ s t, (s,t) ∈ path → m s = t) :
    ∃ terminal ∈ audit.terminals path,
      ∀ s t, (s,t) ∈ terminal.path → m s = t := by
  induction audit generalizing path with
  | certified p proof =>
      exact ⟨⟨path,true,cylinderMass p⟩, by simp [FrontierAudit.terminals], hpath⟩
  | unresolved p =>
      exact ⟨⟨path,false,cylinderMass p⟩, by simp [FrontierAudit.terminals], hpath⟩
  | branch p slot fresh children ih =>
      have hchild : compatible (refine p slot (m slot)) m :=
        compatible_refine p m slot hm
      have hprefix : ∀ s t, (s,t) ∈ path ++ [(slot,m slot)] → m s = t := by
        intro s t h
        rcases List.mem_append.mp h with h | h
        · exact hpath s t h
        · have he : (s,t) = (slot,m slot) := by simpa using h
          cases he
          rfl
      obtain ⟨terminal, hmem, hcorrect⟩ :=
        ih (m slot) (choices_complete (m slot))
          hchild (path ++ [(slot,m slot)]) hprefix
      refine ⟨terminal, ?_, hcorrect⟩
      simp only [FrontierAudit.terminals]
      exact List.mem_flatMap.mpr ⟨⟨m slot,choices_complete (m slot)⟩,
        by simp, hmem⟩

theorem FrontierAudit.has_actual_terminal {good : Machine → Prop}
    {p : PartialMachine} (audit : FrontierAudit good p)
    (m : Machine) (hm : compatible p m) :
    ∃ terminal ∈ audit.terminals,
      ∀ s t, (s,t) ∈ terminal.path → m s = t := by
  exact audit.has_terminal m hm [] (by simp)

#print axioms FrontierAudit.has_terminal
#print axioms FrontierAudit.has_actual_terminal
end BB6Coverage
