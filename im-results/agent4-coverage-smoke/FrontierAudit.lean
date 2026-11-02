import Frontier

namespace BB6Coverage

/-- Partition compatible total machines into certified and explicitly unresolved
leaves; a branch enumerates every real transition outcome at an open slot. -/
inductive FrontierAudit (good : Machine → Prop) : PartialMachine → Type where
  | certified (p : PartialMachine) (proof : Cover good p) : FrontierAudit good p
  | unresolved (p : PartialMachine) : FrontierAudit good p
  | branch (p : PartialMachine) (slot : Slot) (fresh : p slot = none)
      (children : ∀ t, t ∈ choices → FrontierAudit good (refine p slot t)) :
      FrontierAudit good p

/-- A full machine lies in exactly one branch selected by its actual
transition. Open means the terminal branch has no proof. -/
def FrontierAudit.open {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p) (m : Machine) : Prop :=
  match audit with
  | .certified _ _ => False
  | .unresolved _ => True
  | .branch _ slot _ children =>
      (children (m slot) (choices_complete (m slot))).open m

/-- Every compatible machine either has a sound certified leaf or lies in a
recorded open cylinder. No other disposition is permitted. -/
theorem FrontierAudit.exhaustive {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p) (m : Machine) (hm : compatible p m) :
    good m ∨ audit.open m := by
  induction audit with
  | certified p cert =>
      left
      exact cert.sound m hm
  | unresolved p =>
      exact Or.inr trivial
  | branch p slot fresh children ih =>
      have hchild : compatible (refine p slot (m slot)) m :=
        compatible_refine p m slot hm
      rcases ih (m slot) (choices_complete (m slot)) hchild with hgood | hopen
      · exact Or.inl hgood
      · exact Or.inr (by simpa only [FrontierAudit.open] using hopen)

theorem FrontierAudit.close {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p)
    (no_open : ∀ m, compatible p m → ¬audit.open m) : Cover good p := by
  apply Cover.leaf
  intro m hm
  rcases audit.exhaustive m hm with hg | ho
  · exact hg
  · exact False.elim (no_open m hm ho)

def auditSlots : List Slot :=
  (List.finRange 6).flatMap (fun q => [(q, false), (q, true)])

/-- Unassigned *input slots*, not halt actions. -/
def freeSlotCount (p : PartialMachine) : Nat :=
  (auditSlots.filter (fun s => p s = none)).length

def cylinderMass (p : PartialMachine) : Nat := 25 ^ freeSlotCount p

/-- Exact arbitrary-precision full-table multiplicities over each terminal
cylinder, separately for source-certified and unresolved leaves. The caller
must additionally verify mass conservation for its particular tree, or use
the generic conservation theorem when available. -/
def FrontierAudit.report {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p) : Nat × Nat :=
  match audit with
  | .certified p _ => (cylinderMass p, 0)
  | .unresolved p => (0, cylinderMass p)
  | .branch _ _ _ children =>
      (choices.attach.map (fun t => (children t.val t.property).report)).foldl
        (fun acc x => (acc.1 + x.1, acc.2 + x.2)) (0, 0)

#print axioms FrontierAudit.exhaustive
#print axioms FrontierAudit.close
end BB6Coverage
