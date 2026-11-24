import FrontierAudit

namespace BB6Coverage

/-- A score certificate is monotone in its numerical upper bound. -/
theorem decidedBelow_mono {a b : Nat} (hab : a ≤ b) (m : Machine) :
    DecidedBelow a m → DecidedBelow b m := by
  rintro (hne | ⟨n, hn, hh⟩)
  · exact Or.inl hne
  · exact Or.inr ⟨n, Nat.le_trans hn hab, hh⟩

/-- Change the certified predicate without altering the partition or its
open leaves. This permits combining short-run audits with long-run leaves
at a common primitive score bound. -/
def FrontierAudit.weakenGoal {good better : Machine → Prop}
    (h : ∀ m, good m → better m) {p : PartialMachine}
    (audit : FrontierAudit good p) : FrontierAudit better p := by
  induction audit with
  | certified p cert =>
    exact .certified p (.leaf p (fun m hm => h m (cert.sound m hm)))
  | unresolved p => exact .unresolved p
  | branch p slot fresh children ih =>
    exact .branch p slot fresh (fun t ht => ih t ht)

theorem FrontierAudit.weakenGoal_open_iff {good better : Machine → Prop}
    (h : ∀ m, good m → better m) {p : PartialMachine}
    (audit : FrontierAudit good p) (m : Machine) :
    (audit.weakenGoal h).open m ↔ audit.open m := by
  induction audit with
  | certified p cert => rfl
  | unresolved p => rfl
  | branch p slot fresh children ih =>
    exact ih (m slot) (choices_complete (m slot))

theorem FrontierAudit.weakenGoal_report {good better : Machine → Prop}
    (h : ∀ m, good m → better m) {p : PartialMachine}
    (audit : FrontierAudit good p) :
    (audit.weakenGoal h).report = audit.report := by
  induction audit with
  | certified p cert => rfl
  | unresolved p => rfl
  | branch p slot fresh children ih =>
    simp only [FrontierAudit.weakenGoal, FrontierAudit.report]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact ih t.val t.property

def FrontierAudit.raiseBound {a b : Nat} (hab : a ≤ b) {p : PartialMachine}
    (audit : FrontierAudit (DecidedBelow a) p) : FrontierAudit (DecidedBelow b) p :=
  audit.weakenGoal (decidedBelow_mono hab)

theorem FrontierAudit.raiseBound_open_iff {a b : Nat} (hab : a ≤ b)
    {p : PartialMachine} (audit : FrontierAudit (DecidedBelow a) p) (m : Machine) :
    (audit.raiseBound hab).open m ↔ audit.open m :=
  audit.weakenGoal_open_iff (decidedBelow_mono hab) m

theorem FrontierAudit.raiseBound_report {a b : Nat} (hab : a ≤ b)
    {p : PartialMachine} (audit : FrontierAudit (DecidedBelow a) p) :
    (audit.raiseBound hab).report = audit.report :=
  audit.weakenGoal_report (decidedBelow_mono hab)

#print axioms FrontierAudit.raiseBound_open_iff
#print axioms FrontierAudit.raiseBound_report

end BB6Coverage
