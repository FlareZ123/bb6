import FrontierMass
namespace BB6Coverage

private theorem report_snd (xs : List (Nat × Nat)) (a b : Nat) :
    (xs.foldl (fun acc x => (acc.1 + x.1, acc.2 + x.2)) (a,b)).2 =
      b + (xs.map (fun x => x.2)).sum := by
  induction xs generalizing a b with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [show (a + hd.1, b + hd.2) =
      ((fun acc x => (acc.1 + x.1, acc.2 + x.2)) (a,b) hd) by rfl]
    rw [ih]
    omega

private theorem map_snd_le_sum (xs : List (Nat × Nat)) (y : Nat × Nat)
    (hy : y ∈ xs) : y.2 ≤ (xs.map (fun x => x.2)).sum := by
  induction xs with
  | nil => simp at hy
  | cons z zs ih =>
    rcases List.mem_cons.mp hy with h | h
    · subst z; simp [Nat.le_add_right]
    · simp only [List.map_cons, List.sum_cons]
      have hle := ih h
      omega

private theorem report_child_le (p : PartialMachine) (slot : Slot)
    (fresh : p slot = none)
    (children : ∀ t, t ∈ choices → FrontierAudit good (refine p slot t))
    (t : Transition) (ht : t ∈ choices) :
    (children t ht).report.2 ≤
      (FrontierAudit.branch p slot fresh children).report.2 := by
  let x : { t : Transition // t ∈ choices } := ⟨t,ht⟩
  let xs := choices.attach.map (fun y => (children y.val y.property).report)
  have hx : (children t ht).report ∈ xs := by
    have hxx : x ∈ choices.attach := by simp [x]
    apply List.mem_map.mpr
    exact ⟨x, hxx, rfl⟩
  have hle := map_snd_le_sum xs (children t ht).report hx
  simpa [FrontierAudit.report, xs, report_snd] using hle

/-- Each actually unresolved compatible table contributes a strictly
positive open cylinder to the report. -/
theorem FrontierAudit.open_implies_mass {good : Machine → Prop}
    {p : PartialMachine} (audit : FrontierAudit good p)
    (m : Machine) (hm : compatible p m) :
    audit.open m → 0 < audit.report.2 := by
  induction audit with
  | certified p cert => simp [FrontierAudit.open]
  | unresolved p =>
      intro _
      simpa [FrontierAudit.report, cylinderMass] using
        (Nat.pow_pos (n := freeSlotCount p) (by decide : 0 < 25))
  | branch p slot fresh children ih =>
      intro ho
      have ht : m slot ∈ choices := choices_complete (m slot)
      have hchild : compatible (refine p slot (m slot)) m :=
        compatible_refine p m slot hm
      have hchildopen : (children (m slot) ht).open m := by
        simpa only [FrontierAudit.open] using ho
      have hpos := ih (m slot) ht hchild hchildopen
      have hle := report_child_le p slot fresh children (m slot) ht
      omega

/-- A zero open-mass report is itself a sound, fully closed Cover certificate.
This theorem prevents misreporting partially explored trees as complete. -/
theorem FrontierAudit.complete_of_zero {good : Machine → Prop}
    {p : PartialMachine} (audit : FrontierAudit good p)
    (hz : audit.report.2 = 0) : Cover good p := by
  apply audit.close
  intro m hm ho
  have hp := audit.open_implies_mass m hm ho
  omega

#print axioms FrontierAudit.open_implies_mass
#print axioms FrontierAudit.complete_of_zero
end BB6Coverage
