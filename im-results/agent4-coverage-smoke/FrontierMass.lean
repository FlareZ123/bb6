import FrontierAudit
namespace BB6Coverage

private theorem filtered_length_refine (p : PartialMachine) (slot : Slot)
    (t : Transition) (xs : List Slot) (hn : xs.Nodup)
    (hm : slot ∈ xs) (h : p slot = none) :
    (xs.filter (fun s => refine p slot t s = none)).length + 1 =
      (xs.filter (fun s => p s = none)).length := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    have hh : x ∉ xs ∧ xs.Nodup := List.nodup_cons.mp hn
    by_cases hx : x = slot
    · subst x
      have ht : xs.filter (fun s => refine p slot t s = none) =
          xs.filter (fun s => p s = none) := by
        apply List.filter_congr
        intro y hy
        have hne : y ≠ slot := by
          intro heq
          subst y
          exact hh.1 hy
        simp [refine, hne]
      have hhead : refine p slot t slot = some t := by simp [refine]
      simp only [List.filter_cons, hhead, h, decide_false, decide_true,
        Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
        List.length_cons]
      simp [ht]
    · have hm' : slot ∈ xs := by
        rcases List.mem_cons.mp hm with heq | hmem
        · exact False.elim (hx heq.symm)
        · exact hmem
      have hi := ih hh.2 hm'
      by_cases hp : p x = none
      · simp [List.filter_cons, refine, hx, hp] at *
        omega
      · simp [List.filter_cons, refine, hx, hp] at *
        omega

theorem auditSlots_nodup : auditSlots.Nodup := by decide

theorem auditSlots_complete (s : Slot) : s ∈ auditSlots := by
  rcases s with ⟨q,b⟩
  apply List.mem_flatMap.mpr
  refine ⟨q, List.mem_finRange q, ?_⟩
  cases b <;> simp [auditSlots]

theorem freeSlotCount_refine (p : PartialMachine) (slot : Slot)
    (t : Transition) (h : p slot = none) :
    freeSlotCount (refine p slot t) + 1 = freeSlotCount p := by
  exact filtered_length_refine p slot t auditSlots auditSlots_nodup
    (auditSlots_complete slot) h

theorem cylinderMass_refine (p : PartialMachine) (slot : Slot)
    (t : Transition) (h : p slot = none) :
    cylinderMass p = 25 * cylinderMass (refine p slot t) := by
  unfold cylinderMass
  have hs := freeSlotCount_refine p slot t h
  rw [← hs]
  simp [Nat.pow_succ, Nat.mul_comm]

private def addPair (x y : Nat × Nat) : Nat × Nat :=
  (x.1 + y.1, x.2 + y.2)

private theorem foldPair_sum (xs : List (Nat × Nat)) (a b : Nat) :
    (xs.foldl addPair (a,b)).1 + (xs.foldl addPair (a,b)).2 =
      a + b + (xs.map (fun x => x.1 + x.2)).sum := by
  induction xs generalizing a b with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [show addPair (a,b) hd = (a+hd.1,b+hd.2) by rfl]
    rw [ih]
    omega

/-- For every proof-carrying frontier, the certified and still-open
terminal cylinders partition all 25^k total table completions. -/
theorem FrontierAudit.report_conserves {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p) :
    audit.report.1 + audit.report.2 = cylinderMass p := by
  induction audit with
  | certified p cert => simp [FrontierAudit.report]
  | unresolved p => simp [FrontierAudit.report]
  | branch p slot fresh children ih =>
      let w := cylinderMass (refine p slot none)
      have hchild (t : Transition) : cylinderMass (refine p slot t) = w := by
        unfold w cylinderMass
        have a := freeSlotCount_refine p slot t fresh
        have b := freeSlotCount_refine p slot none fresh
        have heq : freeSlotCount (refine p slot t) = freeSlotCount (refine p slot none) := by omega
        rw [heq]
      have hsum (xs : List { t : Transition // t ∈ choices }) :
          ((xs.map (fun x => (children x.val x.property).report)).map
            (fun x => x.1 + x.2)).sum = xs.length * w := by
        induction xs with
        | nil => simp
        | cons hd tl ihtl =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          rw [ih hd.val hd.property, hchild hd.val, ihtl]
          simp [Nat.add_mul, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      change ((choices.attach.map (fun t => (children t.val t.property).report)).foldl
        addPair (0,0)).1 +
        ((choices.attach.map (fun t => (children t.val t.property).report)).foldl
        addPair (0,0)).2 = cylinderMass p
      rw [foldPair_sum]
      simp only [Nat.zero_add]
      rw [hsum]
      simp only [List.length_attach, choices_length]
      exact (cylinderMass_refine p slot none fresh).symm

#print axioms freeSlotCount_refine
#print axioms FrontierAudit.report_conserves
end BB6Coverage
