import FrontierAudit

namespace BB6Coverage

private def setMove (m : Machine) (s : Slot) (t : Transition) : Machine :=
  fun x => if x = s then t else m x

private def sumOver (xs : List Slot) (m : Machine) (f : Machine → Nat) : Nat :=
  match xs with
  | [] => f m
  | s :: rest => (choices.map (fun t => sumOver rest (setMove m s t) f)).sum

private theorem sumMap_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sumMap_const {α : Type} (xs : List α) (k : Nat) :
    (xs.map (fun _ => k)).sum = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

private theorem sumMap_single {α : Type} [DecidableEq α] (xs : List α)
    (a : α) (f : α → Nat) (hn : xs.Nodup) (ha : a ∈ xs)
    (hz : ∀ x, x ∈ xs → x ≠ a → f x = 0) : (xs.map f).sum = f a := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      have hnod := List.nodup_cons.mp hn
      by_cases h : x = a
      · subst x
        have ht : xs.map f = xs.map (fun _ => 0) := by
          apply List.map_congr_left
          intro y hy
          apply hz y (by simp [hy])
          intro hyx
          subst y
          exact hnod.1 hy
        simp [ht, sumMap_const]
      · have hm : a ∈ xs := by
          simpa [Ne.symm h] using ha
        have hx := hz x (by simp) h
        have hh := ih hnod.2 hm (fun y hy => hz y (by simp [hy]))
        simp [hx, hh]

private theorem sumOver_add (xs : List Slot) (m : Machine) (f g : Machine → Nat) :
    sumOver xs m (fun x => f x + g x) = sumOver xs m f + sumOver xs m g := by
  induction xs generalizing m with
  | nil => rfl
  | cons s xs ih =>
      simp only [sumOver, ih, sumMap_add]

private theorem sumOver_sum {α : Type} (ys : List α) (xs : List Slot)
    (m : Machine) (f : α → Machine → Nat) :
    sumOver xs m (fun x => (ys.map (fun y => f y x)).sum) =
      (ys.map (fun y => sumOver xs m (f y))).sum := by
  induction ys with
  | nil =>
      induction xs generalizing m with
      | nil => rfl
      | cons s xs ih =>
          have hz (m' : Machine) : sumOver xs m' (fun _ => 0) = 0 := ih m'
          simp [sumOver, hz, sumMap_const]
  | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons, sumOver_add, ih]

private noncomputable def indicator (P : Prop) : Nat := by
  classical
  exact if P then 1 else 0

private noncomputable def rawMeasure (P : Machine → Prop) : Nat :=
  sumOver auditSlots (fun _ => none) (fun m => indicator (P m))

private theorem rawMeasure_congr {P Q : Machine → Prop}
    (h : ∀ m, P m ↔ Q m) : rawMeasure P = rawMeasure Q := by
  congr 1
  funext m
  exact propext (h m)

private theorem rawMeasure_disjoint {P Q : Machine → Prop}
    (h : ∀ m, ¬ (P m ∧ Q m)) :
    rawMeasure (fun m => P m ∨ Q m) = rawMeasure P + rawMeasure Q := by
  classical
  unfold rawMeasure
  rw [← sumOver_add]
  congr 1
  funext m
  by_cases hp : P m <;> by_cases hq : Q m
  · exact False.elim (h m ⟨hp, hq⟩)
  · simp [indicator, hp, hq]
  · simp [indicator, hp, hq]
  · simp [indicator, hp, hq]

private def outsideOK (xs : List Slot) (p : PartialMachine) (m : Machine) : Prop :=
  ∀ s, s ∉ xs → ∀ t, p s = some t → m s = t

private theorem choices_nodup_measure : choices.Nodup := by decide

private theorem outsideOK_cons (s : Slot) (xs : List Slot) (p : PartialMachine)
    (m : Machine) (t : Transition) (hs : s ∉ xs) :
    outsideOK xs p (setMove m s t) ↔
      outsideOK (s :: xs) p m ∧ (∀ v, p s = some v → t = v) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hx v hv
      have hne : x ≠ s := fun he => hx (by simp [he])
      have hnot : x ∉ xs := fun hm => hx (by simp [hm])
      simpa [setMove, hne] using h x hnot v hv
    · intro v hv
      simpa [setMove] using h s hs v hv
  · intro ⟨h, ht⟩ x hx v hv
    by_cases he : x = s
    · subst x
      simpa [setMove] using ht v hv
    · have hnot : x ∉ s :: xs := by simp [he, hx]
      simpa [setMove, he] using h x hnot v hv

private theorem sumOver_cylinder (xs : List Slot) (m : Machine) (p : PartialMachine)
    (hn : xs.Nodup) :
    sumOver xs m (fun full => indicator (compatible p full)) =
      indicator (outsideOK xs p m) * 25 ^ (xs.filter (fun s => p s = none)).length := by
  classical
  induction xs generalizing m with
  | nil => simp [sumOver, outsideOK, compatible]
  | cons s xs ih =>
      have hnod := List.nodup_cons.mp hn
      let k := 25 ^ (xs.filter (fun s => p s = none)).length
      simp only [sumOver, ih _ hnod.2, outsideOK_cons s xs p _ _ hnod.1]
      change (choices.map (fun t => indicator (outsideOK (s :: xs) p m ∧
        (∀ v, p s = some v → t = v)) * k)).sum = _
      by_cases hout : outsideOK (s :: xs) p m
      · cases hp : p s with
        | none =>
            simp [indicator, hout, hp, sumMap_const, choices_length,
              Nat.pow_succ, Nat.mul_comm, k]
        | some u =>
            have heq : (choices.map (fun t => indicator (outsideOK (s :: xs) p m ∧
                (∀ v, some u = some v → t = v)) * k)).sum = k := by
              rw [sumMap_single choices u _ choices_nodup_measure (choices_complete u)]
              · simp [indicator, hout]
              · intro x _ hx
                simp [indicator, hout, hx]
            rw [heq]
            simp [indicator, hout, hp, k]
      · simp [indicator, hout, sumMap_const]

private theorem auditSlots_nodup_measure : auditSlots.Nodup := by decide
private theorem auditSlots_complete_measure (s : Slot) : s ∈ auditSlots := by
  rcases s with ⟨q,b⟩
  apply List.mem_flatMap.mpr
  refine ⟨q, List.mem_finRange q, ?_⟩
  cases b <;> simp

private theorem rawMeasure_cylinder (p : PartialMachine) :
    rawMeasure (fun m => compatible p m) = cylinderMass p := by
  unfold rawMeasure cylinderMass freeSlotCount
  rw [sumOver_cylinder _ _ _ auditSlots_nodup_measure]
  have h : outsideOK auditSlots p (fun _ => none) := by
    intro s hs t ht
    exact False.elim (hs (auditSlots_complete_measure s))
  simp [indicator, h]

private def reportCoord (b : Bool) (x : Nat × Nat) : Nat :=
  if b then x.1 else x.2

private def terminalEvent {good : Machine → Prop} {p : PartialMachine}
    (b : Bool) (a : FrontierAudit good p) (m : Machine) : Prop :=
  compatible p m ∧ (if b then ¬ a.open m else a.open m)

private theorem foldPair_coord (b : Bool) (xs : List (Nat × Nat)) (acc : Nat × Nat) :
    reportCoord b (xs.foldl (fun a x => (a.1 + x.1, a.2 + x.2)) acc) =
      reportCoord b acc + (xs.map (reportCoord b)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      cases b <;> simp [reportCoord, Nat.add_assoc]

private theorem attachedChoices_nodup : choices.attach.Nodup := by decide

private theorem branch_event_sum {good : Machine → Prop} (p : PartialMachine)
    (slot : Slot) (fresh : p slot = none)
    (children : ∀ t, t ∈ choices → FrontierAudit good (refine p slot t))
    (b : Bool) (m : Machine) :
    indicator (terminalEvent b (.branch p slot fresh children) m) =
      (choices.attach.map (fun t => indicator (terminalEvent b (children t.val t.property) m))).sum := by
  classical
  let t : { x // x ∈ choices } := ⟨m slot, choices_complete (m slot)⟩
  rw [sumMap_single choices.attach t _ attachedChoices_nodup (List.mem_attach _ _)]
  · simp [terminalEvent, t, compatible_refine_iff p m slot fresh, FrontierAudit.open]
  · intro x _ hne
    have hv : m slot ≠ x.val := by
      intro h
      apply hne
      exact Subtype.ext h.symm
    simp [terminalEvent, compatible_refine_iff p m slot fresh, hv, indicator]

private theorem rawMeasure_false : rawMeasure (fun _ => False) = 0 := by
  unfold rawMeasure
  have h (xs : List Slot) (m : Machine) : sumOver xs m (fun _ => indicator False) = 0 := by
    induction xs generalizing m with
    | nil => simp [sumOver, indicator]
    | cons s xs ih => simp [sumOver, ih, sumMap_const]
  exact h _ _

/-- Both coordinates of the audit report count the corresponding terminal
    events on the full raw-table universe, independently of branching order. -/
private theorem report_coord_measure {good : Machine → Prop} {p : PartialMachine}
    (a : FrontierAudit good p) (b : Bool) :
    reportCoord b a.report = rawMeasure (terminalEvent b a) := by
  induction a with
  | certified p cert =>
      cases b
      · simp [reportCoord, FrontierAudit.report]
        rw [← rawMeasure_false]
        apply rawMeasure_congr
        intro m
        simp [terminalEvent, FrontierAudit.open]
      · simp [reportCoord, FrontierAudit.report]
        rw [← rawMeasure_cylinder p]
        apply rawMeasure_congr
        intro m
        simp [terminalEvent, FrontierAudit.open]
  | unresolved p =>
      cases b
      · simp [reportCoord, FrontierAudit.report]
        rw [← rawMeasure_cylinder p]
        apply rawMeasure_congr
        intro m
        simp [terminalEvent, FrontierAudit.open]
      · simp [reportCoord, FrontierAudit.report]
        rw [← rawMeasure_false]
        apply rawMeasure_congr
        intro m
        simp [terminalEvent, FrontierAudit.open]
  | branch p slot fresh children ih =>
      rw [FrontierAudit.report, foldPair_coord]
      simp only [List.map_map]
      have hzero : reportCoord b (0,0) = 0 := by cases b <;> rfl
      rw [hzero, Nat.zero_add]
      have hmap : (choices.attach.map (fun x => reportCoord b (children x.val x.property).report)).sum =
          (choices.attach.map (fun x => rawMeasure (terminalEvent b (children x.val x.property)))).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro x _
        exact ih x.val x.property
      change (choices.attach.map (fun x => reportCoord b (children x.val x.property).report)).sum = _
      rw [hmap]
      unfold rawMeasure
      rw [← sumOver_sum]
      apply congrArg (sumOver auditSlots (fun _ => none))
      funext m
      exact (branch_event_sum p slot fresh children b m).symm

/-- The exact numeric report is determined by the semantic open set, even
    for differently shaped audit trees and different certified predicates. -/
theorem audit_report_eq_of_open_iff {g h : Machine → Prop} {p : PartialMachine}
    (a : FrontierAudit g p) (b : FrontierAudit h p)
    (heq : ∀ m, compatible p m → (a.open m ↔ b.open m)) :
    a.report = b.report := by
  apply Prod.ext
  · change reportCoord true a.report = reportCoord true b.report
    rw [report_coord_measure, report_coord_measure]
    apply rawMeasure_congr
    intro m
    by_cases hm : compatible p m
    · simp [terminalEvent, hm, heq m hm]
    · simp [terminalEvent, hm]
  · change reportCoord false a.report = reportCoord false b.report
    rw [report_coord_measure, report_coord_measure]
    apply rawMeasure_congr
    intro m
    by_cases hm : compatible p m
    · simp [terminalEvent, hm, heq m hm]
    · simp [terminalEvent, hm]

/-- Report delta for closing a fresh cylinder. The semantic premises may be
    established by a sparse-table certificate checker without evaluating
    either the old or the new audit report. -/
theorem audit_report_delta_of_open_iff {g h : Machine → Prop} {p src : PartialMachine}
    (old : FrontierAudit g p) (new : FrontierAudit h p)
    (hsub : ∀ m, compatible src m → compatible p m)
    (hfresh : ∀ m, compatible src m → old.open m)
    (hclose : ∀ m, compatible p m → (new.open m ↔ old.open m ∧ ¬ compatible src m)) :
    new.report = (old.report.1 + cylinderMass src, old.report.2 - cylinderMass src) := by
  have hnewcert : rawMeasure (terminalEvent true new) =
      rawMeasure (fun m => terminalEvent true old m ∨ compatible src m) := by
    apply rawMeasure_congr
    intro m
    classical
    by_cases hm : compatible p m
    · by_cases ho : old.open m <;> by_cases hs : compatible src m <;>
        simp [terminalEvent, hm, hclose m hm, ho, hs]
    · have hs : ¬ compatible src m := fun hc => hm (hsub m hc)
      simp [terminalEvent, hm, hs]
  have hdis : ∀ m, ¬ (terminalEvent true old m ∧ compatible src m) := by
    intro m ⟨hc, hs⟩
    exact hc.2 (hfresh m hs)
  have hcert : new.report.1 = old.report.1 + cylinderMass src := by
    change reportCoord true new.report = reportCoord true old.report + _
    rw [report_coord_measure, report_coord_measure, hnewcert, rawMeasure_disjoint hdis, rawMeasure_cylinder]
  have holdopen : rawMeasure (terminalEvent false old) =
      rawMeasure (fun m => terminalEvent false new m ∨ compatible src m) := by
    apply rawMeasure_congr
    intro m
    classical
    by_cases hm : compatible p m
    · by_cases hs : compatible src m <;> simp [terminalEvent, hm, hclose m hm, hs, hfresh]
    · have hs : ¬ compatible src m := fun hc => hm (hsub m hc)
      simp [terminalEvent, hm, hs]
  have hdis' : ∀ m, ¬ (terminalEvent false new m ∧ compatible src m) := by
    intro m ⟨hc, hs⟩
    exact ((hclose m hc.1).mp hc.2).2 hs
  have hopen : old.report.2 = new.report.2 + cylinderMass src := by
    change reportCoord false old.report = reportCoord false new.report + _
    rw [report_coord_measure, report_coord_measure, holdopen, rawMeasure_disjoint hdis', rawMeasure_cylinder]
  apply Prod.ext
  · exact hcert
  · omega

#print axioms audit_report_eq_of_open_iff
#print axioms audit_report_delta_of_open_iff
end BB6Coverage
