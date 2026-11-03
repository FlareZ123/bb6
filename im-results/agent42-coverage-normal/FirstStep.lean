import Symmetry

namespace BB6Coverage

/-- Swap a noninitial successor state with B, leaving A alone whenever
    the successor is distinct from A. -/
def swapToOne (q : Fin 6) : StatePerm where
  forward := fun s => if s = q then 1 else if s = 1 then q else s
  backward := fun s => if s = q then 1 else if s = 1 then q else s
  leftInverse := by intro s; revert s; revert q; decide
  rightInverse := by intro s; revert s; revert q; decide

theorem swapToOne_root (q : Fin 6) (hq : q ≠ 0) :
    (swapToOne q).forward 0 = 0 := by
  revert q
  decide

theorem swapToOne_target (q : Fin 6) :
    (swapToOne q).forward q = 1 := by
  simp [swapToOne]

/-- Every A/0 transition to a different state can be relabeled and,
    if necessary, tape-reflected so its direction is right and its target B.
    Every blank-tape halting time is preserved. -/
theorem normal_first_other (m : Machine) (w r : Bool) (q : Fin 6)
    (hq : q ≠ 0) (hfirst : m initialSlot = some ⟨w,r,q⟩) :
    ∃ m' : Machine,
      (∀ n, HaltsAfter m' n ↔ HaltsAfter m n) ∧
      m' initialSlot = some ⟨w,true,1⟩ := by
  let e := swapToOne q
  let m' := normalizedTable e (!r) m
  refine ⟨m', ?_, ?_⟩
  · intro n
    have h := normalized_haltsAt_iff e (!r) m 0 n
    have hroot : e.forward (0 : Fin 6) = 0 := swapToOne_root q hq
    rw [hroot] at h
    simpa only [HaltsAfterAt, HaltsAfter, blankAt_zero] using h
  · have hrootb : e.backward (0 : Fin 6) = 0 := by
      simpa [e, swapToOne] using swapToOne_root q hq
    have htarget : e.forward q = 1 := swapToOne_target q
    cases r with
    | false =>
      change ((m (e.backward 0, false)).map reflectMove).map
        (renameMove e) = some ⟨w, true, 1⟩
      rw [hrootb]
      change ((m initialSlot).map reflectMove).map (renameMove e) = some ⟨w, true, 1⟩
      rw [hfirst]
      simp [renameMove, reflectMove, htarget]
    | true =>
      change (m (e.backward 0, false)).map
        (renameMove e) = some ⟨w, true, 1⟩
      rw [hrootb]
      change (m initialSlot).map (renameMove e) = some ⟨w, true, 1⟩
      rw [hfirst]
      simp [renameMove, htarget]

/-- When the first move returns to A, reflection suffices to orient it right. -/
theorem normal_first_self (m : Machine) (w r : Bool)
    (hfirst : m initialSlot = some ⟨w,r,(0 : Fin 6)⟩) :
    ∃ m' : Machine,
      (∀ n, HaltsAfter m' n ↔ HaltsAfter m n) ∧
      m' initialSlot = some ⟨w,true,(0 : Fin 6)⟩ := by
  cases r with
  | false =>
    refine ⟨reflectTable m, reflect_halts_iff m, ?_⟩
    simp [reflectTable, reflectMove, hfirst]
  | true =>
    exact ⟨m, fun n => Iff.rfl, hfirst⟩

/-- Representatives of the twenty-five possible A/0 instructions:
    1 halting instruction, 2 oriented self-returns and 2 oriented B-targets. -/
def CanonicalFirst (m : Machine) : Prop :=
  m initialSlot = none ∨
  (∃ w : Bool, m initialSlot = some ⟨w, true, (0 : Fin 6)⟩) ∨
  (∃ w : Bool, m initialSlot = some ⟨w, true, (1 : Fin 6)⟩)

/-- First-step rooted normal form preserving the exact halting runtime.
    It does not identify different blank roots under a state permutation. -/
theorem normalize_first (m : Machine) :
    ∃ m' : Machine,
      (∀ n, HaltsAfter m' n ↔ HaltsAfter m n) ∧
      CanonicalFirst m' := by
  cases hfirst : m initialSlot with
  | none => exact ⟨m, fun n => Iff.rfl, Or.inl hfirst⟩
  | some t =>
    rcases t with ⟨w, r, q⟩
    by_cases hzero : q = (0 : Fin 6)
    · subst q
      obtain ⟨m', hs, hc⟩ := normal_first_self m w r hfirst
      exact ⟨m', hs, Or.inr (Or.inl ⟨w,hc⟩)⟩
    · obtain ⟨m', hs, hc⟩ := normal_first_other m w r q hzero hfirst
      exact ⟨m', hs, Or.inr (Or.inr ⟨w,hc⟩)⟩

/-- Universal upper bounds reduce soundly to machines with one of five
    canonical first instructions. This discharges the initial state-label
    and left/right symmetry edge, not the remaining search or holdouts. -/
theorem upper_from_five_first_actions (B : Nat)
    (h : ∀ m : Machine, CanonicalFirst m →
      ∀ n, HaltsAfter m n → n+1 ≤ B) :
    ∀ m n, HaltsAfter m n → n+1 ≤ B := by
  intro m n hh
  obtain ⟨m', heq, hcanonical⟩ := normalize_first m
  exact h m' hcanonical n ((heq n).mpr hh)

#print axioms swapToOne
#print axioms normal_first_other
#print axioms normalize_first
#print axioms upper_from_five_first_actions
end BB6Coverage
