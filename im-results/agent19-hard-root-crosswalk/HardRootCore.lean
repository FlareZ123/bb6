import CanonicalRaw114Accepted
import FirstHolePath

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19HardRoot
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath

/-- Literal tables use one Option Move per slot; `none` here is a halt,
    whereas `forgetHaltRows` makes it an unassigned partial-table slot. -/
def literal (xs : List Transition) : Machine :=
  fun s => xs[2*s.1.val + (if s.2 then 1 else 0)]?.getD none

def allSlots : List Slot := (List.finRange 6).flatMap fun q => [(q,false),(q,true)]

theorem allSlots_complete (s : Slot) : s ∈ allSlots := by
  rcases s with ⟨q,b⟩
  apply List.mem_flatMap.mpr
  exact ⟨q, List.mem_finRange q, by cases b <;> simp⟩

def parentCheck (p : PartialMachine) (m : Machine) : Bool :=
  allSlots.all fun s => match p s with
  | none => true
  | some t => decide (m s = t)

theorem parentCheck_iff (p : PartialMachine) (m : Machine) :
    parentCheck p m = true ↔ compatible p m := by
  constructor
  · intro h s t hs
    have hh := List.all_eq_true.mp h s (allSlots_complete s)
    simpa [hs] using hh
  · intro h
    apply List.all_eq_true.mpr
    intro s hs
    cases hp : p s with
    | none => simp
    | some t => simp [h s t hp]

/-- A single halt row makes the weighted bound of its sparse cylinder
    logically equivalent to the bound of its halt-default completion.
    All other completions have twelve ordinary moves. -/
theorem oneHalt_cover_iff (B : Nat) (m : Machine) (s : Slot)
    (hh : m s = none) (ho : ∀ t, t ≠ s → ∃ mv, m t = some mv) :
    Cover (WeightedBound B) (forgetHaltRows m) ↔ WeightedBound B m := by
  constructor
  · intro h
    have hc := weightedTNFDefaultCompletion_compatible (forgetHaltRows m)
    rw [forgetHaltRows_defaultCompletion] at hc
    exact h.sound m hc
  · intro hm
    apply Cover.leaf
    intro m' hc
    cases h : m' s with
    | none =>
      have he : m' = m := by
        funext t
        by_cases ht : t = s
        · subst t; exact h.trans hh.symm
        · obtain ⟨mv, hv⟩ := ho t ht
          exact (hc t _ (by simp [forgetHaltRows, hv])).trans hv.symm
      exact he.symm ▸ hm
    | some mv =>
      apply weighted_never
      apply all_ordinary_never
      intro t
      by_cases ht : t = s
      · subst t; exact ⟨mv,h⟩
      · obtain ⟨v,hv⟩ := ho t ht
        exact ⟨v,hc t _ (by simp [forgetHaltRows,hv])⟩

/-- Exact finite condition for a one-halt weighted cylinder, using the
    actual list of possible normalized blank delays. -/
theorem oneHalt_cover_iff_max (B : Nat) (m : Machine) (s : Slot) (D : Nat)
    (hh : m s = none) (ho : ∀ t, t ≠ s → ∃ mv, m t = some mv)
    (hD : D ∈ delays (zeroNext m) 0)
    (hmax : ∀ d ∈ delays (zeroNext m) 0, d ≤ D) :
    Cover (WeightedBound B) (forgetHaltRows m) ↔
      ∀ k, HaltsAfter m k → k + 1 + D ≤ B := by
  rw [oneHalt_cover_iff B m s hh ho]
  constructor
  · intro h k hk
    have hb := h k D hk hD
    omega
  · intro h k d hk hd
    have hb := h k hk
    have hd' := hmax d hd
    omega

/-- Exact slotwise certificate for the unique ordinary-versus-halt row. -/
def oneHaltCheck (m : Machine) (s : Slot) : Bool :=
  allSlots.all fun t => decide (m t = none) == decide (t=s)

theorem oneHaltCheck_sound (m : Machine) (s : Slot) (h : oneHaltCheck m s = true) :
    m s = none ∧ ∀ t, t ≠ s → ∃ mv, m t = some mv := by
  constructor
  · have hs := List.all_eq_true.mp h s (allSlots_complete s)
    simpa using hs
  · intro t ht
    have hs := List.all_eq_true.mp h t (allSlots_complete t)
    cases hm : m t with
    | none => simp [hm,ht] at hs
    | some mv => exact ⟨mv,rfl⟩

/-- The finite exact delay set can be supplied as a literal list. -/
theorem cover_iff_of_checks (m : Machine) (s : Slot) (ds : List Nat) (D B : Nat)
    (h : oneHaltCheck m s = true)
    (he : delays (zeroNext m) 0 = ds)
    (hD : D ∈ ds) (hmax : ∀ d ∈ ds, d ≤ D) :
    Cover (WeightedBound B) (forgetHaltRows m) ↔
      ∀ k, HaltsAfter m k → k+1+D ≤ B := by
  have ⟨hh,ho⟩ := oneHaltCheck_sound m s h
  exact oneHalt_cover_iff_max B m s D hh ho (he.symm ▸ hD)
    (by rw [he]; exact hmax)

/-- A compatible ordinary partial ancestor is preserved by deleting the
    completed root's halt row, so every completion of the new leaf stays
    in the actual parent cylinder. -/
theorem leaf_extends_parent (p : PartialMachine) (m : Machine)
    (hp : weightedTNFNoAssignedHalt p) (hc : compatible p m) :
    ∀ m', compatible (forgetHaltRows m) m' → compatible p m' := by
  intro m' hm s t hs
  cases t with
  | none => exact False.elim (hp s hs)
  | some v =>
    exact hm s _ (by simp [forgetHaltRows, hc s _ hs])

def ordinaryParentCheck (p : PartialMachine) : Bool :=
  allSlots.all fun s => decide (p s ≠ some (none : Transition))

theorem ordinaryParentCheck_sound (p : PartialMachine)
    (h : ordinaryParentCheck p = true) : weightedTNFNoAssignedHalt p := by
  intro s
  exact of_decide_eq_true (List.all_eq_true.mp h s (allSlots_complete s))

#print axioms parentCheck_iff
#print axioms oneHalt_cover_iff
#print axioms oneHalt_cover_iff_max
#print axioms oneHaltCheck_sound
#print axioms cover_iff_of_checks
#print axioms leaf_extends_parent
#print axioms ordinaryParentCheck_sound
end BB6.Agent19HardRoot
