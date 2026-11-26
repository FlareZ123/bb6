import OneHalt
import SparseBlankDelay
import BoxComplement

namespace BB6.Agent13BoxOneHalt
open BB6Coverage BB6.Agent49Box BB6.Agent13BlankDelay

/-- Complete unexecuted halts using a slot-specific ordinary move. -/
def isolate (fallback : Slot → Move) (m : Machine) (s : Slot) : Machine :=
  fun x => if x = s then none else some ((m x).getD (fallback x))

theorem isolate_missing (fallback : Slot → Move) (m : Machine) (s x : Slot) :
    isolate fallback m s x = none ↔ x = s := by
  by_cases hx : x = s <;> simp [isolate,hx]

theorem isolate_fits (b : Box Slot Transition) (fallback : Slot → Move)
    (hf : ∀ x, none ∈ b x → some (fallback x) ∈ b x)
    (m : Machine) (hm : Fits b m) (s : Slot) (hs : m s = none) :
    Fits b (isolate fallback m s) := by
  intro x
  by_cases hx : x=s
  · subst x
    simpa [isolate,hs] using hm s
  · cases he : m x with
    | none =>
      simpa [isolate,hx,he] using hf x (by simpa [he] using hm x)
    | some t => simpa [isolate,hx,he] using hm x

/-- Writing one at every replaced zero-row preserves the entire blank-delay
    state map, including its undefined endpoints. No offset is lost. -/
theorem isolate_zeroNext (fallback : Slot → Move)
    (hf : ∀ x, (fallback x).write = true)
    (m : Machine) (s : Slot) (hs : m s = none) :
    zeroNext (isolate fallback m s) = zeroNext m := by
  funext q
  by_cases hx : (q,false)=s
  · simp [zeroNext,isolate,hx,hs]
  · cases he : m (q,false) with
    | none => simp [zeroNext,isolate,hx,he,hf]
    | some t => simp [zeroNext,isolate,hx,he]

/-- Select the actual final queried slot of a halting run. Every successful
    instruction before that slot is preserved, so its exact runtime survives. -/
theorem isolate_halting (fallback : Slot → Move) (m : Machine) (n : Nat)
    (hh : HaltsAfter m n) :
    ∃ s, m s = none ∧ HaltsAfter (isolate fallback m s) n := by
  rcases hh with ⟨hseen,hnext⟩
  cases hn : run m n blank with
  | none => simp [hn] at hseen
  | some d =>
    let s := readSlot d
    have hterminal : m s = none := by
      simp only [run,hn,Option.bind_some,rawStep] at hnext
      cases h : m s with
      | none => rfl
      | some t => simp [s,h] at hnext
    have hprefix : ∀ k, k < n → ∀ x, run m k blank = some x →
        m (readSlot x) = isolate fallback m s (readSlot x) := by
      intro k hk x hx
      obtain ⟨t,ht⟩ := defined_before_halt m blank n k hk (by simp [hn]) x hx
      have hneq : readSlot x ≠ s := by
        intro heq
        rw [heq,hterminal] at ht
        contradiction
      simp [isolate,hneq,ht]
    have hsame := run_agrees_on_prefix m (isolate fallback m s) blank n hprefix
    refine ⟨s,hterminal,?_⟩
    constructor
    · rw [← hsame,hn]
      rfl
    · rw [run,← hsame,hn]
      simp [rawStep,isolate,s]

/-- Exact weighted maximum reduction on a product domain: only machines
    with exactly one halt slot need be bounded. Fallback writes-one must
    be allowed wherever a halt is allowed. -/
theorem oneHaltBox_iff (b : Box Slot Transition) (fallback : Slot → Move)
    (hf : ∀ x, none ∈ b x → some (fallback x) ∈ b x)
    (hw : ∀ x, (fallback x).write = true) (B : Nat) :
    (∀ m, Fits b m → WeightedBound B m) ↔
      (∀ s m, Fits b m → (∀ x, m x = none ↔ x = s) → WeightedBound B m) := by
  constructor
  · intro h s m hm _
    exact h m hm
  · intro h m hm k d hk hd
    obtain ⟨s,hs,hh⟩ := isolate_halting fallback m k hk
    let m' := isolate fallback m s
    have hf' : Fits b m' := isolate_fits b fallback hf m hm s hs
    have hz := isolate_zeroNext fallback hw m s hs
    exact h s m' hf' (isolate_missing fallback m s) k d hh (by simpa [m',hz] using hd)

/-- The designated halt slice is an actual product domain: the selected row
    is intersected with {halt}; every other row excludes halt. -/
def haltSlice (b : Box Slot Transition) (s : Slot) : Box Slot Transition :=
  fun x => (b x).filter (fun t => decide (t = none ↔ x = s))

theorem fits_haltSlice_iff (b : Box Slot Transition) (s : Slot) (m : Machine) :
    Fits (haltSlice b s) m ↔ Fits b m ∧ (∀ x, m x = none ↔ x = s) := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro x
      exact (List.mem_filter.mp (h x)).1
    · intro x
      exact of_decide_eq_true (List.mem_filter.mp (h x)).2
  · rintro ⟨hb,hh⟩ x
    exact List.mem_filter.mpr ⟨hb x,decide_eq_true (hh x)⟩

theorem oneHaltSlices_iff (b : Box Slot Transition) (fallback : Slot → Move)
    (hf : ∀ x, none ∈ b x → some (fallback x) ∈ b x)
    (hw : ∀ x, (fallback x).write = true) (B : Nat) :
    (∀ m, Fits b m → WeightedBound B m) ↔
      (∀ s m, Fits (haltSlice b s) m → WeightedBound B m) := by
  rw [oneHaltBox_iff b fallback hf hw B]
  constructor
  · intro h s m hm
    obtain ⟨hb,hh⟩ := (fits_haltSlice_iff b s m).mp hm
    exact h s m hb hh
  · intro h s m hb hh
    exact h s m ((fits_haltSlice_iff b s m).mpr ⟨hb,hh⟩)

#print axioms oneHaltBox_iff
#print axioms oneHaltSlices_iff
end BB6.Agent13BoxOneHalt
