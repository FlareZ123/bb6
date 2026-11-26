import OneHalt
import SparseBlankDelay
import BoxComplement

namespace BB6.Agent13BoxMinimalHalt
open BB6Coverage BB6.Agent49Box BB6.Agent13BlankDelay

/-- Prefer an ordinary action whenever the row permits one. -/
def preferred (b : Box Slot Transition) (s : Slot) : Transition :=
  ((b s).find? Option.isSome).getD none

theorem preferred_mem (b : Box Slot Transition) (s : Slot)
    (h : none ∈ b s) : preferred b s ∈ b s := by
  unfold preferred
  cases he : (b s).find? Option.isSome with
  | none => simpa [he] using h
  | some a => simpa [he] using List.mem_of_find?_eq_some he

theorem preferred_none_iff (b : Box Slot Transition) (s : Slot) :
    preferred b s = none ↔ ∀ v : Move, some v ∉ b s := by
  unfold preferred
  cases he : (b s).find? Option.isSome with
  | none =>
    simp only [Option.getD_none, true_iff]
    intro v hv
    exact (List.find?_eq_none.mp he (some v) hv) rfl
  | some a =>
    have ha : a.isSome = true := List.find?_some he
    cases a with
    | none => simp at ha
    | some v =>
      simp only [Option.getD_some, reduceCtorEq, false_iff]
      intro h
      exact h v (List.mem_of_find?_eq_some he)

/-- Keep the actual final halt and unavoidable halts; fill other absent rows. -/
def minimal (b : Box Slot Transition) (m : Machine) (s : Slot) : Machine :=
  fun x => if x = s then none else (m x).orElse (fun _ => preferred b x)

theorem minimal_agrees (b : Box Slot Transition) (m : Machine) (s : Slot)
    (hs : m s = none) (x : Slot) (v : Move) (hv : m x = some v) :
    minimal b m s x = some v := by
  have hx : x ≠ s := by
    intro h; rw [h,hs] at hv; contradiction
  simp [minimal,hx,hv]

theorem minimal_fits (b : Box Slot Transition) (m : Machine) (hm : Fits b m)
    (s : Slot) (hs : m s = none) : Fits b (minimal b m s) := by
  intro x
  by_cases hx : x=s
  · subst x; simpa [minimal,hs] using hm s
  · cases he : m x with
    | none =>
      simpa [minimal,hx,he] using preferred_mem b x (by simpa [he] using hm x)
    | some v => simpa [minimal,hx,he] using hm x

theorem minimal_halt_slots (b : Box Slot Transition) (m : Machine) (hm : Fits b m)
    (s : Slot) (_hs : m s = none) (x : Slot) :
    minimal b m s x = none ↔ x = s ∨ ∀ v : Move, some v ∉ b x := by
  by_cases hx : x=s
  · simp [minimal,hx]
  · cases he : m x with
    | none => simp [minimal,hx,he,preferred_none_iff]
    | some v =>
      simp only [minimal,hx,ite_false,he,Option.orElse_some,reduceCtorEq,false_or,false_iff]
      intro h
      exact h v (by simpa [he] using hm x)

/-- Every edge of the original zero-transition graph survives an ordinary
    extension, though further edges may be added. -/
theorem zeroNext_extends (m m' : Machine)
    (h : ∀ x v, m x = some v → m' x = some v) (s t : Fin 6)
    (he : zeroNext m s = some t) : zeroNext m' s = some t := by
  unfold zeroNext at he ⊢
  cases hm : m (s,false) with
  | none => simp [hm] at he
  | some v => simpa [h _ _ hm,hm] using he

theorem follow_extends {α : Type} (f g : α → Option α)
    (h : ∀ s t, f s = some t → g s = some t) (n : Nat) (s t : α)
    (he : follow f n s = some t) : follow g n s = some t := by
  induction n generalizing s with
  | zero => exact he
  | succ n ih =>
    unfold follow at he ⊢
    cases hf : f s with
    | none => simp [hf] at he
    | some u =>
      rw [h s u hf]
      simp only [Option.bind_some]
      exact ih u (by simpa [hf] using he)

theorem delays_extends (m m' : Machine)
    (h : ∀ x v, m x = some v → m' x = some v) (d : Nat)
    (hd : d ∈ delays (zeroNext m) 0) : d ∈ delays (zeroNext m') 0 := by
  unfold delays at hd ⊢
  obtain ⟨hr,ha⟩ := List.mem_filter.mp hd
  obtain ⟨s,hs,hf⟩ := List.any_eq_true.mp ha
  have he : follow (zeroNext m) d s = some 0 := by simpa using hf
  have hg := follow_extends (zeroNext m) (zeroNext m') (zeroNext_extends m m' h) d s 0 he
  exact List.mem_filter.mpr ⟨hr,List.any_eq_true.mpr ⟨s,hs,by simpa using hg⟩⟩

/-- The final halt selects the only missing transition that must be retained
    among rows permitting ordinary actions. -/
theorem final_slot (m : Machine) (n : Nat) (hh : HaltsAfter m n) :
    ∃ s, m s = none ∧ ∀ m' : Machine,
      (∀ x v, m x = some v → m' x = some v) → m' s = none → HaltsAfter m' n := by
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
    refine ⟨s,hterminal,?_⟩
    intro m' hm' hs'
    have hprefix : ∀ k, k < n → ∀ x, run m k blank = some x →
        m (readSlot x) = m' (readSlot x) := by
      intro k hk x hx
      obtain ⟨v,hv⟩ := defined_before_halt m blank n k hk (by simp [hn]) x hx
      exact hv.trans (hm' _ _ hv).symm
    have hsame := run_agrees_on_prefix m m' blank n hprefix
    constructor
    · rw [← hsame,hn]; rfl
    · rw [run,← hsame,hn]; simp [rawStep,s] at hs' ⊢; rw [hs']

/-- Exact maximum reduction for every finite product domain, including
    boxes with unavoidable halts, with no hypothesis on allowed actions. -/
theorem minimalHaltBox_iff (b : Box Slot Transition) (B : Nat) :
    (∀ m, Fits b m → WeightedBound B m) ↔
      (∀ s m, Fits b m → (∀ x, m x = none ↔ x = s ∨ ∀ v : Move, some v ∉ b x) → WeightedBound B m) := by
  constructor
  · intro h s m hm _; exact h m hm
  · intro h m hm k d hk hd
    obtain ⟨s,hs,hpres⟩ := final_slot m k hk
    let m' := minimal b m s
    have he := minimal_agrees b m s hs
    have hf := minimal_fits b m hm s hs
    have hh : HaltsAfter m' k := hpres m' he (by simp [m',minimal])
    exact h s m' hf (minimal_halt_slots b m hm s hs) k d hh (delays_extends m m' he d hd)

/-- For each possible final halt, keep unavoidable halt-only rows and remove
    halt from all other rows. Empty slices represent no machines. -/
def minimalSlice (b : Box Slot Transition) (s : Slot) : Box Slot Transition :=
  fun x => (b x).filter (fun t => decide (t = none ↔ x = s ∨ preferred b x = none))

theorem fits_minimalSlice_iff (b : Box Slot Transition) (s : Slot) (m : Machine) :
    Fits (minimalSlice b s) m ↔ Fits b m ∧
      (∀ x, m x = none ↔ x = s ∨ ∀ v : Move, some v ∉ b x) := by
  constructor
  · intro h
    refine ⟨fun x => (List.mem_filter.mp (h x)).1, ?_⟩
    intro x
    have he := of_decide_eq_true (List.mem_filter.mp (h x)).2
    simpa only [preferred_none_iff] using he
  · rintro ⟨hb,hh⟩ x
    apply List.mem_filter.mpr
    refine ⟨hb x,decide_eq_true ?_⟩
    simpa only [preferred_none_iff] using hh x

theorem minimalSlices_iff (b : Box Slot Transition) (B : Nat) :
    (∀ m, Fits b m → WeightedBound B m) ↔
      (∀ s m, Fits (minimalSlice b s) m → WeightedBound B m) := by
  rw [minimalHaltBox_iff]
  constructor
  · intro h s m hm
    obtain ⟨hb,hh⟩ := (fits_minimalSlice_iff b s m).mp hm
    exact h s m hb hh
  · intro h s m hb hh
    exact h s m ((fits_minimalSlice_iff b s m).mpr ⟨hb,hh⟩)

#print axioms minimalSlices_iff
#print axioms minimalHaltBox_iff
end BB6.Agent13BoxMinimalHalt
