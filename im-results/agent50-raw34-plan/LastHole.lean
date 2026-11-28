import ExactHalt
namespace BB6.Agent50Raw34Plan
open BB6Coverage

def ordinaryAt (p : PartialMachine) (s : Slot) : Bool :=
  match p s with
  | some (some _) => true
  | _ => false

def allOtherOrdinary (p : PartialMachine) (s : Slot) : Bool :=
  slots.all fun t => if t = s then true else ordinaryAt p t

theorem allOtherOrdinary_sound (p : PartialMachine) (s : Slot)
    (h : allOtherOrdinary p s = true) (m : Machine) (hm : compatible p m)
    (t : Slot) (ht : t ≠ s) : ∃ mv, m t = some mv := by
  have hb := List.all_eq_true.mp h t (slots_complete t)
  have ha : ordinaryAt p t = true := by simpa [ht] using hb
  cases hp : p t with
  | none => simp [ordinaryAt,hp] at ha
  | some tr =>
    cases tr with
    | none => simp [ordinaryAt,hp] at ha
    | some mv => exact ⟨mv,hm t _ hp⟩

theorem noHalt_never (m : Machine) (h : ∀ t, ∃ mv, m t = some mv) : NeverHalts m := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    cases hr : run m k blank with
    | none => simp [hr] at ih
    | some c =>
      obtain ⟨mv,hmv⟩ := h (readSlot c)
      simp [run,hr,rawStep,hmv]

theorem lastHole_cover {good : Machine → Prop} (p : PartialMachine) (s : Slot)
    (h : allOtherOrdinary p s = true)
    (neverGood : ∀ m, NeverHalts m → good m)
    (haltCover : Cover good (refine p s none)) : Cover good p := by
  apply Cover.leaf
  intro m hm
  cases hs : m s with
  | none =>
    apply haltCover.sound m
    have hc := compatible_refine p m s hm
    rw [hs] at hc
    exact hc
  | some mv =>
    apply neverGood m
    apply noHalt_never m
    intro t
    by_cases ht : t = s
    · subst t; exact ⟨mv,hs⟩
    · exact allOtherOrdinary_sound p s h m hm t ht

#print axioms allOtherOrdinary_sound
#print axioms noHalt_never
#print axioms lastHole_cover
end BB6.Agent50Raw34Plan
