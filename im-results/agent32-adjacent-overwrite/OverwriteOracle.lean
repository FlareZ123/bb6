import GenericOverwrite

namespace BB6Overwrite
open BB6Coverage

/-- Check syntactically that every ordinary transition entering p wrote the
    same bit and moved opposite the chosen outgoing direction. -/
def incomingConsistent (m : Machine) (p : Fin 6) (w dir : Bool) : Bool :=
  (List.finRange 6).all (fun s =>
    ([false,true] : List Bool).all (fun b =>
      match m (s,b) with
      | none => true
      | some t => if decide (t.next=p) then
                      decide (t.write=w ∧ t.right= !dir)
                  else true))

theorem incomingConsistent_sound (m : Machine) (p : Fin 6) (w dir : Bool)
    (hh : incomingConsistent m p w dir = true) :
    ∀ (slot : Slot) (t : Move), m slot = some t → t.next = p →
      t.write = w ∧ t.right = !dir := by
  intro ⟨s,b⟩ t hs ht
  unfold incomingConsistent at hh
  have hq := (List.all_eq_true.mp hh) s (List.mem_finRange s)
  have hb : (match m (s,b) with
      | none => true
      | some t => if decide (t.next = p) then
         decide (t.write = w ∧ t.right = !dir) else true) = true := by
    exact (List.all_eq_true.mp hq) b (by cases b <;> simp)
  simp [hs, ht] at hb
  exact hb

/-- A decidable sufficient certificate for all-time exclusion of the listed
    immediate predecessor of a halting input with read bit forb. -/
def forbiddenCheck (m : Machine) (p : Fin 6) (rd dir forb : Bool)
    (q : Fin 6) (wr : Bool) : Bool :=
    decide (m (p,rd) = some ⟨wr,dir,q⟩) &&
    incomingConsistent m p (!forb) dir &&
    decide (p = ⟨0, by decide⟩ → (!forb) = false)

theorem forbiddenCheck_sound (m : Machine) (p : Fin 6)
    (rd dir forb : Bool) (q : Fin 6) (wr : Bool)
    (hh : forbiddenCheck m p rd dir forb q wr = true)
    (n : Nat) (c : Config) (hrun : run m n blank = some c)
    (hslot : readSlot c = (p,rd)) :
    ∃ d, rawStep m c = some d ∧ d.state = q ∧ d.tape d.head ≠ forb := by
  unfold forbiddenCheck at hh
  simp only [Bool.and_eq_true] at hh
  obtain ⟨⟨hrow, hentry⟩, hinit⟩ := hh
  have hrow' : m (p,rd) = some ⟨wr,dir,q⟩ := by
    exact of_decide_eq_true hrow
  have hinit' : p = ⟨0, by decide⟩ → (!forb) = false := by
    exact of_decide_eq_true hinit
  exact forbidden_transition m p rd dir forb q wr hrow'
    (incomingConsistent_sound m p (!forb) dir hentry)
    hinit' n c hrun hslot

#print axioms incomingConsistent_sound
#print axioms forbiddenCheck_sound
end BB6Overwrite
