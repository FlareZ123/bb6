import Frontier
import Lean.Elab.Tactic.Omega

namespace BB6Overwrite
open BB6Coverage

def delta (dir : Bool) : Int := if dir then 1 else -1

theorem opposite_departure (c : Config) (t : Move) (dir : Bool)
    (hr : t.right = !dir) :
    (applyMove c t).head + delta dir = c.head := by
  simp only [applyMove, hr]
  cases dir <;> simp [delta] <;> omega

theorem opposite_last_write (c : Config) (t : Move) (dir : Bool)
    (hr : t.right = !dir) :
    (applyMove c t).tape ((applyMove c t).head + delta dir) = t.write := by
  have h := opposite_departure c t dir hr
  change (if (applyMove c t).head + delta dir = c.head then t.write
    else c.tape ((applyMove c t).head + delta dir)) = t.write
  simp [h]

theorem next_head_read (c : Config) (t : Move) :
    (applyMove c t).tape (applyMove c t).head =
      c.tape (c.head + delta t.right) := by
  have hne : c.head + delta t.right ≠ c.head := by
    cases t.right <;> simp [delta] <;> omega
  have hhead : (applyMove c t).head = c.head + delta t.right := by
    cases hdir : t.right <;> simp [applyMove,delta,hdir]
  change (if (applyMove c t).head = c.head then t.write
    else c.tape (applyMove c t).head) = c.tape (c.head + delta t.right)
  rw [hhead]
  simp [hne]

theorem safe_next_cell (m : Machine) (p : Fin 6) (dir w : Bool)
    (hentry : ∀ slot t, m slot = some t → t.next = p →
      t.write = w ∧ t.right = !dir)
    (hinit : p = ⟨0, by decide⟩ → w = false)
    (n : Nat) (c : Config)
    (hrun : run m n blank = some c) (hs : c.state = p) :
    c.tape (c.head + delta dir) = w := by
  cases n with
  | zero =>
      have hc : c = blank := by simpa [run] using hrun.symm
      subst c
      have hp : p = ⟨0, by decide⟩ := by simpa [blank] using hs.symm
      have hw : w = false := hinit hp
      subst w
      simp [blank, delta]
  | succ n =>
      cases hprev : run m n blank with
      | none => simp [run,hprev] at hrun
      | some d =>
          cases haction : m (readSlot d) with
          | none => simp [run,rawStep,hprev,haction] at hrun
          | some t =>
              have hc : applyMove d t = c := by
                simpa [run,rawStep,hprev,haction] using hrun
              have ht : t.next = p := by
                rw [← hc] at hs
                exact hs
              obtain ⟨hw,hd⟩ := hentry (readSlot d) t haction ht
              rw [← hc]
              rw [opposite_last_write d t dir hd]
              exact hw

theorem safe_immediate_target (m : Machine)
    (p : Fin 6) (read_p dir forbidden : Bool) (target : Fin 6) (write_p : Bool)
    (hentry : ∀ slot t, m slot = some t → t.next = p →
      t.write = !forbidden ∧ t.right = !dir)
    (hinit : p = ⟨0, by decide⟩ → (!forbidden) = false)
    (n : Nat) (c : Config)
    (hrun : run m n blank = some c)
    (hs : readSlot c = (p,read_p)) :
    (applyMove c ⟨write_p,dir,target⟩).tape
      (applyMove c ⟨write_p,dir,target⟩).head ≠ forbidden := by
  have hp : c.state = p := by simpa [readSlot] using congrArg Prod.fst hs
  have hsafe := safe_next_cell m p dir (!forbidden) hentry hinit n c hrun hp
  rw [next_head_read]
  rw [hsafe]
  cases forbidden <;> decide

theorem forbidden_transition (m : Machine)
    (p : Fin 6) (read_p dir forbidden : Bool) (target : Fin 6) (write_p : Bool)
    (hrow : m (p,read_p) = some ⟨write_p,dir,target⟩)
    (hentry : ∀ slot t, m slot = some t → t.next = p →
      t.write = !forbidden ∧ t.right = !dir)
    (hinit : p = ⟨0, by decide⟩ → (!forbidden) = false)
    (n : Nat) (c : Config)
    (hrun : run m n blank = some c)
    (hs : readSlot c = (p,read_p)) :
    ∃ d, rawStep m c = some d ∧ d.state = target ∧
      d.tape d.head ≠ forbidden := by
  let mv : Move := ⟨write_p,dir,target⟩
  refine ⟨applyMove c mv, ?_, rfl, ?_⟩
  · simp [rawStep, hs, hrow, mv]
  · exact safe_immediate_target m p read_p dir forbidden target write_p
      hentry hinit n c hrun hs

#print axioms safe_next_cell
#print axioms safe_immediate_target
#print axioms forbidden_transition
end BB6Overwrite
