import Root56Coverage
import Raw11Extra127

namespace Raw11Extra127Coverage
open BB6Coverage BB6.Agent13BlankDelay
open Root56Coverage (center center_right center_left center_blank nearL nearR)

def table (v : Fin 3) : PartialMachine := fun slot =>
  (Raw11Extra127.transition v slot.1.val slot.2).map fun (w,d,t) => some ⟨w,d,t⟩

theorem step_center {v : Fin 3} {m : Machine} (hm : compatible (table v) m) (c : Config) (r : Root56.Config)
    (h : Raw11Extra127.step v (center c) = some r) :
    ∃ s, rawStep m c = some s ∧ center s = r := by
  change (Raw11Extra127.transition v c.state.val (c.tape c.head)).map (fun (w,d,q') => if d then Root56.right q'.val (nearL c) w (nearR c) else Root56.left q'.val (nearL c) w (nearR c)) = some r at h
  cases ht : Raw11Extra127.transition v c.state.val (c.tape c.head) with
  | none => simp [ht] at h
  | some t =>
    rcases t with ⟨w,d,q⟩
    have hh := hm (readSlot c) (some ⟨w,d,q⟩) (by unfold table; change (Raw11Extra127.transition v c.state.val (c.tape c.head)).map _ = _; rw [ht]; rfl)
    refine ⟨applyMove c ⟨w,d,q⟩,by simp [rawStep,hh],?_⟩
    cases d
    · rw [center_left]
      simpa [ht] using h
    · rw [center_right]
      simpa [ht] using h

theorem run_center {v : Fin 3} {m : Machine} (hm : compatible (table v) m) (n : Nat) (c : Config) (r : Root56.Config)
    (h : Raw11Extra127.run v n (center c) = some r) :
    ∃ s, run m n c = some s ∧ center s = r := by
  induction n generalizing r with
  | zero => exact ⟨c,rfl,Option.some.inj h⟩
  | succ n ih =>
    rw [Raw11Extra127.run_add] at h
    cases hr : Raw11Extra127.run v n (center c) with
    | none => simp [hr] at h
    | some r' =>
      obtain ⟨s,hs,hc⟩ := ih r' hr
      have hstep : Raw11Extra127.step v (center s) = some r := by
        rw [hc]
        simpa [hr,Raw11Extra127.run] using h
      obtain ⟨s',hs',hc'⟩ := step_center hm s r hstep
      exact ⟨s',by rw [run.eq_2,hs]; exact hs',hc'⟩

theorem never_compatible (v : Fin 3) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  have hn := Raw11Extra127.never v n
  rw [← center_blank] at hn
  cases h : Raw11Extra127.run v n (center blank) with
  | none => exact False.elim (hn h)
  | some r =>
    obtain ⟨s,hs,_⟩ := run_center hm n blank r h
    rw [hs]; rfl

theorem weighted (v : Fin 3) (B : Nat) : Cover (WeightedBound B) (table v) :=
  .leaf _ fun m hm => weighted_never B m (never_compatible v m hm)

#print axioms never_compatible
#print axioms weighted
end Raw11Extra127Coverage
