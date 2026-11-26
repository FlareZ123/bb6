import Raw54RACounterCore
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RAClosed
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.RACounter Agent50Zipper

/-- A total positive-cost return on a section suffices; the return need not
be an increment or even be injective. -/
theorem neverOfSection (p : PartialMachine) (W : Type) (f : W → Z0)
    (w0 : W) (entry : Nat)
    (first : run0 p entry ⟨0,[],[]⟩ = some (f w0))
    (closed : ∀ w, ∃ t w', 0 < t ∧ run0 p t (f w) = some (f w'))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k : Nat, ∃ t w, k ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some (f w) := by
    intro k
    induction k with
    | zero => exact ⟨entry,w0,by omega,first⟩
    | succ k ih =>
      obtain ⟨t,w,ht,h⟩ := ih
      obtain ⟨s,w',hs,g⟩ := closed w
      exact ⟨t+s,w',by omega,join0 h g⟩
  intro n
  obtain ⟨t,w,ht,hr⟩ := arbitrary n
  have hz : (zrun p t start).map project = some (f w) := (run_project p t start).trans hr
  cases h : zrun p t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl
#print axioms neverOfSection
end BB6.Agent8Raw54.RAClosed
