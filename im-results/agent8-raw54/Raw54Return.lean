import SweepPumping
namespace BB6.Agent8Raw54
open BB6Coverage BB6Coverage.Agent31Pump Agent50Zipper

theorem never_of_returns (p : PartialMachine) (family : Nat → Z0) (entry : Nat)
    (first : run0 p entry ⟨0,[],[]⟩ = some (family 0))
    (next : ∀ n, ∃ t, 0<t ∧ run0 p t (family n) = some (family (n+1)))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t, k ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some (family k) := by
    intro k
    induction k with
    | zero => exact ⟨entry,by omega,first⟩
    | succ k ih =>
      obtain ⟨t,ht,hr⟩ := ih
      obtain ⟨s,hs,hstep⟩ := next k
      exact ⟨t+s,by omega,join0 hr hstep⟩
  intro n
  obtain ⟨t,ht,hr⟩ := arbitrary n
  have hz : (zrun p t start).map project = some (family n) := (run_project p t start).trans hr
  cases h : zrun p t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl

#print axioms never_of_returns
end BB6.Agent8Raw54
