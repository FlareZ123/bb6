import SweepPumping
namespace BB6Coverage.Agent4Live
open BB6Coverage Agent31Pump Agent50Zipper

/-- Unbounded finite live prefixes imply nonhalting for every compatible
completion. The endpoint need not be a predetermined family. -/
theorem never_of_live (p : PartialMachine)
    (arbitrary : ∀ n : Nat, ∃ t z, n ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some z)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨t,c,ht,hr⟩ := arbitrary n
  have hz : (zrun p t Agent31Pump.start).map project = some c :=
    (run_project p t Agent31Pump.start).trans hr
  cases h : zrun p t Agent31Pump.start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p m hm t Agent31Pump.start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never_of_live
end BB6Coverage.Agent4Live
