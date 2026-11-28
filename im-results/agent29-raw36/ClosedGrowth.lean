import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29ClosedGrowth
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega,rep,rep,ih,List.append_assoc]

/-- A closed set of live macro configurations proves nonhalting even if
    the macro phase and the number of parameters vary at each iteration. -/
theorem never_of_invariant (p : PartialMachine) (I : Z0 → Prop)
    (entry : Nat) (z0 : Z0)
    (first : run0 p entry ⟨0,[],[]⟩ = some z0) (h0 : I z0)
    (next : ∀ z, I z → ∃ k z', 0 < k ∧ run0 p k z = some z' ∧ I z')
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have live : ∀ n, ∃ t z, n ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some z ∧ I z := by
    intro n
    induction n with
    | zero => exact ⟨entry,z0,by omega,first,h0⟩
    | succ n ih =>
      obtain ⟨t,z,ht,hr,hz⟩ := ih
      obtain ⟨k,z',hk,hs,hz'⟩ := next z hz
      exact ⟨t+k,z',by omega,join0 hr hs,hz'⟩
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := live n
  have hz : (zrun p t BB6Coverage.Agent31Pump.start).map project = some z :=
    (run_project p t BB6Coverage.Agent31Pump.start).trans hr
  cases h : zrun p t BB6Coverage.Agent31Pump.start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p m hm t BB6Coverage.Agent31Pump.start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms never_of_invariant
end BB6.Agent29ClosedGrowth
