import SweepPumping
open BB6Coverage BB6Coverage.Agent31Pump
namespace BB6Coverage.Agent31Pump
section
variable (p : PartialMachine) (I : Z0 → Prop)
variable (closed : ∀ c, I c → ∃ t d, 0 < t ∧ run0 p t c = some d ∧ I d)
noncomputable def phaseTime (c : {z // I z}) : Nat := Classical.choose (closed c.val c.property)
noncomputable def phaseNext (c : {z // I z}) : {z // I z} :=
  ⟨Classical.choose (Classical.choose_spec (closed c.val c.property)), (Classical.choose_spec (Classical.choose_spec (closed c.val c.property))).2.2⟩
theorem phaseTime_pos (c : {z // I z}) : 0 < phaseTime p I closed c :=
  (Classical.choose_spec (Classical.choose_spec (closed c.val c.property))).1
theorem phaseNext_run (c : {z // I z}) : run0 p (phaseTime p I closed c) c.val = some (phaseNext p I closed c).val :=
  (Classical.choose_spec (Classical.choose_spec (closed c.val c.property))).2.1
noncomputable def phaseOrbit (z : {z // I z}) : Nat → {z // I z}
  | 0 => z
  | n+1 => phaseNext p I closed (phaseOrbit z n)
theorem phaseOrbit_step (z : {z // I z}) (n : Nat) : run0 p (phaseTime p I closed (phaseOrbit p I closed z n)) (phaseOrbit p I closed z n).val = some (phaseOrbit p I closed z (n+1)).val :=
  phaseNext_run p I closed (phaseOrbit p I closed z n)
end
end BB6Coverage.Agent31Pump
