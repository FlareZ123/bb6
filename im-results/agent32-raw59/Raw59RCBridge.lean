import Raw59RCShared
namespace BB6.Agent32Raw59RC
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr⟩ := arbitrary_live v n
  have hz : (zrun (table v) t BB6Coverage.Agent31Pump.start).map project = some z :=
    (run_project (table v) t BB6Coverage.Agent31Pump.start).trans hr
  cases h : zrun (table v) t BB6Coverage.Agent31Pump.start with
  | none => simp [h] at hz
  | some q =>
    have H := zrun_sound (table v) m hm t BB6Coverage.Agent31Pump.start q h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms never
end BB6.Agent32Raw59RC

namespace BB6.Agent32Raw59RC0
open BB6Coverage
def table : PartialMachine := BB6.Agent32Raw59RC.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent32Raw59RC.never false m hm
#print axioms never
end BB6.Agent32Raw59RC0

namespace BB6.Agent32Raw59RC1
open BB6Coverage
def table : PartialMachine := BB6.Agent32Raw59RC.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent32Raw59RC.never true m hm
#print axioms never
end BB6.Agent32Raw59RC1
