import Raw112CarryNever
import Raw112Sibling

namespace BB6Coverage.Agent31Pump.Raw112Sibling
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

theorem never (m : Machine) (hm : compatible sibling m) : NeverHalts m := by
  intro n
  obtain ⟨t,b,ht,hr⟩ := sibling_unbounded n
  have hz : (zrun sibling t start).map project = some b :=
    (run_project sibling t start).trans hr
  cases h : zrun sibling t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound sibling m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6Coverage.Agent31Pump.Raw112Sibling
