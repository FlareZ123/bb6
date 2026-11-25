import Raw110PairMacro
set_option maxHeartbeats 0
namespace BB6.Agent7Raw110Pair
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Complete every unassigned slot by a genuine halt. The sparse run is
    precisely the primitive run of this particular compatible completion. -/
def haltComplete (p : PartialMachine) : Machine := fun s => (p s).bind id

theorem haltComplete_compatible (p : PartialMachine) : compatible p (haltComplete p) := by
  intro s tr h
  simp [haltComplete,h]

theorem step_none_complete (p : PartialMachine) (z : Z) (h : step p z = none) :
    rawStep (haltComplete p) (embed z) = none := by
  rw [rawStep,read_embed]
  unfold step at h
  unfold haltComplete
  cases e : (p (z.q,z.l.headD false)).bind id with
  | none => rfl
  | some mv => rw [e] at h; contradiction

theorem zrun_none_complete (p : PartialMachine) (n : Nat) (z : Z)
    (h : zrun p n z = none) : run (haltComplete p) n (embed z) = none := by
  induction n generalizing z with
  | zero => simp [zrun] at h
  | succ n ih =>
    rw [show n+1=1+n by omega,run_append]
    cases hs : step p z with
    | none =>
      have hstep : run (haltComplete p) 1 (embed z) = none := by
        simpa [run] using step_none_complete p z hs
      rw [hstep]; rfl
    | some x =>
      have hfirst := step_sound p (haltComplete p) (haltComplete_compatible p) z x hs
      have hstep : run (haltComplete p) 1 (embed z) = some (embed x) := by
        simpa [run] using hfirst
      rw [hstep]
      exact ih x (by simpa [zrun,hs] using h)

theorem never_of_forever (slow : Bool) (h : Forever slow)
    (m : Machine) (hm : compatible (table slow) m) : NeverHalts m := by
  intro n
  obtain ⟨x,hx⟩ := h n
  have hz : (zrun (table slow) n start).map project = some x :=
    (run_project (table slow) n start).trans hx
  cases hrun : zrun (table slow) n start with
  | none => simp [hrun] at hz
  | some z =>
    have H := zrun_sound (table slow) m hm n start z hrun
    rw [start_embed] at H
    rw [H]; rfl

theorem forever_of_universal_never (slow : Bool)
    (h : ∀ m, compatible (table slow) m → NeverHalts m) : Forever slow := by
  intro n
  cases hz : zrun (table slow) n start with
  | none =>
    have hn := zrun_none_complete (table slow) n start hz
    rw [start_embed] at hn
    have H := h (haltComplete (table slow)) (haltComplete_compatible (table slow)) n
    simp [hn] at H
  | some z =>
    refine ⟨project z,?_⟩
    change run0 (table slow) n (project start) = some (project z)
    rw [← run_project,hz]; rfl

theorem universal_never_iff :
    (∀ m, compatible (table false) m → NeverHalts m) ↔
    (∀ m, compatible (table true) m → NeverHalts m) := by
  constructor
  · intro h
    exact never_of_forever true (forever_iff.mp (forever_of_universal_never false h))
  · intro h
    exact never_of_forever false (forever_iff.mpr (forever_of_universal_never true h))

#print axioms universal_never_iff
end BB6.Agent7Raw110Pair
