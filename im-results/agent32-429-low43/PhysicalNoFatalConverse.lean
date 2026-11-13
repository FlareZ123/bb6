import BB429PhysicalFrontier
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429PhysicalNoFatalConverse

open BB6Coverage BB429PhysicalFrontier

/-- The physical C/01 gateway: state C, scanned zero, marked cell immediately
    to the right. -/
def physicalC01 (c : Config) : Prop :=
  c.state.val = 2 ∧ c.tape c.head = false ∧ c.tape (c.head+1) = true

/-- A physical C/01 configuration takes one original-table step to D/1,
    whose next raw step is undefined. -/
theorem physicalC01_one_halts (c : Config)
    (hf : physicalC01 c) :
    ∃ d : Config, rawStep target429 c = some d ∧
      rawStep target429 d = none := by
  rcases hf with ⟨hs, hcur, hright⟩
  have hstate : c.state = (⟨2, by decide⟩ : Fin 6) := Fin.ext hs
  let mv : Move := ⟨false, true, ⟨3, by decide⟩⟩
  let d : Config := applyMove c mv
  have hread : readSlot c = (⟨2, by decide⟩, false) := by
    simp [readSlot, hstate, hcur]
  have htable : target429 (⟨2, by decide⟩, false) = some mv := by
    decide
  have htable' : target429 (2, false) = some mv := by
    simpa using htable
  have hstep : rawStep target429 c = some d := by
    simp [rawStep, hread, htable', d]
  have hne : c.head+1 ≠ c.head := by omega
  have hreadD : readSlot d = (⟨3, by decide⟩, true) := by
    simp [d, mv, readSlot, applyMove, hright, hne]
  have htableD : target429 (⟨3, by decide⟩, true) = none := by
    decide
  have htableD' : target429 (3, true) = none := by
    simpa using htableD
  have hhalt : rawStep target429 d = none := by
    simp [rawStep, hreadD, htableD']
  exact ⟨d, hstep, hhalt⟩

/-- Any successful original physical run ending at a live, non-C/01
    configuration has avoided C/01 at every primitive prefix. This is a
    machine-level converse, independent of the zipper representation. -/
theorem physical_run_prefix_c01_free
    (n : Nat) (c d : Config)
    (hrun : run target429 n c = some d)
    (hfree : ¬ physicalC01 d)
    (hlive : rawStep target429 d ≠ none) :
    ∀ t, t ≤ n → ∃ e, run target429 t c = some e ∧
      ¬ physicalC01 e := by
  induction n generalizing c d with
  | zero =>
      have hcd : c = d := by
        simpa [BB6Coverage.run] using hrun
      subst d
      intro t ht
      have ht0 : t = 0 := by omega
      subst t
      exact ⟨c, rfl, hfree⟩
  | succ n ih =>
      cases hp : run target429 n c with
      | none =>
          simp [BB6Coverage.run, hp] at hrun
      | some p =>
          have hstep : rawStep target429 p = some d := by
            simpa [BB6Coverage.run, hp] using hrun
          have hfreeP : ¬ physicalC01 p := by
            intro hf
            obtain ⟨q, hq, hhalt⟩ := physicalC01_one_halts p hf
            have hqd : q = d := Option.some.inj (hq.symm.trans hstep)
            subst d
            exact hlive hhalt
          have hliveP : rawStep target429 p ≠ none := by
            rw [hstep]
            simp
          intro t ht
          by_cases hle : t ≤ n
          · exact ih c p hp hfreeP hliveP t hle
          · have htEq : t = n+1 := by omega
            subst t
            exact ⟨d, hrun, hfree⟩

/-- A physical C/0 checkpoint with a blank immediate right cell is
    both nonfatal and live in the original machine. -/
theorem physicalC0_blank_right_live (c : Config)
    (hs : c.state.val = 2)
    (hcur : c.tape c.head = false)
    (hright : c.tape (c.head+1) = false) :
    ¬ physicalC01 c ∧ rawStep target429 c ≠ none := by
  have hstate : c.state = (⟨2, by decide⟩ : Fin 6) := Fin.ext hs
  have hread : readSlot c = (⟨2, by decide⟩, false) := by
    simp [readSlot, hstate, hcur]
  have htable : target429 (⟨2, by decide⟩, false) =
      some ⟨false, true, ⟨3, by decide⟩⟩ := by
    decide
  have hlive : rawStep target429 c ≠ none := by
    unfold rawStep
    rw [hread, htable]
    simp
  exact ⟨by simp [physicalC01, hright], hlive⟩

/-- Every successful physical run ending at a live C/0 checkpoint with
    blank immediate right cell is C/01-free at every primitive prefix. -/
theorem physical_run_prefix_c01_free_of_c0_blank_right
    (n : Nat) (c d : Config)
    (hrun : run target429 n c = some d)
    (hs : d.state.val = 2)
    (hcur : d.tape d.head = false)
    (hright : d.tape (d.head+1) = false) :
    ∀ t, t ≤ n → ∃ e, run target429 t c = some e ∧
      ¬ physicalC01 e := by
  obtain ⟨hfree, hlive⟩ :=
    physicalC0_blank_right_live d hs hcur hright
  exact physical_run_prefix_c01_free n c d hrun hfree hlive

/-- Exact composition law for the original physical #429 interpreter. -/
theorem physical_run_add (n t : Nat) (c : Config) :
    run target429 (n+t) c =
      (run target429 n c).bind (run target429 t) := by
  induction t with
  | zero => simp [BB6Coverage.run]
  | succ t ih =>
      calc
        run target429 (n+(t+1)) c =
            (run target429 (n+t) c).bind (rawStep target429) := by
              simp [BB6Coverage.run, Nat.add_succ]
        _ = ((run target429 n c).bind (run target429 t)).bind
              (rawStep target429) := by rw [ih]
        _ = (run target429 n c).bind
              (fun d => (run target429 t d).bind (rawStep target429)) := by
                simp [Option.bind_assoc]
        _ = (run target429 n c).bind (run target429 (t+1)) := by rfl

/-- Compose two exact physical run segments from their intermediate endpoint. -/
theorem physical_run_add_of_endpoint
    (n m : Nat) (c c1 c2 : Config)
    (h1 : run target429 n c = some c1)
    (h2 : run target429 m c1 = some c2) :
    run target429 (n+m) c = some c2 := by
  rw [physical_run_add, h1]
  exact h2

#print axioms physicalC01_one_halts
#print axioms physical_run_add
#print axioms physical_run_add_of_endpoint
#print axioms physicalC0_blank_right_live
#print axioms physical_run_prefix_c01_free
#print axioms physical_run_prefix_c01_free_of_c0_blank_right

end BB429PhysicalNoFatalConverse
