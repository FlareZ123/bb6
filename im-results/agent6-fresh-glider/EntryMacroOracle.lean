import RayMacro
import RayFinite
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

/-- The infinite-tape blank input with any specified control state,
    represented by an exact finite-support tape. -/
def finiteStateBlank (state : Fin 6) : FinRayCfg :=
  { state := state, head := 0, ones := [] }

@[simp] theorem embed_finiteStateBlank (state : Fin 6) :
    embedFinRay (finiteStateBlank state) = stateBlank state := rfl

/-- A sparse genuine-blank entry to a fresh ray, followed by a distinct
    state-specific finite macro whose return advances into virgin blanks.
    The macro is independently tested from a blank tape with the entry
    control state, which is valid by the translation theorem. -/
def finiteEntryMacroCheck (p : PartialMachine) (entrySteps n : Nat) : Bool :=
  match finitePartialRun p entrySteps finiteBlank with
  | none => false
  | some entry =>
      match finitePartialRun p n (finiteStateBlank entry.state) with
      | none => false
      | some c =>
          finiteFreshRight entry &&
          decide (c.state = entry.state) &&
          decide (0 < c.head) &&
          finiteFreshRight c &&
          (List.range n).all (fun j =>
            match finitePartialRun p j (finiteStateBlank entry.state) with
            | none => false
            | some d => decide (0 <= d.head))

theorem finiteEntryMacroCheck_sound (p : PartialMachine)
    (entrySteps n bound : Nat) (hn : 0 < n)
    (h : finiteEntryMacroCheck p entrySteps n = true) :
    Cover (DecidedBelow bound) p := by
  cases he : finitePartialRun p entrySteps finiteBlank with
  | none =>
      simp [finiteEntryMacroCheck, he] at h
  | some entry =>
      cases hc : finitePartialRun p n (finiteStateBlank entry.state) with
      | none =>
          simp [finiteEntryMacroCheck, he, hc] at h
      | some c =>
          simp only [finiteEntryMacroCheck, he, hc,
            Bool.and_eq_true, decide_eq_true_eq] at h
          rcases h with ⟨⟨⟨⟨hentryFresh, hsame⟩, hpos⟩, hmacroFresh⟩, hwindow⟩
          apply Cover.leaf
          intro m hm
          left
          apply entry_fresh_state_never m entry.state entrySteps
            n c.head.toNat hn (by omega)
          · refine ⟨embedFinRay entry, ?_, ?_⟩
            · simpa only [embedFinRay_blank] using
                (finitePartialRun_sound p m hm finiteBlank entry entrySteps he)
            · exact ⟨rfl, finiteFreshRight_sound entry hentryFresh⟩
          · refine ⟨embedFinRay c, ?_, ?_, ?_, ?_⟩
            · simpa only [embed_finiteStateBlank] using
                (finitePartialRun_sound p m hm (finiteStateBlank entry.state)
                  c n hc)
            · exact hsame
            · simp only [embedFinRay]
              omega
            · intro x hx
              exact finiteFreshRight_sound c hmacroFresh x (by simpa [embedFinRay] using hx)
          · intro j hj d hrun
            have hflag :
                (match finitePartialRun p j (finiteStateBlank entry.state) with
                  | none => false
                  | some t => decide (0 <= t.head)) = true :=
              (List.all_eq_true.mp hwindow) j (List.mem_range.mpr hj)
            cases hjfin : finitePartialRun p j (finiteStateBlank entry.state) with
            | none =>
                simp [hjfin] at hflag
            | some t =>
                have hge : 0 <= t.head :=
                  of_decide_eq_true (by simpa [hjfin] using hflag)
                have hsource :
                    run m j (stateBlank entry.state) = some (embedFinRay t) := by
                  simpa only [embed_finiteStateBlank] using
                    (finitePartialRun_sound p m hm
                      (finiteStateBlank entry.state) t j hjfin)
                have heq : d = embedFinRay t :=
                  Option.some.inj (hrun.symm.trans hsource)
                subst d
                simpa [embedFinRay] using hge

/-- Bounded discovery of true blank entries with any repeated control
    state; each successful finite witness proves an infinite run. -/
def finiteEntryMacroOracle (p : PartialMachine)
    (entryLimit macroLimit : Nat) : Bool :=
  (List.range entryLimit).any (fun k =>
    (List.range macroLimit).any (fun i =>
      finiteEntryMacroCheck p k (i+1)))

theorem finiteEntryMacroOracle_sound (p : PartialMachine)
    (entryLimit macroLimit bound : Nat)
    (h : finiteEntryMacroOracle p entryLimit macroLimit = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp hk
  exact finiteEntryMacroCheck_sound p k (i+1) bound (by omega) hi

/-- Genuine A to B entry, followed by a fresh-ray cycle at B that
    never returns to A. This is outside the original A-only macro oracle. -/
def entryToBExample : PartialMachine := fun s =>
  if s = (0,false) then some (some ⟨false,true,1⟩)
  else if s = (1,false) then some (some ⟨true,true,2⟩)
  else if s = (2,false) then some (some ⟨false,false,3⟩)
  else if s = (3,true) then some (some ⟨false,true,1⟩)
  else none

theorem entryToB_check :
    finiteEntryMacroCheck entryToBExample 1 3 = true := by decide

theorem entryToB_cover (bound : Nat) :
    Cover (DecidedBelow bound) entryToBExample :=
  finiteEntryMacroCheck_sound entryToBExample 1 3 bound
    (by decide) entryToB_check

#print axioms finiteEntryMacroCheck_sound
#print axioms finiteEntryMacroOracle_sound
#print axioms entryToB_cover

end BB6Coverage
