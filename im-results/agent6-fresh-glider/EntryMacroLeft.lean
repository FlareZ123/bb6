import EntryMacroOracle
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

/-- The leftward counterpart of finite-entry repetition: first a genuine
    blank-start prefix reaches a clean left ray, then a state-specific
    finite macro moves into a further pristine left frontier. -/
def finiteEntryMacroLeftCheck (p : PartialMachine) (entrySteps n : Nat) : Bool :=
  match finitePartialRun p entrySteps finiteBlank with
  | none => false
  | some entry =>
      match finitePartialRun p n (finiteStateBlank entry.state) with
      | none => false
      | some c =>
          finiteFreshLeft entry &&
          decide (c.state = entry.state) &&
          decide (c.head < 0) &&
          finiteFreshLeft c &&
          (List.range n).all (fun j =>
            match finitePartialRun p j (finiteStateBlank entry.state) with
            | none => false
            | some d => decide (d.head <= 0))

theorem finiteEntryMacroLeftCheck_sound (p : PartialMachine)
    (entrySteps n bound : Nat) (hn : 0 < n)
    (h : finiteEntryMacroLeftCheck p entrySteps n = true) :
    Cover (DecidedBelow bound) p := by
  cases he : finitePartialRun p entrySteps finiteBlank with
  | none =>
      simp [finiteEntryMacroLeftCheck, he] at h
  | some entry =>
      cases hc : finitePartialRun p n (finiteStateBlank entry.state) with
      | none =>
          simp [finiteEntryMacroLeftCheck, he, hc] at h
      | some c =>
          simp only [finiteEntryMacroLeftCheck, he, hc,
            Bool.and_eq_true, decide_eq_true_eq] at h
          rcases h with ⟨⟨⟨⟨hentryFresh, hsame⟩, hneg⟩, hmacroFresh⟩, hwindow⟩
          apply Cover.leaf
          intro m hm
          left
          apply entry_fresh_state_never_left m entry.state entrySteps n
            (-c.head).toNat hn (by omega)
          · refine ⟨embedFinRay entry, ?_, ?_, ?_⟩
            · simpa only [embedFinRay_blank] using
                (finitePartialRun_sound p m hm finiteBlank entry entrySteps he)
            · rfl
            · exact finiteFreshLeft_sound entry hentryFresh
          · refine ⟨embedFinRay c, ?_, ?_, ?_, ?_⟩
            · simpa only [embed_finiteStateBlank] using
                (finitePartialRun_sound p m hm (finiteStateBlank entry.state)
                  c n hc)
            · exact hsame
            · simp only [embedFinRay]
              omega
            · intro x hx
              have hle : x <= c.head := by omega
              exact finiteFreshLeft_sound c hmacroFresh x hle
          · intro j hj d hrun
            have hflag :
                (match finitePartialRun p j (finiteStateBlank entry.state) with
                  | none => false
                  | some t => decide (t.head <= 0)) = true :=
              (List.all_eq_true.mp hwindow) j (List.mem_range.mpr hj)
            cases hjfin : finitePartialRun p j (finiteStateBlank entry.state) with
            | none =>
                simp [hjfin] at hflag
            | some t =>
                have hle : t.head <= 0 :=
                  of_decide_eq_true (by simpa [hjfin] using hflag)
                have hsource :
                    run m j (stateBlank entry.state) = some (embedFinRay t) := by
                  simpa only [embed_finiteStateBlank] using
                    (finitePartialRun_sound p m hm
                      (finiteStateBlank entry.state) t j hjfin)
                have heq : d = embedFinRay t :=
                  Option.some.inj (hrun.symm.trans hsource)
                subst d
                simpa [embedFinRay] using hle

def finiteEntryMacroLeftOracle (p : PartialMachine)
    (entryLimit macroLimit : Nat) : Bool :=
  (List.range entryLimit).any (fun k =>
    (List.range macroLimit).any (fun i =>
      finiteEntryMacroLeftCheck p k (i+1)))

theorem finiteEntryMacroLeftOracle_sound (p : PartialMachine)
    (entryLimit macroLimit bound : Nat)
    (h : finiteEntryMacroLeftOracle p entryLimit macroLimit = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp hk
  exact finiteEntryMacroLeftCheck_sound p k (i+1) bound (by omega) hi

/-- Search finite blank-origin entries and then left or right macros. -/
def finiteEntryMacroBiOracle (p : PartialMachine)
    (entryLimit macroLimit : Nat) : Bool :=
  finiteEntryMacroOracle p entryLimit macroLimit ||
    finiteEntryMacroLeftOracle p entryLimit macroLimit

theorem finiteEntryMacroBiOracle_sound (p : PartialMachine)
    (entryLimit macroLimit bound : Nat)
    (h : finiteEntryMacroBiOracle p entryLimit macroLimit = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with hr | hl
  · exact finiteEntryMacroOracle_sound p entryLimit macroLimit bound hr
  · exact finiteEntryMacroLeftOracle_sound p entryLimit macroLimit bound hl

/-- Reflected genuine-entry sparse table; unlike A-only macro, the
    infinitely repeated control state is B and the head moves left. -/
def entryToBLeftExample : PartialMachine := fun s =>
  if s = (0,false) then some (some ⟨false,false,1⟩)
  else if s = (1,false) then some (some ⟨true,false,2⟩)
  else if s = (2,false) then some (some ⟨false,true,3⟩)
  else if s = (3,true) then some (some ⟨false,false,1⟩)
  else none

theorem entryToBLeft_check :
    finiteEntryMacroLeftCheck entryToBLeftExample 1 3 = true := by decide

theorem entryToBLeft_cover (bound : Nat) :
    Cover (DecidedBelow bound) entryToBLeftExample :=
  finiteEntryMacroLeftCheck_sound entryToBLeftExample 1 3 bound
    (by decide) entryToBLeft_check

#print axioms finiteEntryMacroLeftCheck_sound
#print axioms finiteEntryMacroLeftOracle_sound
#print axioms finiteEntryMacroBiOracle_sound
#print axioms entryToBLeft_cover

end BB6Coverage
