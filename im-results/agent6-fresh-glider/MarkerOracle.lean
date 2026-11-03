import MarkerTailExample
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

/-- On a finite-support tape, this decides that the right-facing ray
    consists of exactly one marked cell at the head, and all later cells
    are blank. Cells to the left may be arbitrary. -/
def finiteMarkerRight (c : FinRayCfg) : Bool :=
  c.ones.contains c.head &&
    c.ones.all (fun x => decide (x <= c.head))

theorem finiteMarkerRight_sound (c : FinRayCfg)
    (h : finiteMarkerRight c = true) :
    ∀ x, c.head <= x →
      finiteTape c x = markerPattern (x-c.head) := by
  have hpair : c.ones.contains c.head = true ∧
      c.ones.all (fun x => decide (x <= c.head)) = true :=
    (Bool.and_eq_true _ _).mp h
  have hbounded : ∀ y, y ∈ c.ones → y <= c.head := by
    intro y hy
    have hc := (List.all_eq_true.mp hpair.2) y hy
    simpa using hc
  intro x hx
  change c.ones.contains x = decide (x-c.head=0)
  by_cases heq : x=c.head
  · subst x
    simp [hpair.1]
  · have hnot : x ∉ c.ones := by
      intro hm
      have hle := hbounded x hm
      omega
    have hne : x-c.head ≠ 0 := by omega
    cases hc : c.ones.contains x with
    | false => simp [hc, hne]
    | true => exact False.elim (hnot (List.contains_iff_mem.mp hc))

def finiteMarkerSeed (s : Fin 6) : FinRayCfg :=
  {state := s, head := 0, ones := [0]}

theorem embed_finiteMarkerSeed (s : Fin 6) :
    embedFinRay (finiteMarkerSeed s) = tailSeed s markerPattern := by
  apply congrArg (fun tape : Int → Bool =>
    ({state := s, head := 0, tape := tape} : Config))
  funext x
  change ([0] : List Int).contains x =
    (if 0 <= x then markerPattern x else false)
  by_cases hx : x = 0
  · subst x
    decide
  · by_cases hp : 0 <= x
    · simp [markerPattern, hx, hp]
    · simp [markerPattern, hx, hp]

/-- An actual sparse finite blank-origin entry into a marked moving
    frontier, followed by a repeatable finite macro on a marked seed. -/
def finiteMarkerEntryCheck (p : PartialMachine)
    (entrySteps n : Nat) : Bool :=
  match finitePartialRun p entrySteps finiteBlank with
  | none => false
  | some entry =>
      match finitePartialRun p n (finiteMarkerSeed entry.state) with
      | none => false
      | some c =>
          finiteMarkerRight entry &&
          decide (c.state = entry.state) &&
          decide (0 < c.head) &&
          finiteMarkerRight c &&
          (List.range n).all (fun j =>
            match finitePartialRun p j (finiteMarkerSeed entry.state) with
            | none => false
            | some d => decide (0 <= d.head))

theorem finiteMarkerEntryCheck_sound (p : PartialMachine)
    (entrySteps n bound : Nat) (hn : 0 < n)
    (h : finiteMarkerEntryCheck p entrySteps n = true) :
    Cover (DecidedBelow bound) p := by
  cases he : finitePartialRun p entrySteps finiteBlank with
  | none =>
      simp [finiteMarkerEntryCheck, he] at h
  | some entry =>
      cases hc : finitePartialRun p n (finiteMarkerSeed entry.state) with
      | none =>
          simp [finiteMarkerEntryCheck, he, hc] at h
      | some c =>
          simp only [finiteMarkerEntryCheck, he, hc,
            Bool.and_eq_true, decide_eq_true_eq] at h
          rcases h with ⟨⟨⟨⟨hentryMarker, hsame⟩, hpos⟩, hmarker⟩, hwindow⟩
          apply Cover.leaf
          intro m hm
          left
          apply entry_tail_pattern_never m entry.state markerPattern
            entrySteps n c.head.toNat hn (by omega)
          · refine ⟨embedFinRay entry, ?_, ?_⟩
            · simpa only [embedFinRay_blank] using
                (finitePartialRun_sound p m hm
                  finiteBlank entry entrySteps he)
            · constructor
              · rfl
              · intro x hx
                exact finiteMarkerRight_sound entry hentryMarker x hx
          · refine ⟨embedFinRay c, ?_, ?_, ?_, ?_⟩
            · simpa only [embed_finiteMarkerSeed] using
                (finitePartialRun_sound p m hm
                  (finiteMarkerSeed entry.state) c n hc)
            · exact hsame
            · simp only [embedFinRay]
              omega
            · intro x hx
              have hge : c.head <= x := by omega
              have ht := finiteMarkerRight_sound c hmarker x hge
              simpa only [embedFinRay] using ht
          · intro j hj d hrun
            have hflag :
                (match finitePartialRun p j (finiteMarkerSeed entry.state) with
                 | none => false
                 | some t => decide (0 <= t.head)) = true :=
              (List.all_eq_true.mp hwindow) j (List.mem_range.mpr hj)
            cases hjfin : finitePartialRun p j (finiteMarkerSeed entry.state) with
            | none => simp [hjfin] at hflag
            | some t =>
                have hge : 0 <= t.head :=
                  of_decide_eq_true (by simpa [hjfin] using hflag)
                have hsource : run m j (tailSeed entry.state markerPattern) =
                    some (embedFinRay t) := by
                  simpa only [embed_finiteMarkerSeed] using
                    (finitePartialRun_sound p m hm
                      (finiteMarkerSeed entry.state) t j hjfin)
                have heq : d = embedFinRay t :=
                  Option.some.inj (hrun.symm.trans hsource)
                subst d
                simpa [embedFinRay] using hge

/-- Finite search over entry steps and macro length, accepting only
    universally sound all-completion nonhalting certificates. -/
def finiteMarkerEntryOracle (p : PartialMachine)
    (entryLimit macroLimit : Nat) : Bool :=
  (List.range entryLimit).any (fun k =>
    (List.range macroLimit).any (fun i =>
      finiteMarkerEntryCheck p k (i+1)))

theorem finiteMarkerEntryOracle_sound (p : PartialMachine)
    (entryLimit macroLimit bound : Nat)
    (h : finiteMarkerEntryOracle p entryLimit macroLimit = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp hk
  exact finiteMarkerEntryCheck_sound p k (i+1) bound (by omega) hi

theorem marked_check : finiteMarkerEntryCheck markedTailPump 2 3 = true := by
  decide

theorem marked_entry_oracle_accept :
    finiteMarkerEntryOracle markedTailPump 3 3 = true := by
  apply List.any_eq_true.mpr
  refine ⟨2, by decide, ?_⟩
  apply List.any_eq_true.mpr
  exact ⟨2, by decide, marked_check⟩

theorem marked_entry_oracle_leaf (bound : Nat) :
    Cover (DecidedBelow bound) markedTailPump :=
  finiteMarkerEntryOracle_sound markedTailPump 3 3 bound
    marked_entry_oracle_accept

#print axioms finiteMarkerRight_sound
#print axioms finiteMarkerEntryCheck_sound
#print axioms finiteMarkerEntryOracle_sound
#print axioms marked_entry_oracle_leaf
end BB6Coverage
