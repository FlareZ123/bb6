import Machine623DepthFiveSplit

namespace BB6Coverage

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/-- The seventh useful D/1 child: write one, move right, remain in D. -/
def machine623D1ToDRight1 : Move :=
  ⟨true, true, ⟨3, by decide⟩⟩

private def machine623D1GliderPartial : PartialMachine :=
  machine623D1Child (some machine623D1ToDRight1)

private def machine623D1GliderState : Fin 6 := ⟨3, by decide⟩

/-- The moving boundary cell is one; every cell strictly to its right is
    blank.  This one-cell tail word is preserved by the three-step macro. -/
private def machine623D1GliderPattern (x : Int) : Bool :=
  decide (x = 0)

private def machine623D1GliderSeed : FinRayCfg :=
  { state := machine623D1GliderState, head := 0, ones := [0] }

private def machine623D1GliderAt1 : FinRayCfg :=
  { state := machine623D1GliderState, head := 1, ones := [0, 0] }

private def machine623D1GliderAt2 : FinRayCfg :=
  { state := machine623D1GliderState, head := 0, ones := [1, 0, 0] }

private def machine623D1GliderEnd : FinRayCfg :=
  { state := machine623D1GliderState, head := 1, ones := [0, 1, 0, 0] }

/-- Exact blank-origin entry after twelve moves.  The finite support list
    retains duplicate writes because FinRayCfg is a trace representation. -/
private def machine623D1GliderEntry : FinRayCfg :=
  { state := machine623D1GliderState, head := 4,
    ones := [3, 4, 3, 2, 1, 0, 1, 2, 3, 0] }

private theorem machine623D1Glider_seed_eq_tailSeed :
    embedFinRay machine623D1GliderSeed =
      tailSeed machine623D1GliderState machine623D1GliderPattern := by
  apply Config.ext
  · rfl
  · rfl
  · funext x
    by_cases hx : x = 0
    · subst x
      simp [embedFinRay, finiteTape, machine623D1GliderSeed,
        tailSeed, machine623D1GliderPattern]
    · simp [embedFinRay, finiteTape, machine623D1GliderSeed,
        tailSeed, machine623D1GliderPattern, hx]

private theorem machine623D1GliderEntry_tail (x : Int) (hx : 4 ≤ x) :
    finiteTape machine623D1GliderEntry x =
      machine623D1GliderPattern (x - 4) := by
  by_cases h4 : x = 4
  · subst x
    simp [finiteTape, machine623D1GliderEntry, machine623D1GliderPattern]
  · have hgt : 4 < x := by omega
    have hnot : x ∉ machine623D1GliderEntry.ones := by
      simp [machine623D1GliderEntry]
      omega
    have hcontains :
        machine623D1GliderEntry.ones.contains x = false := by
      cases h : machine623D1GliderEntry.ones.contains x with
      | false => rfl
      | true => exact False.elim
          (hnot (List.contains_iff_mem.mp h))
    have hpattern :
        machine623D1GliderPattern (x - 4) = false := by
      have hne : x - 4 ≠ 0 := by omega
      simp [machine623D1GliderPattern, hne]
    simp [finiteTape, hcontains, hpattern]

private theorem machine623D1Glider_entry_pattern :
    TailPatternRay machine623D1GliderState machine623D1GliderPattern
      (embedFinRay machine623D1GliderEntry) := by
  constructor
  · rfl
  · intro x hx
    have hx4 : (4 : Int) ≤ x := by
      simpa [embedFinRay, machine623D1GliderEntry] using hx
    simpa [embedFinRay, machine623D1GliderEntry] using
      machine623D1GliderEntry_tail x hx4

private theorem machine623D1GliderEnd_tail (x : Int) (hx : 1 ≤ x) :
    finiteTape machine623D1GliderEnd x =
      machine623D1GliderPattern (x - 1) := by
  by_cases h1 : x = 1
  · subst x
    simp [finiteTape, machine623D1GliderEnd, machine623D1GliderPattern]
  · have hgt : 1 < x := by omega
    have hnot : x ∉ machine623D1GliderEnd.ones := by
      simp [machine623D1GliderEnd]
      omega
    have hcontains :
        machine623D1GliderEnd.ones.contains x = false := by
      cases h : machine623D1GliderEnd.ones.contains x with
      | false => rfl
      | true => exact False.elim
          (hnot (List.contains_iff_mem.mp h))
    have hpattern :
        machine623D1GliderPattern (x - 1) = false := by
      have hne : x - 1 ≠ 0 := by omega
      simp [machine623D1GliderPattern, hne]
    simp [finiteTape, hcontains, hpattern]

private theorem machine623D1Glider_entry (m : Machine)
    (hm : compatible machine623D1GliderPartial m) :
    ∃ q, run m 12 blank = some q ∧
      TailPatternRay machine623D1GliderState machine623D1GliderPattern q := by
  have hrun :
      finitePartialRun machine623D1GliderPartial 12 finiteBlank =
        some machine623D1GliderEntry := by decide
  have hsource := finitePartialRun_sound machine623D1GliderPartial m hm
    finiteBlank machine623D1GliderEntry 12 hrun
  refine ⟨embedFinRay machine623D1GliderEntry, ?_,
    machine623D1Glider_entry_pattern⟩
  simpa only [embedFinRay_blank] using hsource

private theorem machine623D1Glider_macro (m : Machine)
    (hm : compatible machine623D1GliderPartial m) :
    ∃ r, run m 3
        (tailSeed machine623D1GliderState machine623D1GliderPattern) =
          some r ∧
      r.state = machine623D1GliderState ∧
      r.head = 1 ∧
      ∀ x, (1 : Int) ≤ x →
        r.tape x = machine623D1GliderPattern (x - 1) := by
  have hrun :
      finitePartialRun machine623D1GliderPartial 3
        machine623D1GliderSeed = some machine623D1GliderEnd := by decide
  have hsource := finitePartialRun_sound machine623D1GliderPartial m hm
    machine623D1GliderSeed machine623D1GliderEnd 3 hrun
  have hsource' :
      run m 3
        (tailSeed machine623D1GliderState machine623D1GliderPattern) =
          some (embedFinRay machine623D1GliderEnd) := by
    rw [← machine623D1Glider_seed_eq_tailSeed]
    exact hsource
  refine ⟨embedFinRay machine623D1GliderEnd, hsource', rfl, rfl, ?_⟩
  intro x hx
  simpa [embedFinRay, machine623D1GliderEnd] using
    machine623D1GliderEnd_tail x hx

private theorem machine623D1Glider_window (m : Machine)
    (hm : compatible machine623D1GliderPartial m) :
    ∀ k, k < 3 →
      ∀ d, run m k
        (tailSeed machine623D1GliderState machine623D1GliderPattern) =
          some d → 0 ≤ d.head := by
  intro k hk d hd
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hkcases with hk0 | hk1 | hk2
  · subst k
    have hrun :
        finitePartialRun machine623D1GliderPartial 0
          machine623D1GliderSeed = some machine623D1GliderSeed := rfl
    have hsource := finitePartialRun_sound machine623D1GliderPartial m hm
      machine623D1GliderSeed machine623D1GliderSeed 0 hrun
    have hsource' :
        run m 0
          (tailSeed machine623D1GliderState machine623D1GliderPattern) =
            some (embedFinRay machine623D1GliderSeed) := by
      rw [← machine623D1Glider_seed_eq_tailSeed]
      exact hsource
    have hdeq : d = embedFinRay machine623D1GliderSeed :=
      Option.some.inj (hd.symm.trans hsource')
    subst d
    simp [embedFinRay, machine623D1GliderSeed]
  · subst k
    have hrun :
        finitePartialRun machine623D1GliderPartial 1
          machine623D1GliderSeed = some machine623D1GliderAt1 := by decide
    have hsource := finitePartialRun_sound machine623D1GliderPartial m hm
      machine623D1GliderSeed machine623D1GliderAt1 1 hrun
    have hsource' :
        run m 1
          (tailSeed machine623D1GliderState machine623D1GliderPattern) =
            some (embedFinRay machine623D1GliderAt1) := by
      rw [← machine623D1Glider_seed_eq_tailSeed]
      exact hsource
    have hdeq : d = embedFinRay machine623D1GliderAt1 :=
      Option.some.inj (hd.symm.trans hsource')
    subst d
    simp [embedFinRay, machine623D1GliderAt1]
  · subst k
    have hrun :
        finitePartialRun machine623D1GliderPartial 2
          machine623D1GliderSeed = some machine623D1GliderAt2 := by decide
    have hsource := finitePartialRun_sound machine623D1GliderPartial m hm
      machine623D1GliderSeed machine623D1GliderAt2 2 hrun
    have hsource' :
        run m 2
          (tailSeed machine623D1GliderState machine623D1GliderPattern) =
            some (embedFinRay machine623D1GliderAt2) := by
      rw [← machine623D1Glider_seed_eq_tailSeed]
      exact hsource
    have hdeq : d = embedFinRay machine623D1GliderAt2 :=
      Option.some.inj (hd.symm.trans hsource')
    subst d
    simp [embedFinRay, machine623D1GliderAt2]

/-- A one-cell moving-frontier glider is a new all-time nonhalting
    certificate for the D/1 = 1RD child of the authentic #623 depth-five
    raw-table split.  It uses the existing arbitrary-tail pumping theorem,
    not a finite-runtime extrapolation. -/
theorem machine623D1ToDRight1_never (m : Machine)
    (hm : compatible machine623D1GliderPartial m) : NeverHalts m :=
  entry_tail_pattern_never m machine623D1GliderState
    machine623D1GliderPattern 12 3 1 (by decide) (by decide)
    (machine623D1Glider_entry m hm)
    (machine623D1Glider_macro m hm)
    (machine623D1Glider_window m hm)

theorem machine623D1ToDRight1_cover :
    Cover (DecidedBelow 6)
      (machine623D1Child (some machine623D1ToDRight1)) := by
  apply Cover.leaf
  intro m hm
  exact Or.inl (machine623D1ToDRight1_never m hm)

#print axioms machine623D1ToDRight1_never
#print axioms machine623D1ToDRight1_cover

end BB6Coverage
