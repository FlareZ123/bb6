import F418SourceEvents
import F418Seed
namespace BB6.Agent32F418.Root
open BB6Coverage BB6.Agent32FiniteSource
open Arithmetic EventSystem State TapeEncoding SourceEvents

/-- The literal blank-start seed agrees with the arithmetic encoding. -/
theorem blank_seed : RunEq 670 finiteBlank (encode EventSystem.seed) := by
  apply runEq_output (runEq_of_run BB6.Agent32F418.seed)
  have hr : seedRight = rightWord 1 39464 16 := by decide
  rw [hr]
  apply cfg_eq
  · exact word_symm (by simpa only [leftWord,sparse_zero,List.append_nil] using word_zero 3)
  · exact word_refl _

/-- Every arithmetic iterate is reached by at least as many primitive transitions. -/
theorem iterate_source {s t : State} {k : Nat} (hs : Safe s) (hr : iterate k s = some t) :
    ∃ steps, k≤steps ∧ RunEq steps (encode s) (encode t) := by
  induction k generalizing s with
  | zero =>
    simp [iterate] at hr
    subst t
    exact ⟨0,by omega,runEq_of_run (run_zero _)⟩
  | succ k ih =>
    cases he : advance s with
    | none => simp [iterate,he] at hr
    | some u =>
      obtain ⟨m,hm,h1⟩ := advance_source hs he
      obtain ⟨n,hn,h2⟩ := ih (safe_advance hs he) (by simpa [iterate,he] using hr)
      exact ⟨m+n,by omega,runEq_trans h1 h2⟩

theorem blank_iterate_source {k : Nat} {s : State} (hr : iterate k EventSystem.seed = some s) :
    ∃ steps, 670+k≤steps ∧ RunEq steps finiteBlank (encode s) := by
  obtain ⟨m,hm,h⟩ := iterate_source seed_safe hr
  exact ⟨670+m,by omega,runEq_trans blank_seed h⟩

theorem prefix_exists {m : Machine} {c d : FiniteCfg} {n k : Nat}
    (hn : n≤k) (hr : finiteRun m k c = some d) : ∃ e, finiteRun m n c = some e := by
  have he : k=n+(k-n) := by omega
  rw [he,run_append] at hr
  cases h : finiteRun m n c with
  | none => simp [h] at hr
  | some e => exact ⟨e,rfl⟩

/-- An infinite arithmetic orbit yields arbitrarily long successful primitive runs. -/
theorem source_never_of_events (h : ∀ k, ∃ s, iterate k EventSystem.seed = some s) : NeverHalts machine := by
  apply (finite_never_iff machine).mp
  intro k
  obtain ⟨s,hs⟩ := h k
  obtain ⟨m,hm,d,hr,_⟩ := blank_iterate_source hs
  exact prefix_exists (by omega) hr

/-- Every terminating arithmetic orbit reaches exactly the missing F/1 instruction. -/
theorem source_halt_of_events (h : ∃ k, iterate k EventSystem.seed = none) :
    ∃ n c, finiteRun machine n finiteBlank = some c ∧ query c = (5,true) ∧ step machine c = none := by
  obtain ⟨k,hk⟩ := h
  obtain ⟨s,hr,ht⟩ := iterate_none_has_terminal hk
  obtain ⟨j,hj⟩ := reaches_iff.mp hr
  obtain ⟨m,_,h1⟩ := blank_iterate_source hj
  obtain ⟨n,c,_,h2,hq,hh⟩ := terminal_source (seed_orbit_safe hj) ht
  obtain ⟨d,hd,he⟩ := runEq_trans h1 (runEq_of_run h2)
  exact ⟨m+n,d,hd,(tape_query he).trans hq,tape_halt (tape_symm he) hh⟩

/-- Source-level iff: halting of the literal table is equivalent to reaching
    the fatal odd-bit language in the arithmetic seed orbit. -/
theorem source_termination_iff : (∃ k, finiteRun machine k finiteBlank = none) ↔
    ∃ s, Reaches EventSystem.seed s ∧ Fatal s := by
  rw [← seed_termination_iff]
  constructor
  · rintro ⟨k,hk⟩
    apply Classical.byContradiction
    intro hn
    have h : ∀ j, ∃ s, iterate j EventSystem.seed = some s := by
      intro j
      cases hj : iterate j EventSystem.seed with
      | none => exact False.elim (hn ⟨j,hj⟩)
      | some s => exact ⟨s,rfl⟩
    obtain ⟨c,hc⟩ := (finite_never_iff machine).mpr (source_never_of_events h) k
    rw [hk] at hc
    contradiction
  · intro h
    obtain ⟨n,c,hr,_,hh⟩ := source_halt_of_events h
    refine ⟨n+1,?_⟩
    rw [run_append,hr]
    simp [finiteRun,hh]

/-- Absolute-tape formulation used by the repository coverage framework. -/
theorem source_nonhalt_iff : NeverHalts machine ↔
    ¬ ∃ s, Reaches EventSystem.seed s ∧ Fatal s := by
  rw [← source_termination_iff,← finite_never_iff]
  constructor
  · intro h hn
    obtain ⟨n,hn⟩ := hn
    obtain ⟨c,hc⟩ := h n
    rw [hn] at hc
    contradiction
  · intro h n
    cases hn : finiteRun machine n finiteBlank with
    | none => exact False.elim (h ⟨n,hn⟩)
    | some c => exact ⟨c,rfl⟩

#print axioms blank_seed
#print axioms iterate_source
#print axioms source_halt_of_events
#print axioms source_termination_iff
#print axioms source_nonhalt_iff
end BB6.Agent32F418.Root
