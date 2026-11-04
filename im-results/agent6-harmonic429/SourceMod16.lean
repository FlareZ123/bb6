import SourceLadder
import BB429Extra11
import Lean.Elab.Tactic.Omega

namespace BB429SourceMod16
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

theorem source_run_to_local (n u w : Nat)
    (h : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w)) :
    BB429.run n (0,0) = some (u,w) := by
  have heq := BB429SourceLadder.source_run_eq n (0,0)
  have hh : (BB429.run n (0,0)).map BB429SourceLadder.lift =
      some (.J u w) := by
    rw [← heq]
    simpa [highLevelStart] using h
  cases hr : BB429.run n (0,0) with
  | none => simp [hr] at hh
  | some s =>
    obtain ⟨a,b⟩ := s
    simp only [hr, Option.map_some, BB429SourceLadder.lift] at hh
    have he : a=u ∧ b=w := by
      simpa only [Option.some.injEq, HighLevelState.J.injEq] using hh
    rcases he with ⟨rfl,rfl⟩
    exact hr

theorem source_next_none_to_local (u w : Nat)
    (h : highLevelNext (.J u w) = none) :
    BB429.next (u,w) = none := by
  have hh := BB429SourceLadder.source_step_eq u w
  rw [h] at hh
  cases hs : BB429.next (u,w) with
  | none => exact hs
  | some s => simp [hs] at hh

/-- All genuine accelerated blank-origin halting sites lie in five u-residue
    classes modulo 16. This is a necessary condition, not a nonhalting proof. -/
theorem source_halting_mod16 (n u w : Nat)
    (h : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%16=1 ∨ u%16=3 ∨ u%16=5 ∨ u%16=9 ∨ u%16=13 := by
  exact BB429Extra11.blank_halting_mod16 n u w
    (source_run_to_local n u w h) (source_next_none_to_local u w hn)

#print axioms source_halting_mod16
end BB429SourceMod16
