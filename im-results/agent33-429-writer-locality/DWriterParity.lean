import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429DWriterParity
open BB6Coverage BB429PhysicalFrontier BB429OddExcursion BB429PhysicalBridge

/-- Prepared D/0 writes a marked cell to its right. Its left context begins
with zero and then an odd-length full block of ones. Synthetic input. -/
def oddD (k : Nat) : Zipper :=
  z 3 (false :: List.replicate (2*k+3) true) false []

def evenD (k : Nat) : Zipper :=
  z 3 (false :: List.replicate (2*k+2) true) false []

theorem oddD_to_prepared (k : Nat) :
    one (oddD k) = some (prepared (2*k+3)) := by rfl

theorem evenD_to_prepared (k : Nat) :
    one (evenD k) = some (prepared (2*k+2)) := by rfl

/-- Exact one-sided fatal C/01 event, for every odd prepared left block. -/
theorem oddD_fatal (k : Nat) :
    ∃ l, BB429OddExcursion.run (4*k+19) (oddD k) =
      some (z 2 l false [true]) := by
  obtain ⟨l,hl⟩ := odd_prepared_fatal k
  refine ⟨l, ?_⟩
  have ht : 4*k+19 = 1+(2*(2*k+3)+12) := by omega
  rw [ht, BB429OddExcursion.run_add]
  simp only [BB429OddExcursion.run, oddD_to_prepared, Option.bind_some]
  exact hl

/-- Even prepared left blocks reach the marker in C/1, not C/0. -/
theorem evenD_crosses (k : Nat) :
    ∃ l, BB429OddExcursion.run (4*k+8) (evenD k) =
      some (z 2 l true []) := by
  obtain ⟨l,hl⟩ := even_prepared_crosses k
  refine ⟨l, ?_⟩
  have ht : 4*k+8 = 1+(2*(2*k+2)+3) := by omega
  rw [ht, BB429OddExcursion.run_add]
  simp only [BB429OddExcursion.run, evenD_to_prepared, Option.bind_some]
  exact hl

/-- All-time parameter-uniform exact original six-state physical C/01,
    including every bit of the infinite tape, for freely prepared D inputs. -/
theorem oddD_original_fatal (k : Nat) (c : Config)
    (hc : Represents (oddD k) c) :
    ∃ c', BB6Coverage.run target429 (4*k+19) c = some c' ∧
      c'.state.val = 2 ∧ c'.tape c'.head = false ∧
      c'.tape (c'.head + 1) = true := by
  obtain ⟨l,hl⟩ := oddD_fatal k
  obtain ⟨c',hraw,hrep⟩ :=
    source_run_rep (4*k+19) (oddD k) c hc (z 2 l false [true]) hl
  refine ⟨c',hraw,?_⟩
  rcases hrep with ⟨hs,hcur,_,hright⟩
  refine ⟨hs,hcur,?_⟩
  simpa [z] using hright 0

theorem evenD_original_crosses (k : Nat) (c : Config)
    (hc : Represents (evenD k) c) :
    ∃ c', BB6Coverage.run target429 (4*k+8) c = some c' ∧
      c'.state.val = 2 ∧ c'.tape c'.head = true := by
  obtain ⟨l,hl⟩ := evenD_crosses k
  obtain ⟨c',hraw,hrep⟩ :=
    source_run_rep (4*k+8) (evenD k) c hc (z 2 l true []) hl
  refine ⟨c',hraw,?_⟩
  exact ⟨hrep.1,hrep.2.1⟩

#print axioms oddD_fatal
#print axioms evenD_crosses
#print axioms oddD_original_fatal
#print axioms evenD_original_crosses
end BB429DWriterParity
