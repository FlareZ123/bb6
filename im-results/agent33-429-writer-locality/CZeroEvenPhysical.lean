import CZeroEvenReturn
import BB429PhysicalBridge

namespace BB429CZeroEvenPhysical

open BB6Coverage BB429PhysicalFrontier BB429OddExcursion
open BB429PhysicalBridge BB429CZeroEvenReturn

/-- Full original #429 bi-infinite-tape transition: a completely marked,
    even-length left stack at a fresh C/0 frontier returns to the exact
    next C/0 stack with its right half completely blank. Every k is covered. -/
theorem even_frontier_original (k : Nat) (c : Config)
    (hc : Represents (z 2 (ones (2*k+2)) false []) c) :
    ∃ c', BB6Coverage.run target429 (4*k+11) c = some c' ∧
      Represents (z 2 (true::false::ones (2*k+4)) false []) c' := by
  exact source_run_rep _ _ _ hc _ (C0_even_to_C0 k)

/-- The contrasting odd full-block family, on an entirely represented
    original physical tape, reaches fatal C/01 for every k. -/
theorem odd_frontier_original (k : Nat) (c : Config)
    (hc : Represents (z 2 (ones (2*k+3)) false []) c) :
    ∃ l c', BB6Coverage.run target429 (4*k+20) c = some c' ∧
      Represents (z 2 l false [true]) c' := by
  obtain ⟨l,hl⟩ := C0_odd_to_fatal k
  obtain ⟨c',hraw,hrep⟩ :=
    source_run_rep (4*k+20)
      (z 2 (ones (2*k+3)) false []) c hc
      (z 2 l false [true]) hl
  exact ⟨l,c',hraw,hrep⟩

#print axioms even_frontier_original
#print axioms odd_frontier_original
end BB429CZeroEvenPhysical
