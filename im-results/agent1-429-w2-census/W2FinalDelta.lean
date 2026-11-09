import W2OddEvents
import W4Closure
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2FinalDelta

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429W4Closure BB429W2OddEvent
open BB429PhysicalBridge BB429DeltaPhysicalBridge BB6Coverage BB429PhysicalFrontier

/-- Even v>=2 source return with exact invariant signed head displacement. -/
theorem even_w2_delta_ge_two (k : Nat) :
    runWithDelta (38*k+242) (junc 0 (2*k+2) 2) =
      some (junc 0 0 (4*k+22),-10) := by
  have hfirst := w2_to_A_boundary_delta (2*k+2)
  have hlast := even_boundary_to_canonical k
  have hparam : 2*k+2+3 = 2*k+5 := by omega
  have htime : 38*k+242 = (2*(2*k+2)+27)+(34*k+211) := by omega
  rw [htime,runWithDelta_add,hfirst]
  simp only [Option.bind_some]
  rw [hparam,hlast]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- Odd v>=3 source return with exact invariant signed head displacement. -/
theorem odd_w2_delta_ge_three (k : Nat) :
    runWithDelta (44*k+310) (junc 0 (2*k+3) 2) =
      some (junc 0 0 (4*k+28),-10) := by
  have hfirst := w2_to_A_boundary_delta (2*k+3)
  have hlast := odd_boundary_to_canonical k
  have hparam : 2*k+3+3 = 2*k+1+5 := by omega
  have htime : 44*k+310 = (2*(2*k+3)+27)+(40*k+277) := by omega
  rw [htime,runWithDelta_add,hfirst]
  simp only [Option.bind_some]
  rw [hparam,hlast]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- Every even right-two return moves the head exactly ten cells left. -/
theorem even_w2_all_delta (k : Nat) :
    runWithDelta (38*k+204) (junc 0 (2*k) 2) =
      some (junc 0 0 (4*k+18),-10) := by
  cases k with
  | zero => decide
  | succ k =>
      simpa only [show 38*(k+1)+204=38*k+242 by omega,
        show 2*(k+1)=2*k+2 by omega,
        show 4*(k+1)+18=4*k+22 by omega] using even_w2_delta_ge_two k

/-- Every odd right-two return moves the head exactly ten cells left. -/
theorem odd_w2_all_delta (k : Nat) :
    runWithDelta (44*k+266) (junc 0 (2*k+1) 2) =
      some (junc 0 0 (4*k+24),-10) := by
  cases k with
  | zero => decide
  | succ k =>
      simpa only [show 44*(k+1)+266=44*k+310 by omega,
        show 2*(k+1)+1=2*k+3 by omega,
        show 4*(k+1)+24=4*k+28 by omega] using odd_w2_delta_ge_three k

/-- The new rightmost prescribed marker is six cells farther right
    than the initial marked frontier for every even right-two return. -/
theorem even_w2_frontier_extension (k : Nat) :
    ((junc 0 0 (4*k+18)).right.length : Int) - 10 =
      ((junc 0 (2*k) 2).right.length : Int) + 6 := by
  rw [BB429W4CZeroEvents.junc_right_length,
      BB429W4CZeroEvents.junc_right_length]
  omega

/-- The new rightmost prescribed marker is ten cells farther right
    than the initial marked frontier for every odd right-two return. -/
theorem odd_w2_frontier_extension (k : Nat) :
    ((junc 0 0 (4*k+24)).right.length : Int) - 10 =
      ((junc 0 (2*k+1) 2).right.length : Int) + 10 := by
  rw [BB429W4CZeroEvents.junc_right_length,
      BB429W4CZeroEvents.junc_right_length]
  omega

/-- Full physical original-table right-two even return with exact
    physical head displacement, for arbitrary represented tapes. -/
theorem physical_even_w2_delta (k : Nat) (c : Config)
    (hrep : Represents (junc 0 (2*k) 2) c) :
    ∃ c', BB6Coverage.run target429 (38*k+204) c = some c' ∧
      Represents (junc 0 0 (4*k+18)) c' ∧ c'.head = c.head - 10 := by
  obtain ⟨c',hr,hs,hd⟩ :=
    source_runWithDelta_rep (38*k+204) (junc 0 (2*k) 2) c hrep
      (junc 0 0 (4*k+18)) (-10) (even_w2_all_delta k)
  refine ⟨c',hr,hs,?_⟩
  omega

/-- Full physical original-table right-two odd return with exact
    physical head displacement, for arbitrary represented tapes. -/
theorem physical_odd_w2_delta (k : Nat) (c : Config)
    (hrep : Represents (junc 0 (2*k+1) 2) c) :
    ∃ c', BB6Coverage.run target429 (44*k+266) c = some c' ∧
      Represents (junc 0 0 (4*k+24)) c' ∧ c'.head = c.head - 10 := by
  obtain ⟨c',hr,hs,hd⟩ :=
    source_runWithDelta_rep (44*k+266) (junc 0 (2*k+1) 2) c hrep
      (junc 0 0 (4*k+24)) (-10) (odd_w2_all_delta k)
  refine ⟨c',hr,hs,?_⟩
  omega

#print axioms even_w2_all_delta
#print axioms odd_w2_all_delta
#print axioms even_w2_frontier_extension
#print axioms odd_w2_frontier_extension
#print axioms physical_even_w2_delta
#print axioms physical_odd_w2_delta

end BB429W2FinalDelta
