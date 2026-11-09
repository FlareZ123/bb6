import W2BoundaryHeadMax
import W2Junc2GateMax
import W2OddJuncMax
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2FullHeadMax

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4HeadMax BB429W2BoundaryHeadMax
open BB429W2Junc2GateMax BB429W2OddJuncMax

/-- Kernel-decided smallest even right-two return, including every
    head prefix and its sharp global right-hand record. -/
theorem w2_even_base_max :
  runWithMax 204 (junc 0 0 2) =
    some (junc 0 0 18, -10,11) := by decide

/-- Kernel-decided smallest odd right-two return. -/
theorem w2_odd_base_max :
  runWithMax 266 (junc 0 1 2) =
    some (junc 0 0 24, -10,17) := by decide

/-- Every positive even middle parameter has a complete original-table
    head maximum. The terminal C/0 step is one cell below this record. -/
theorem w2_even_inductive_max (k : Nat) :
    runWithMax (38*k+242) (junc 0 (2*k+2) 2) =
      some (junc 0 0 (4*k+22), -10, ((4*k+15 : Nat) : Int)) := by
  have hprep := junc0_w2_to_boundary_max (2*k+2)
  have hmid := even_boundary_to_junc2_max k
  have hlast := junc2_w1_full_max (2*k+6) (by omega)
  have hparam : (2*k+2)+3=2*k+5 := by omega
  rw [hparam] at hprep
  have hlen1 : 2*(2*k+2)+27=4*k+31 := by omega
  rw [hlen1] at hprep
  have hlen3 : 8*(2*k+6)+54=16*k+102 := by omega
  rw [hlen3] at hlast
  have hterm : 2*(2*k+6)+10=4*k+22 := by omega
  rw [hterm] at hlast
  rw [show 38*k+242=(4*k+31)+((18*k+109)+(16*k+102)) by omega,
    runWithMax_add,hprep]
  simp only [Option.bind_some]
  rw [runWithMax_add,hmid]
  simp only [Option.bind_some]
  rw [hlast]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- All positive odd middle parameters admit the analogous sharp head
    maximum without truncating the tape or the number of alternations. -/
theorem w2_odd_inductive_max (k : Nat) :
    runWithMax (44*k+310) (junc 0 (2*k+3) 2) =
      some (junc 0 0 (4*k+28), -10, ((4*k+21 : Nat) : Int)) := by
  have hprep := junc0_w2_to_boundary_max (2*k+3)
  have hmid := odd_boundary_to_junc0_max k
  have hlast := junc0_odd_w1_full_max (k+3)
  have hparam : (2*k+3)+3=2*k+6 := by omega
  rw [hparam] at hprep
  have hlen1 : 2*(2*k+3)+27=4*k+33 := by omega
  rw [hlen1] at hprep
  have hlen3 : 22*(k+3)+126=22*k+192 := by omega
  rw [hlen3] at hlast
  have hterm : 4*(k+3)+16=4*k+28 := by omega
  have hinputlast : 2*(k+3)+1=2*k+7 := by omega
  rw [hterm,hinputlast] at hlast
  rw [show 44*k+310=(4*k+33)+((18*k+85)+(22*k+192)) by omega,
    runWithMax_add,hprep]
  simp only [Option.bind_some]
  rw [runWithMax_add,hmid]
  simp only [Option.bind_some]
  rw [hlast]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- EVERY even-indexed right-two Junc has an exact complete-excursion
    primitive-step maximum, including the exceptional zero index. -/
theorem w2_all_even_max (k : Nat) :
  runWithMax (38*k+204) (junc 0 (2*k) 2) =
    some (junc 0 0 (4*k+18), -10, ((4*k+11 : Nat) : Int)) := by
  cases k with
  | zero => exact w2_even_base_max
  | succ k =>
      simpa only [show 38*(k+1)+204=38*k+242 by omega,
        show 2*(k+1)=2*k+2 by omega,
        show 4*(k+1)+18=4*k+22 by omega,
        show 4*(k+1)+11=4*k+15 by omega] using
        w2_even_inductive_max k

/-- EVERY odd-indexed right-two Junc has an exact complete-excursion
    primitive-step maximum, including the exceptional index one. -/
theorem w2_all_odd_max (k : Nat) :
  runWithMax (44*k+266) (junc 0 (2*k+1) 2) =
    some (junc 0 0 (4*k+24), -10, ((4*k+17 : Nat) : Int)) := by
  cases k with
  | zero => exact w2_odd_base_max
  | succ k =>
      simpa only [show 44*(k+1)+266=44*k+310 by omega,
        show 2*(k+1)+1=2*k+3 by omega,
        show 4*(k+1)+24=4*k+28 by omega,
        show 4*(k+1)+17=4*k+21 by omega] using
        w2_odd_inductive_max k

#print axioms w2_even_base_max
#print axioms w2_odd_base_max
#print axioms w2_even_inductive_max
#print axioms w2_odd_inductive_max
#print axioms w2_all_even_max
#print axioms w2_all_odd_max

end BB429W2FullHeadMax
