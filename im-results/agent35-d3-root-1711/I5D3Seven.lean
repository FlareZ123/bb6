import I5D3Continuation
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 180000
set_option maxHeartbeats 0

namespace BB6.Agent35I5Seven

open CryptidBoundary
open BB6.BoundaryPadding
open BB6.Agent19.Physical
open BB6.Agent35I5Continuation

/-- A 99-return regular stretch, previously omitted, reaches q=8
    before the conjectured 2511-return stretch. -/
def raw5a : Option DRegular.L := BB6.DRegularFast.fastRun 99 s4
def t5a : Nat := ((raw5a.getD (⟨0,0,0⟩ : DRegular.L)).a-10)/9
def e5a : DRegular.L := ⟨9*t5a+10,8,1⟩
theorem raw5a_data : raw5a = some e5a := by decide

def s5a : DRegular.L := q8Out t5a

/-- With the missing q=8 return performed, the 2511-return
    q=7 checkpoint is present exactly as the earlier model predicted. -/
def raw5b : Option DRegular.L := BB6.DRegularFast.fastRun 2511 s5a
def t5b : Nat := ((raw5b.getD (⟨0,0,0⟩ : DRegular.L)).a-10)/9
def e5b : DRegular.L := ⟨9*t5b+10,7,1⟩
theorem raw5b_data : raw5b = some e5b := by decide

def s5b : DRegular.L := q7AOut t5b

/-- The following q=7 exceptional event has the exact
    t ≡ 4 (mod 27) source-return guard. -/
def raw6 : Option DRegular.L := BB6.DRegularFast.fastRun 2138 s5b
def t6 : Nat := ((raw6.getD (⟨0,0,0⟩ : DRegular.L)).a-7)/9
def e6 : DRegular.L := ⟨9*t6+7,7,1⟩
theorem raw6_data : raw6 = some e6 ∧ t6 % 27 = 4 := by decide

def s6 : DRegular.L := q7EscapeOut t6

def regCost5a : Nat := DRegular.accumulated 99 s4
def regCost5b : Nat := DRegular.accumulated 2511 s5a
def regCost6 : Nat := DRegular.accumulated 2138 s5b

private theorem reg5a_obs :
    ObsEq (run regCost5a (DRegularSource.sourceSection s4))
      (DRegularSource.sourceSection e5a) := by
  have hc : DRegular.Canon s4 := by
    constructor
    · simp [s4] <;> omega
    · simp [s4]
  exact regular_source 99 s4 e5a hc raw5a_data

private theorem reg5b_obs :
    ObsEq (run regCost5b (DRegularSource.sourceSection s5a))
      (DRegularSource.sourceSection e5b) := by
  have hc : DRegular.Canon s5a := by
    constructor
    · simp [s5a,q8Out] <;> omega
    · simp [s5a,q8Out]
  exact regular_source 2511 s5a e5b hc raw5b_data

private theorem reg6_obs :
    ObsEq (run regCost6 (DRegularSource.sourceSection s5b))
      (DRegularSource.sourceSection e6) := by
  have hc : DRegular.Canon s5b := by
    constructor
    · simp [s5b,q7AOut] <;> omega
    · simp [s5b,q7AOut]
  exact regular_source 2138 s5b e6 hc raw6_data.1

def tailCost : Nat :=
  regCost5a + q8Cost t5a +
  regCost5b + q7ACost t5b +
  regCost6 + q7EscapeCost t6

/-- Original physical D3 source path: the 99-return correction followed
    by the already authenticated E/A and E/E/E/E/A macros. -/
theorem tail_source :
    ObsEq (run tailCost (DRegularSource.sourceSection s4))
      (DRegularSource.sourceSection s6) := by
  have h01 := source_chain regCost5a (q8Cost t5a)
    (DRegularSource.sourceSection s4)
    (DRegularSource.sourceSection e5a)
    (DRegularSource.sourceSection s5a)
    reg5a_obs (q8_rejoin t5a)
  have h02 := source_chain
    (regCost5a+q8Cost t5a) regCost5b
    (DRegularSource.sourceSection s4)
    (DRegularSource.sourceSection s5a)
    (DRegularSource.sourceSection e5b)
    h01 reg5b_obs
  have h03 := source_chain
    (regCost5a+q8Cost t5a+regCost5b) (q7ACost t5b)
    (DRegularSource.sourceSection s4)
    (DRegularSource.sourceSection e5b)
    (DRegularSource.sourceSection s5b)
    h02 (q7A_rejoin t5b)
  have h04 := source_chain
    (regCost5a+q8Cost t5a+regCost5b+q7ACost t5b) regCost6
    (DRegularSource.sourceSection s4)
    (DRegularSource.sourceSection s5b)
    (DRegularSource.sourceSection e6)
    h03 reg6_obs
  have h05 := source_chain
    (regCost5a+q8Cost t5a+regCost5b+q7ACost t5b+regCost6)
    (q7EscapeCost t6)
    (DRegularSource.sourceSection s4)
    (DRegularSource.sourceSection e6)
    (DRegularSource.sourceSection s6)
    h04 (q7_escape_rejoin t6 raw6_data.2)
  simpa [tailCost,Nat.add_assoc] using h05

def sourceElapsedSeven : Nat := sourceElapsedFinal + tailCost
def horizonSeven : Nat := 15 + sourceElapsedSeven

/-- The authentic blank-root D3 path reaches a live F/0 source section
    after the 1711 initial returns, original exceptional reentry, four
    initial long stretches, and these three additional stretches. -/
theorem root_source_seven :
    ObsEq (run sourceElapsedSeven (sourceUnary 5))
      (DRegularSource.sourceSection s6) := by
  exact source_chain sourceElapsedFinal tailCost
    (sourceUnary 5)
    (DRegularSource.sourceSection s4)
    (DRegularSource.sourceSection s6)
    root_source tail_source

theorem final_next_live_seven :
    (run (sourceElapsedSeven+1) (sourceUnary 5)).st ≠ 6 := by
  have hObs := source_congr 1 root_source_seven
  have hstate := obs_state hObs
  have hrun :
      run (sourceElapsedSeven+1) (sourceUnary 5) =
        run 1 (run sourceElapsedSeven (sourceUnary 5)) := by
    exact CryptidBoundary.run_add _ _ _
  rw [hrun]
  intro hbad
  have hright :
      (run 1 (DRegularSource.sourceSection s6)).st ≠ 6 := by
    simp [CryptidBoundary.run,CryptidBoundary.step,
      DRegularSource.sourceSection,CryptidBoundary.init,goL,
      s6,q7EscapeOut]
  exact hright (hstate.symm.trans hbad)

theorem no_frozen_through_seven (n : Nat)
    (hn : n ≤ sourceElapsedSeven+1) :
    (run n (sourceUnary 5)).st ≠ 6 :=
  no_frozen_before_live_endpoint (sourceUnary 5)
    (sourceElapsedSeven+1) n hn final_next_live_seven

/-- Corrected authentic D3 root cannot halt at any primitive time up to
    the 7th additional exceptional reentry after the original 1711 section
    prefix; this is finite nonhalting, NOT eventual nonhalting. -/
theorem parsed_D3_no_halt_through_seven (n : Nat)
    (hn : n ≤ horizonSeven) :
    ¬ BB6.Portfolio.haltsAt
      (BB6.Portfolio.parseRLE BB6.Portfolio.rleD3)
      (0 : BB6.Portfolio.State) n := by
  by_cases hlt : n < 15
  · intro hh
    have hh' : BB6.Portfolio.haltsAt BB6.Portfolio.D3
        (0 : BB6.Portfolio.State) n := by
      simpa only [BB6.Portfolio.parsed_D3_eq] using hh
    have hd0 := BB6.Portfolio.D3_exact_halt_time n
    have hp := BB6.Portfolio.no_halt_before_prefix
      BB6.Portfolio.D0 (BB6.Portfolio.blank (1 : BB6.Portfolio.State))
      (BB6.Portfolio.F0Pure 5 (-3)) 15 n
      BB6.Portfolio.blank_root_B_to_I5 (hd0.mp hh')
    omega
  · have hge : 15 ≤ n := by omega
    let k := n-15
    have hk : k ≤ sourceElapsedSeven := by
      dsimp [k,horizonSeven,sourceElapsedSeven] at *
      omega
    have htime : 15+k=n := by omega
    intro hh
    have hh' : BB6.Portfolio.haltsAt
        (BB6.Portfolio.parseRLE BB6.Portfolio.rleD3)
        (0 : BB6.Portfolio.State) (15+k) := by
      simpa [htime] using hh
    have hfrozen :=
      (BB6.Agent19.Physical.parsed_D3_exact_source_time k).mp hh'
    exact (no_frozen_through_seven (k+1) (by omega)) hfrozen.2

theorem horizonSeven_ge_old : horizonFinal ≤ horizonSeven := by
  dsimp [horizonFinal,horizonSeven,sourceElapsedSeven]
  omega

theorem horizonSeven_ge_10pow1458 : 10^1458 ≤ horizonSeven :=
  Nat.le_trans horizonFinal_ge_10pow1458 horizonSeven_ge_old

#print axioms raw5a_data
#print axioms raw5b_data
#print axioms raw6_data
#print axioms tail_source
#print axioms root_source_seven
#print axioms parsed_D3_no_halt_through_seven
#print axioms horizonSeven_ge_10pow1458

end BB6.Agent35I5Seven
