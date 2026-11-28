import I5D3Seven
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 180000
set_option maxHeartbeats 0

namespace BB6.Agent35I5Eleven
open CryptidBoundary
open BB6.BoundaryPadding
open BB6.Agent19.Physical
open BB6.Agent35I5Continuation
open BB6.Agent35I5Seven

/-- Four subsequent exact model exits, each witnessed by a kernel
    reduction and individually lifted to original-source macro segments. -/

def raw8 : Option DRegular.L := BB6.DRegularFast.fastRun 113 s6
def t8 : Nat := ((raw8.getD (⟨0,0,0⟩ : DRegular.L)).a-4)/9
def e8 : DRegular.L := ⟨9*t8+4,4,1⟩
theorem raw8_data : raw8 = some e8 := by decide
def s8 : DRegular.L := ⟨64*t8+25,1,5⟩

def raw9 : Option DRegular.L := BB6.DRegularFast.fastRun 2393 s8
def t9 : Nat := ((raw9.getD (⟨0,0,0⟩ : DRegular.L)).a-4)/9
def e9 : DRegular.L := ⟨9*t9+4,8,1⟩
theorem raw9_data : raw9 = some e9 := by decide
def s9 : DRegular.L := ⟨64*t9+33,1,5⟩

def raw10 : Option DRegular.L := BB6.DRegularFast.fastRun 604 s9
def t10 : Nat := ((raw10.getD (⟨0,0,0⟩ : DRegular.L)).a-10)/9
def e10 : DRegular.L := ⟨9*t10+10,5,1⟩
theorem raw10_data : raw10 = some e10 := by decide
def s10 : DRegular.L := q5EAOut t10

def raw11 : Option DRegular.L := BB6.DRegularFast.fastRun 5507 s10
def t11 : Nat := ((raw11.getD (⟨0,0,0⟩ : DRegular.L)).a-7)/9
def e11 : DRegular.L := ⟨9*t11+7,5,1⟩
theorem raw11_data : raw11 = some e11 ∧ t11 % 9 = 8 := by decide
def s11 : DRegular.L := q5FourthOut t11

def q4BCost (t : Nat) : Nat :=
  BB6.Agent32EAll.duration (3*t) 3 +
    BB6.Agent25BGeneral.bCost t
def q8BCost (t : Nat) : Nat :=
  BB6.Agent32EAll.duration (3*t) 7 +
    BB6.Agent25BGeneral.bCost t

private theorem q4B_obs (t : Nat) :
    ObsEq
      (run (q4BCost t) (DRegularSource.sourceSection ⟨9*t+4,4,1⟩))
      (DRegularSource.sourceSection ⟨64*t+25,1,5⟩) := by
  simpa [q4BCost] using
    (BB6.Agent25BGeneral.exceptional_EB_general t 2)

private theorem q8B_obs (t : Nat) :
    ObsEq
      (run (q8BCost t) (DRegularSource.sourceSection ⟨9*t+4,8,1⟩))
      (DRegularSource.sourceSection ⟨64*t+33,1,5⟩) := by
  simpa [q8BCost] using
    (BB6.Agent25BGeneral.exceptional_EB_general t 6)

def regCost8 : Nat := DRegular.accumulated 113 s6
def regCost9 : Nat := DRegular.accumulated 2393 s8
def regCost10 : Nat := DRegular.accumulated 604 s9
def regCost11 : Nat := DRegular.accumulated 5507 s10

private theorem reg8_obs :
    ObsEq (run regCost8 (DRegularSource.sourceSection s6))
      (DRegularSource.sourceSection e8) := by
  have hc : DRegular.Canon s6 := by
    constructor
    · simp [s6,q7EscapeOut,q7KA] <;> omega
    · simp [s6,q7EscapeOut]
  exact regular_source 113 s6 e8 hc raw8_data

private theorem reg9_obs :
    ObsEq (run regCost9 (DRegularSource.sourceSection s8))
      (DRegularSource.sourceSection e9) := by
  have hc : DRegular.Canon s8 := by
    constructor
    · simp [s8] <;> omega
    · simp [s8]
  exact regular_source 2393 s8 e9 hc raw9_data

private theorem reg10_obs :
    ObsEq (run regCost10 (DRegularSource.sourceSection s9))
      (DRegularSource.sourceSection e10) := by
  have hc : DRegular.Canon s9 := by
    constructor
    · simp [s9] <;> omega
    · simp [s9]
  exact regular_source 604 s9 e10 hc raw10_data

private theorem reg11_obs :
    ObsEq (run regCost11 (DRegularSource.sourceSection s10))
      (DRegularSource.sourceSection e11) := by
  have hc : DRegular.Canon s10 := by
    constructor
    · simp [s10,q5EAOut] <;> omega
    · simp [s10,q5EAOut]
  exact regular_source 5507 s10 e11 hc raw11_data.1

def tailElevenCost : Nat :=
  regCost8 + q4BCost t8 +
  regCost9 + q8BCost t9 +
  regCost10 + q5EACost t10 +
  regCost11 + q5FourthCost t11

/-- Four further complete, designated source returns on the actual
    D3 blank-root trajectory, including an E/E/B/A q5 branch. -/
theorem tail_eleven_source :
    ObsEq (run tailElevenCost (DRegularSource.sourceSection s6))
      (DRegularSource.sourceSection s11) := by
  have h01 := source_chain regCost8 (q4BCost t8)
    (DRegularSource.sourceSection s6)
    (DRegularSource.sourceSection e8)
    (DRegularSource.sourceSection s8)
    reg8_obs (q4B_obs t8)
  have h02 := source_chain
    (regCost8+q4BCost t8) regCost9
    (DRegularSource.sourceSection s6)
    (DRegularSource.sourceSection s8)
    (DRegularSource.sourceSection e9)
    h01 reg9_obs
  have h03 := source_chain
    (regCost8+q4BCost t8+regCost9) (q8BCost t9)
    (DRegularSource.sourceSection s6)
    (DRegularSource.sourceSection e9)
    (DRegularSource.sourceSection s9)
    h02 (q8B_obs t9)
  have h04 := source_chain
    (regCost8+q4BCost t8+regCost9+q8BCost t9) regCost10
    (DRegularSource.sourceSection s6)
    (DRegularSource.sourceSection s9)
    (DRegularSource.sourceSection e10)
    h03 reg10_obs
  have h05 := source_chain
    (regCost8+q4BCost t8+regCost9+q8BCost t9+regCost10) (q5EACost t10)
    (DRegularSource.sourceSection s6)
    (DRegularSource.sourceSection e10)
    (DRegularSource.sourceSection s10)
    h04 (q5EA_rejoin t10)
  have h06 := source_chain
    (regCost8+q4BCost t8+regCost9+q8BCost t9+
      regCost10+q5EACost t10) regCost11
    (DRegularSource.sourceSection s6)
    (DRegularSource.sourceSection s10)
    (DRegularSource.sourceSection e11)
    h05 reg11_obs
  have h07 := source_chain
    (regCost8+q4BCost t8+regCost9+q8BCost t9+
      regCost10+q5EACost t10+regCost11) (q5FourthCost t11)
    (DRegularSource.sourceSection s6)
    (DRegularSource.sourceSection e11)
    (DRegularSource.sourceSection s11)
    h06 (q5_fourth_source t11 raw11_data.2)
  simpa [tailElevenCost,Nat.add_assoc] using h07

def sourceElapsedEleven : Nat := sourceElapsedSeven + tailElevenCost
def horizonEleven : Nat := 15 + sourceElapsedEleven

theorem root_source_eleven :
    ObsEq (run sourceElapsedEleven (sourceUnary 5))
      (DRegularSource.sourceSection s11) :=
  source_chain sourceElapsedSeven tailElevenCost
    (sourceUnary 5)
    (DRegularSource.sourceSection s6)
    (DRegularSource.sourceSection s11)
    root_source_seven tail_eleven_source

theorem final_next_live_eleven :
    (run (sourceElapsedEleven+1) (sourceUnary 5)).st ≠ 6 := by
  have hObs := source_congr 1 root_source_eleven
  have hstate := obs_state hObs
  have hrun :
      run (sourceElapsedEleven+1) (sourceUnary 5) =
        run 1 (run sourceElapsedEleven (sourceUnary 5)) := by
    exact CryptidBoundary.run_add _ _ _
  rw [hrun]
  intro hbad
  have hright :
      (run 1 (DRegularSource.sourceSection s11)).st ≠ 6 := by
    simp [CryptidBoundary.run,CryptidBoundary.step,
      DRegularSource.sourceSection,CryptidBoundary.init,goL,
      s11,q5FourthOut]
  exact hright (hstate.symm.trans hbad)

theorem no_frozen_through_eleven (n : Nat)
    (hn : n ≤ sourceElapsedEleven+1) :
    (run n (sourceUnary 5)).st ≠ 6 :=
  no_frozen_before_live_endpoint (sourceUnary 5)
    (sourceElapsedEleven+1) n hn final_next_live_eleven

theorem parsed_D3_no_halt_through_eleven (n : Nat)
    (hn : n ≤ horizonEleven) :
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
    have hk : k ≤ sourceElapsedEleven := by
      dsimp [k,horizonEleven,sourceElapsedEleven] at *
      omega
    have htime : 15+k=n := by omega
    intro hh
    have hh' : BB6.Portfolio.haltsAt
        (BB6.Portfolio.parseRLE BB6.Portfolio.rleD3)
        (0 : BB6.Portfolio.State) (15+k) := by
      simpa [htime] using hh
    have hfrozen :=
      (BB6.Agent19.Physical.parsed_D3_exact_source_time k).mp hh'
    exact (no_frozen_through_eleven (k+1) (by omega)) hfrozen.2

theorem horizonEleven_ge_old : horizonSeven ≤ horizonEleven := by
  dsimp [horizonSeven,horizonEleven,sourceElapsedEleven]
  omega

theorem horizonEleven_ge_10pow1458 : 10^1458 ≤ horizonEleven :=
  Nat.le_trans horizonSeven_ge_10pow1458 horizonEleven_ge_old

#print axioms raw8_data
#print axioms raw9_data
#print axioms raw10_data
#print axioms raw11_data
#print axioms q4B_obs
#print axioms q8B_obs
#print axioms tail_eleven_source
#print axioms root_source_eleven
#print axioms parsed_D3_no_halt_through_eleven
#print axioms horizonEleven_ge_10pow1458

end BB6.Agent35I5Eleven
