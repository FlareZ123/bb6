/-
Copyright (c) 2026 FlareZ123. All rights reserved.
Research scratch certificate against google-deepmind/cryptids commit
3647718b5df22e1a61462dec0376bd204526285a.
-/
import BusyBeaver.BB6.Halt.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH
import BusyBeaver.BB6.Halt.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA

set_option maxRecDepth 200000

open BusyBeaver.SymRunEngine

namespace BusyBeaver.SymRunAudit

abbrev SymState := SymMode × List SymTok × List SymTok

def tokFieldMax : SymTok → Nat
  | .item .zero => 0
  | .item (.run n) => n
  | .repB1 n => n
  | .rep2 n => n
  | .rep12 n => n

def listFieldMax (xs : List SymTok) : Nat :=
  xs.foldl (fun a t => max a (tokFieldMax t)) 0

def stateFieldMax (s : SymState) : Nat :=
  max (listFieldMax s.2.1) (listFieldMax s.2.2)

def stateTokenCount (s : SymState) : Nat :=
  s.2.1.length + s.2.2.length

/-- Maxima over the starting state and every state reached by up to n symbolic transitions. -/
def traceStats : Nat → SymState → Nat × Nat
  | 0, s => (stateFieldMax s, stateTokenCount s)
  | n + 1, s =>
      let tail := traceStats n (stepSym s)
      (max (stateFieldMax s) tail.1, max (stateTokenCount s) tail.2)

theorem f424_chunk00 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.initSymCyc3).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.initSymCyc3).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk01 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk4096).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk4096).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk02 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk8192).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk8192).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk03 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk12288).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk12288).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk04 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk16384).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk16384).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk05 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk20480).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk20480).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk06 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk24576).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk24576).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk07 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk28672).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk28672).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk08 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk32768).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk32768).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk09 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk36864).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk36864).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk10 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk40960).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk40960).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk11 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk45056).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk45056).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk12 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk49152).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk49152).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk13 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk53248).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk53248).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk14 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk57344).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk57344).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk15 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk61440).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk61440).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk16 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk65536).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk65536).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk17 :
    (traceStats 879 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk69632).1 < 2^203 ∧
    (traceStats 879 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.symChk69632).2 ≤ 94 := by
  decide +kernel

theorem f412_chunk00 :
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.initSymCyc3).1 < 2^69 ∧
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.initSymCyc3).2 ≤ 94 := by
  decide +kernel

theorem f412_chunk01 :
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.symChk4096).1 < 2^69 ∧
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.symChk4096).2 ≤ 94 := by
  decide +kernel

theorem f412_chunk02 :
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.symChk8192).1 < 2^69 ∧
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.symChk8192).2 ≤ 94 := by
  decide +kernel

theorem f412_chunk03 :
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.symChk12288).1 < 2^69 ∧
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.symChk12288).2 ≤ 94 := by
  decide +kernel

theorem f412_chunk04 :
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.symChk16384).1 < 2^69 ∧
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.symChk16384).2 ≤ 94 := by
  decide +kernel

theorem f412_chunk05 :
    (traceStats 903 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.symChk20480).1 < 2^69 ∧
    (traceStats 903 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.symChk20480).2 ≤ 94 := by
  decide +kernel

theorem f424_all_ranges :
  f424_chunk00 ∧ f424_chunk01 ∧ f424_chunk02 ∧ f424_chunk03 ∧
  f424_chunk04 ∧ f424_chunk05 ∧ f424_chunk06 ∧ f424_chunk07 ∧
  f424_chunk08 ∧ f424_chunk09 ∧ f424_chunk10 ∧ f424_chunk11 ∧
  f424_chunk12 ∧ f424_chunk13 ∧ f424_chunk14 ∧ f424_chunk15 ∧
  f424_chunk16 ∧ f424_chunk17 := by
  exact ⟨f424_chunk00, f424_chunk01, f424_chunk02, f424_chunk03,
    f424_chunk04, f424_chunk05, f424_chunk06, f424_chunk07,
    f424_chunk08, f424_chunk09, f424_chunk10, f424_chunk11,
    f424_chunk12, f424_chunk13, f424_chunk14, f424_chunk15,
    f424_chunk16, f424_chunk17⟩

theorem f412_all_ranges :
  f412_chunk00 ∧ f412_chunk01 ∧ f412_chunk02 ∧
  f412_chunk03 ∧ f412_chunk04 ∧ f412_chunk05 := by
  exact ⟨f412_chunk00, f412_chunk01, f412_chunk02,
    f412_chunk03, f412_chunk04, f412_chunk05⟩

#print axioms f424_all_ranges
#print axioms f412_all_ranges

end BusyBeaver.SymRunAudit
