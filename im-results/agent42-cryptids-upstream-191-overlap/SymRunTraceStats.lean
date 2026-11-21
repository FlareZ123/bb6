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
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.initSymCyc3).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.initSymCyc3).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk01 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk4096).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk4096).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk02 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk8192).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk8192).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk03 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk12288).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk12288).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk04 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk16384).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk16384).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk05 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk20480).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk20480).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk06 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk24576).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk24576).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk07 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk28672).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk28672).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk08 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk32768).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk32768).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk09 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk36864).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk36864).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk10 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk40960).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk40960).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk11 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk45056).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk45056).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk12 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk49152).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk49152).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk13 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk53248).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk53248).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk14 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk57344).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk57344).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk15 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk61440).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk61440).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk16 :
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk65536).1 < 2^203 ∧
    (traceStats 4096 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk65536).2 ≤ 94 := by
  decide +kernel

theorem f424_chunk17 :
    (traceStats 879 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk69632).1 < 2^203 ∧
    (traceStats 879 BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.symChk69632).2 ≤ 94 := by
  decide +kernel

theorem f412_chunk00 :
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.initSymCyc3).1 < 2^69 ∧
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.initSymCyc3).2 ≤ 94 := by
  decide +kernel

theorem f412_chunk01 :
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.symChk4096).1 < 2^69 ∧
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.symChk4096).2 ≤ 94 := by
  decide +kernel

theorem f412_chunk02 :
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.symChk8192).1 < 2^69 ∧
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.symChk8192).2 ≤ 94 := by
  decide +kernel

theorem f412_chunk03 :
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.symChk12288).1 < 2^69 ∧
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.symChk12288).2 ≤ 94 := by
  decide +kernel

theorem f412_chunk04 :
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.symChk16384).1 < 2^69 ∧
    (traceStats 4096 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.symChk16384).2 ≤ 94 := by
  decide +kernel

theorem f412_chunk05 :
    (traceStats 903 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.symChk20480).1 < 2^69 ∧
    (traceStats 903 BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.symChk20480).2 ≤ 94 := by
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

theorem f424_checkpoint_chain :
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk1 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk2 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk3 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk4 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk5 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk6 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk7 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk8 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk9 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk10 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk11 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk12 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk13 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk14 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk15 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk16 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk17 ∧
  BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk18 := by
  exact ⟨BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk1,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk2,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk3,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk4,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk5,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk6,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk7,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk8,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk9,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk10,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk11,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk12,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk13,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk14,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk15,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk16,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk17,
    BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution.sym_chk18⟩

theorem f412_checkpoint_chain :
  BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.sym_chk1 ∧
  BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.sym_chk2 ∧
  BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.sym_chk3 ∧
  BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.sym_chk4 ∧
  BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.sym_chk5 ∧
  BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.sym_chk6 := by
  exact ⟨BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.sym_chk1,
    BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.sym_chk2,
    BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.sym_chk3,
    BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.sym_chk4,
    BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.sym_chk5,
    BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.sym_chk6⟩

theorem f424_trace_range_certificate :
  f424_all_ranges ∧ f424_checkpoint_chain :=
  ⟨f424_all_ranges, f424_checkpoint_chain⟩

theorem f412_trace_range_certificate :
  f412_all_ranges ∧ f412_checkpoint_chain :=
  ⟨f412_all_ranges, f412_checkpoint_chain⟩

#print axioms f424_trace_range_certificate
#print axioms f412_trace_range_certificate


/-!
## One-step symbolic field bound

The pure symbolic engine can increase the largest numeric run/repeat field
by at most one per transition.  The proof decomposes the BB/DL/CB cases;
the only counter-incrementing CB repeat cases are paid for by the opposite
side's existing repeat counter.
-/

@[simp] theorem listFieldMax_nil : listFieldMax [] = 0 := rfl

theorem foldl_max_acc (xs : List SymTok) (a : Nat) :
    xs.foldl (fun b t => max b (tokFieldMax t)) a =
      max a (xs.foldl (fun b t => max b (tokFieldMax t)) 0) := by
  induction xs generalizing a with
  | nil => simp
  | cons t xs ih =>
      simp only [List.foldl_cons]
      rw [ih (max a (tokFieldMax t))]
      rw [ih (max 0 (tokFieldMax t))]
      omega

theorem listFieldMax_append (xs ys : List SymTok) :
    listFieldMax (xs ++ ys) = max (listFieldMax xs) (listFieldMax ys) := by
  simp only [listFieldMax, List.foldl_append]
  exact foldl_max_acc ys (xs.foldl (fun a t => max a (tokFieldMax t)) 0)

theorem listFieldMax_suffix (pre xs : List SymTok) :
    listFieldMax xs ≤ listFieldMax (pre ++ xs) := by
  rw [listFieldMax_append]
  exact Nat.le_max_right _ _

@[simp] theorem listFieldMax_cons (t : SymTok) (xs : List SymTok) :
    listFieldMax (t :: xs) = max (tokFieldMax t) (listFieldMax xs) := by
  simpa [listFieldMax] using (listFieldMax_append [t] xs)

theorem bumpSymL_field_growth (xs : List SymTok) :
    listFieldMax (bumpSymL xs) ≤ listFieldMax xs + 1 := by
  induction xs with
  | nil => simp [bumpSymL, listFieldMax, tokFieldMax]
  | cons t xs ih =>
    cases t with
    | item x =>
      cases x with
      | zero => simp [bumpSymL, listFieldMax_cons, tokFieldMax]
      | run d => simp [bumpSymL, listFieldMax_cons, tokFieldMax]; omega
    | repB1 k =>
      cases k with
      | zero => simpa [bumpSymL, listFieldMax_cons, tokFieldMax] using ih
      | succ k =>
        cases k with
        | zero => simp [bumpSymL, listFieldMax_cons, tokFieldMax]; omega
        | succ k => simp [bumpSymL, listFieldMax_cons, tokFieldMax]; omega
    | rep2 p =>
      cases p with
      | zero => simpa [bumpSymL, listFieldMax_cons, tokFieldMax] using ih
      | succ p => simp [bumpSymL, listFieldMax_cons, tokFieldMax]; omega
    | rep12 m =>
      cases m with
      | zero => simpa [bumpSymL, listFieldMax_cons, tokFieldMax] using ih
      | succ m => simp [bumpSymL, listFieldMax_cons, tokFieldMax]; omega

theorem bumpSymR_field_growth (xs : List SymTok) :
    listFieldMax (bumpSymR xs) ≤ listFieldMax xs + 1 := by
  induction xs with
  | nil => simp [bumpSymR, listFieldMax, tokFieldMax]
  | cons t xs ih =>
    cases t with
    | item x =>
      cases x with
      | zero => simp [bumpSymR, listFieldMax_cons, tokFieldMax]
      | run d => simp [bumpSymR, listFieldMax_cons, tokFieldMax]; omega
    | repB1 k =>
      cases k with
      | zero => simpa [bumpSymR, listFieldMax_cons, tokFieldMax] using ih
      | succ k =>
        cases k with
        | zero => simp [bumpSymR, listFieldMax_cons, tokFieldMax]; omega
        | succ k => simp [bumpSymR, listFieldMax_cons, tokFieldMax]; omega
    | rep2 p =>
      cases p with
      | zero => simpa [bumpSymR, listFieldMax_cons, tokFieldMax] using ih
      | succ p => simp [bumpSymR, listFieldMax_cons, tokFieldMax]; omega
    | rep12 m =>
      cases m with
      | zero => simpa [bumpSymR, listFieldMax_cons, tokFieldMax] using ih
      | succ m => simp [bumpSymR, listFieldMax_cons, tokFieldMax]; omega

theorem prependZeroSym_field_max (n : Nat) (xs : List SymTok) :
    listFieldMax (prependZeroSym n xs) = listFieldMax xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [prependZeroSym, ih]
    simp [listFieldMax_cons, tokFieldMax]

theorem max_le_max_plus_one {a b a' b' : Nat}
    (ha : a' ≤ a+1) (hb : b' ≤ b+1) : max a' b' ≤ max a b + 1 := by omega

theorem max_left_bump_le (l r r' : Nat) (hr : r' ≤ r+1) :
    max l r' ≤ max l r + 1 := by
  apply Nat.max_le.mpr
  constructor
  · exact Nat.le_trans (Nat.le_max_left l r) (Nat.le_add_right (max l r) 1)
  · exact Nat.le_trans hr (Nat.add_le_add_right (Nat.le_max_right l r) 1)

theorem stepElemBB_field_growth (L R : List SymTok) :
    stateFieldMax (stepElemBB L R) ≤ stateFieldMax (.BB, L, R) + 1 := by
  have hR := bumpSymR_field_growth R
  cases L with
  | nil => simpa [stepElemBB, stateFieldMax, strictList_eq] using hR
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero => simp [stepElemBB, stateFieldMax, listFieldMax_cons, tokFieldMax, strictList_eq] <;> omega
      | run d =>
        cases d with
        | zero => simp [stepElemBB, stateFieldMax, listFieldMax_cons, tokFieldMax]
        | succ d =>
          cases d with
          | zero =>
            have hm := max_left_bump_le (listFieldMax L1) (listFieldMax R) (listFieldMax (bumpSymR R)) hR
            simp [stepElemBB, stateFieldMax, listFieldMax_cons, tokFieldMax]
            exact Nat.le_trans hm (Nat.add_le_add_right (Nat.le_max_right 1 (max (listFieldMax L1) (listFieldMax R))) 1)
          | succ d =>
            cases d with
            | zero =>
              have hm := max_left_bump_le (listFieldMax L1) (listFieldMax R) (listFieldMax (bumpSymR R)) hR
              simp [stepElemBB, stateFieldMax, listFieldMax_cons, tokFieldMax]
              exact Nat.le_trans hm (Nat.add_le_add_right (Nat.le_max_right 2 (max (listFieldMax L1) (listFieldMax R))) 1)
            | succ d =>
              cases d with
              | zero => simp [stepElemBB, stateFieldMax, listFieldMax_cons, tokFieldMax] <;> omega
              | succ d => simp [stepElemBB, stateFieldMax, listFieldMax_cons, tokFieldMax] <;> omega
    | repB1 k => simp [stepElemBB, stateFieldMax, listFieldMax_cons, tokFieldMax]
    | rep2 p => simp [stepElemBB, stateFieldMax, listFieldMax_cons, tokFieldMax]
    | rep12 m => simp [stepElemBB, stateFieldMax, listFieldMax_cons, tokFieldMax]

theorem stepElemDL_field_growth (L R : List SymTok) :
    stateFieldMax (stepElemDL L R) ≤ stateFieldMax (.DL, L, R) + 1 := by
  have hR := bumpSymR_field_growth R
  cases L with
  | nil => simp [stepElemDL, stateFieldMax]
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero => simp [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax]
      | run d =>
        cases d with
        | zero =>
          have hm := max_left_bump_le (listFieldMax L1) (listFieldMax R) (listFieldMax (bumpSymR R)) hR
          simp [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax]
          exact hm
        | succ d =>
          cases d with
          | zero =>
            have hm := max_left_bump_le (listFieldMax L1) (listFieldMax R) (listFieldMax (bumpSymR R)) hR
            simp [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax]
            exact Nat.le_trans hm (Nat.add_le_add_right (Nat.le_max_right 1 (max (listFieldMax L1) (listFieldMax R))) 1)
          | succ d =>
            cases d with
            | zero =>
              cases R with
              | nil => simp [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax]
              | cons r R1 =>
                cases r with
                | item y =>
                  cases y with
                  | zero => simp [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax]
                  | run d0 =>
                    simp [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax, prependZeroSym_field_max]
                    omega
                | repB1 k => simp [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax]
                | rep2 p => simp [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax]
                | rep12 m => simp [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax]
            | succ d => simp [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax]
    | repB1 k => simp [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax]
    | rep2 p => simp [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax]
    | rep12 m => simp [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax]

theorem stepElemCB_run0_field_growth (L R : List SymTok) :
    stateFieldMax (stepElemCB_run0 L R) ≤ stateFieldMax (.CB, L, .item (.run 0) :: R) + 1 := by
  have hL := bumpSymL_field_growth L
  cases R with
  | nil =>
    simp [stepElemCB_run0, stateFieldMax, listFieldMax_cons, tokFieldMax]
    omega
  | cons t R2 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        simp [stepElemCB_run0, stateFieldMax, listFieldMax_cons, tokFieldMax]
        omega
      | run d =>
        cases d with
        | zero =>
          simp [stepElemCB_run0, stateFieldMax, listFieldMax_cons, tokFieldMax]
          omega
        | succ d =>
          simp [stepElemCB_run0, stateFieldMax, listFieldMax_cons, tokFieldMax, prependZeroSym_field_max]
          omega
    | repB1 k => simp [stepElemCB_run0, stateFieldMax, listFieldMax_cons, tokFieldMax]
    | rep2 p => simp [stepElemCB_run0, stateFieldMax, listFieldMax_cons, tokFieldMax]
    | rep12 m => simp [stepElemCB_run0, stateFieldMax, listFieldMax_cons, tokFieldMax]

theorem stepElemCB_field_growth (L R : List SymTok) :
    stateFieldMax (stepElemCB L R) ≤ stateFieldMax (.CB, L, R) + 1 := by
  have hL := bumpSymL_field_growth L
  cases R with
  | nil =>
    simpa [stepElemCB, stateFieldMax, listFieldMax_cons, tokFieldMax] using
      (max_le_max_plus_one (a := listFieldMax L) (b := 0) (a' := listFieldMax (bumpSymL L)) (b' := 0) hL (by omega))
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        have hR1 := bumpSymR_field_growth R1
        simpa [stepElemCB, stateFieldMax, listFieldMax_cons, tokFieldMax] using
          (max_le_max_plus_one hL hR1)
      | run d =>
        cases d with
        | zero => simpa [stepElemCB] using stepElemCB_run0_field_growth L R1
        | succ d =>
          cases d with
          | zero =>
            have hRbound : listFieldMax R1 ≤ listFieldMax (.item (.run 1) :: R1) + 1 := by
              simp [listFieldMax_cons, tokFieldMax]
              omega
            simpa [stepElemCB, stateFieldMax, listFieldMax_cons, tokFieldMax] using
              (max_le_max_plus_one hL hRbound)
          | succ d =>
            cases d with
            | zero =>
              have hRbound : listFieldMax (.item (.run 0) :: .item .zero :: R1) ≤
                  listFieldMax (.item (.run 2) :: R1) + 1 := by
                simp [listFieldMax_cons, tokFieldMax]
                omega
              simpa [stepElemCB, stateFieldMax, listFieldMax_cons, tokFieldMax] using
                (max_le_max_plus_one hL hRbound)
            | succ d =>
              have hRbound : listFieldMax (.item (.run 0) :: .item (.run d) :: R1) ≤
                  listFieldMax (.item (.run (d+3)) :: R1) + 1 := by
                simp [listFieldMax_cons, tokFieldMax]
                omega
              simpa [stepElemCB, stateFieldMax, listFieldMax_cons, tokFieldMax] using
                (max_le_max_plus_one hL hRbound)
    | repB1 k => simp [stepElemCB, stateFieldMax, listFieldMax_cons, tokFieldMax]
    | rep2 p => simp [stepElemCB, stateFieldMax, listFieldMax_cons, tokFieldMax]
    | rep12 m => simp [stepElemCB, stateFieldMax, listFieldMax_cons, tokFieldMax]

theorem stepElemSym_field_growth (mode : SymMode) (L R : List SymTok) :
    stateFieldMax (stepElemSym mode L R) ≤ stateFieldMax (mode, L, R) + 1 := by
  cases mode with
  | BB => exact stepElemBB_field_growth L R
  | DL => exact stepElemDL_field_growth L R
  | CB => exact stepElemCB_field_growth L R
  | HALT => simp [stepElemSym, stateFieldMax]

theorem peelPureTok_field_growth (t : SymTok) (xs : List SymTok) :
    listFieldMax (peelPureTok t xs) ≤ max (tokFieldMax t) (listFieldMax xs) := by
  cases t with
  | item x => cases x <;> simp [peelPureTok, listFieldMax_cons, tokFieldMax]
  | repB1 k => cases k <;> simp [peelPureTok, listFieldMax_cons, tokFieldMax] <;> omega
  | rep2 p => cases p <;> simp [peelPureTok, listFieldMax_cons, tokFieldMax] <;> omega
  | rep12 m => cases m <;> simp [peelPureTok, listFieldMax_cons, tokFieldMax] <;> omega

theorem stripPrefixSym_suffix (pre xs rest : List SymTok)
    (h : stripPrefixSym pre xs = some rest) :
    listFieldMax rest ≤ listFieldMax xs := by
  have hx := stripPrefixSym_some pre xs rest h
  rw [hx, listFieldMax_append]
  exact Nat.le_max_right _ _

theorem stateFieldMax_left_mono (mode : SymMode) (L' L R : List SymTok)
    (hL : listFieldMax L' ≤ listFieldMax L) :
    stateFieldMax (mode, L', R) ≤ stateFieldMax (mode, L, R) := by
  simp only [stateFieldMax]
  apply Nat.max_le.mpr
  constructor
  · exact Nat.le_trans hL (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

theorem stepPureBB_field_growth (L R : List SymTok) :
    stateFieldMax (stepPureBB L R) ≤ stateFieldMax (.BB, L, R) + 1 := by
  cases L with
  | nil => exact stepElemBB_field_growth [] R
  | cons t L1 =>
    cases t with
    | item x => exact stepElemBB_field_growth (.item x :: L1) R
    | repB1 k =>
      simp [stepPureBB, stateFieldMax, listFieldMax_cons, tokFieldMax] <;> omega
    | rep2 p =>
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_suffix _ R R2 hs
        simp [stepPureBB, hs, stateFieldMax, listFieldMax_cons, tokFieldMax]
        omega
      | none =>
        have hp := peelPureTok_field_growth (.rep2 p) L1
        have hp' : listFieldMax (peelPureTok (.rep2 p) L1) ≤ listFieldMax (.rep2 p :: L1) := by
          simpa [listFieldMax_cons] using hp
        have hE := stepElemBB_field_growth (peelPureTok (.rep2 p) L1) R
        have hm := stateFieldMax_left_mono .BB (peelPureTok (.rep2 p) L1) (.rep2 p :: L1) R hp'
        calc
          stateFieldMax (stepPureBB (.rep2 p :: L1) R) ≤ stateFieldMax (.BB, peelPureTok (.rep2 p) L1, R) + 1 := by
            simpa [stepPureBB, hs] using hE
          _ ≤ stateFieldMax (.BB, .rep2 p :: L1, R) + 1 := Nat.add_le_add_right hm 1
    | rep12 m =>
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_suffix _ R R2 hs
        simp [stepPureBB, hs, stateFieldMax, listFieldMax_cons, tokFieldMax]
        omega
      | none =>
        have hp := peelPureTok_field_growth (.rep12 m) L1
        have hp' : listFieldMax (peelPureTok (.rep12 m) L1) ≤ listFieldMax (.rep12 m :: L1) := by
          simpa [listFieldMax_cons] using hp
        have hE := stepElemBB_field_growth (peelPureTok (.rep12 m) L1) R
        have hm := stateFieldMax_left_mono .BB (peelPureTok (.rep12 m) L1) (.rep12 m :: L1) R hp'
        calc
          stateFieldMax (stepPureBB (.rep12 m :: L1) R) ≤ stateFieldMax (.BB, peelPureTok (.rep12 m) L1, R) + 1 := by
            simpa [stepPureBB, hs] using hE
          _ ≤ stateFieldMax (.BB, .rep12 m :: L1, R) + 1 := Nat.add_le_add_right hm 1

theorem stepPureDL_field_growth (L R : List SymTok) :
    stateFieldMax (stepPureDL L R) ≤ stateFieldMax (.DL, L, R) + 1 := by
  cases L with
  | nil => simp [stepPureDL, stateFieldMax]
  | cons t L1 =>
    have hp := peelPureTok_field_growth t L1
    have hp' : listFieldMax (peelPureTok t L1) ≤ listFieldMax (t :: L1) := by
      simpa [listFieldMax_cons] using hp
    have hE := stepElemDL_field_growth (peelPureTok t L1) R
    have hm := stateFieldMax_left_mono .DL (peelPureTok t L1) (t :: L1) R hp'
    calc
      stateFieldMax (stepPureDL (t :: L1) R) ≤ stateFieldMax (.DL, peelPureTok t L1, R) + 1 := by
        simpa [stepPureDL] using hE
      _ ≤ stateFieldMax (.DL, t :: L1, R) + 1 := Nat.add_le_add_right hm 1

theorem stepPureCB_field_growth (L R : List SymTok) :
    stateFieldMax (stepPureCB L R) ≤ stateFieldMax (.CB, L, R) + 1 := by
  have hL := bumpSymL_field_growth L
  cases R with
  | nil => exact stepElemCB_field_growth L []
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero => exact stepElemCB_field_growth L (.item .zero :: R1)
      | run n =>
        cases n with
        | zero => exact stepElemCB_run0_field_growth L R1
        | succ n =>
          cases n with
          | zero => exact stepElemCB_field_growth L (.item (.run 1) :: R1)
          | succ n =>
            cases n with
            | zero => exact stepElemCB_field_growth L (.item (.run 2) :: R1)
            | succ n =>
              have hR : listFieldMax (.item (.run 0) :: .item (.run n) :: R1) ≤
                  listFieldMax (.item (.run (n+3)) :: R1) + 1 := by
                simp [listFieldMax_cons, tokFieldMax]
                omega
              simpa [stepPureCB, stateFieldMax, listFieldMax_cons, tokFieldMax] using
                (max_le_max_plus_one hL hR)
    | repB1 k =>
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1)] L with
      | some L2 =>
        have hL2 := stripPrefixSym_suffix _ L L2 hs
        have hR1 : listFieldMax R1 ≤ listFieldMax (.repB1 k :: R1) := by
          simpa using (listFieldMax_suffix [.repB1 k] R1)
        simp [stepPureCB, hs, stateFieldMax, listFieldMax_cons, tokFieldMax]
        omega
      | none =>
        cases hs2 : stripPrefixSym [.item (.run 0)] L with
        | some L1 =>
          have hL1 := stripPrefixSym_suffix _ L L1 hs2
          have hR1 : listFieldMax R1 ≤ listFieldMax (.repB1 k :: R1) := by
            simpa using (listFieldMax_suffix [.repB1 k] R1)
          simp [stepPureCB, hs, hs2, stateFieldMax, listFieldMax_cons, tokFieldMax]
          omega
        | none => simp [stepPureCB, hs, hs2, stateFieldMax]
    | rep2 p =>
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] L with
      | some L2 =>
        have hL2 := stripPrefixSym_suffix _ L L2 hs
        have hR1 : listFieldMax R1 ≤ listFieldMax (.rep2 p :: R1) := by
          simpa using (listFieldMax_suffix [.rep2 p] R1)
        simp [stepPureCB, hs, stateFieldMax, listFieldMax_cons, tokFieldMax]
        omega
      | none =>
        cases hs2 : stripPrefixSym [.item (.run 0)] L with
        | some L1 =>
          have hL1 := stripPrefixSym_suffix _ L L1 hs2
          have hR1 : listFieldMax R1 ≤ listFieldMax (.rep2 p :: R1) := by
            simpa using (listFieldMax_suffix [.rep2 p] R1)
          simp [stepPureCB, hs, hs2, stateFieldMax, listFieldMax_cons, tokFieldMax]
          omega
        | none => simp [stepPureCB, hs, hs2, stateFieldMax]
    | rep12 m =>
      cases hs : stripPrefixSym [.item (.run 0)] L with
      | some L1 =>
        have hL1 := stripPrefixSym_suffix _ L L1 hs
        have hR1 : listFieldMax R1 ≤ listFieldMax (.rep12 m :: R1) := by
          simpa using (listFieldMax_suffix [.rep12 m] R1)
        simp [stepPureCB, hs, stateFieldMax, listFieldMax_cons, tokFieldMax]
        omega
      | none => simp [stepPureCB, hs, stateFieldMax]

theorem stepPure_field_growth (s : SymState) :
    stateFieldMax (stepPure s) ≤ stateFieldMax s + 1 := by
  cases s with
  | mk mode rest =>
    cases rest with
    | mk L R =>
      cases mode with
      | BB => exact stepPureBB_field_growth L R
      | DL => exact stepPureDL_field_growth L R
      | CB => exact stepPureCB_field_growth L R
      | HALT => simp [stepPure, stateFieldMax]

#print axioms stepPure_field_growth


end BusyBeaver.SymRunAudit
