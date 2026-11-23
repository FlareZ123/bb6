/-
Copyright (c) 2026 FlareZ123. All rights reserved.
Research scratch certificate against google-deepmind/cryptids commit
3647718b5df22e1a61462dec0376bd204526285a.
-/
import BusyBeaver.BB6.Halt.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH
import BusyBeaver.BB6.Halt.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA

set_option maxRecDepth 200000

open BusyBeaver.SymRunEngine

attribute [local simp] strictList_eq

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
      | run d => simp [bumpSymL, listFieldMax_cons, tokFieldMax]<;> omega
    | repB1 k =>
      cases k with
      | zero => simpa [bumpSymL, listFieldMax_cons, tokFieldMax] using ih
      | succ k =>
        cases k with
        | zero => simp [bumpSymL, listFieldMax_cons, tokFieldMax]<;> omega
        | succ k => simp [bumpSymL, listFieldMax_cons, tokFieldMax]<;> omega
    | rep2 p =>
      cases p with
      | zero => simpa [bumpSymL, listFieldMax_cons, tokFieldMax] using ih
      | succ p => simp [bumpSymL, listFieldMax_cons, tokFieldMax]<;> omega
    | rep12 m =>
      cases m with
      | zero => simpa [bumpSymL, listFieldMax_cons, tokFieldMax] using ih
      | succ m => simp [bumpSymL, listFieldMax_cons, tokFieldMax]<;> omega

theorem bumpSymR_field_growth (xs : List SymTok) :
    listFieldMax (bumpSymR xs) ≤ listFieldMax xs + 1 := by
  induction xs with
  | nil => simp [bumpSymR, listFieldMax, tokFieldMax]
  | cons t xs ih =>
    cases t with
    | item x =>
      cases x with
      | zero => simp [bumpSymR, listFieldMax_cons, tokFieldMax]
      | run d => simp [bumpSymR, listFieldMax_cons, tokFieldMax]<;> omega
    | repB1 k =>
      cases k with
      | zero => simpa [bumpSymR, listFieldMax_cons, tokFieldMax] using ih
      | succ k =>
        cases k with
        | zero => simp [bumpSymR, listFieldMax_cons, tokFieldMax]<;> omega
        | succ k => simp [bumpSymR, listFieldMax_cons, tokFieldMax]<;> omega
    | rep2 p =>
      cases p with
      | zero => simpa [bumpSymR, listFieldMax_cons, tokFieldMax] using ih
      | succ p => simp [bumpSymR, listFieldMax_cons, tokFieldMax]<;> omega
    | rep12 m =>
      cases m with
      | zero => simpa [bumpSymR, listFieldMax_cons, tokFieldMax] using ih
      | succ m => simp [bumpSymR, listFieldMax_cons, tokFieldMax]<;> omega

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

theorem max_left_bump_le_head (a b c k : Nat) (hc : c ≤ b+1) :
    max a c ≤ max k (max a b) + 1 := by
  omega

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
            simpa [stepElemBB, stateFieldMax, listFieldMax_cons, tokFieldMax, strictList_eq] using
              (max_left_bump_le_head (listFieldMax L1) (listFieldMax R)
                (listFieldMax (bumpSymR R)) 1 hR)
          | succ d =>
            cases d with
            | zero =>
              simpa [stepElemBB, stateFieldMax, listFieldMax_cons, tokFieldMax, strictList_eq] using
                (max_left_bump_le_head (listFieldMax L1) (listFieldMax R)
                  (listFieldMax (bumpSymR R)) 2 hR)
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
          simpa [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax, strictList_eq] using
            (max_left_bump_le_head (listFieldMax L1) (listFieldMax R)
              (listFieldMax (bumpSymR R)) 0 hR)
        | succ d =>
          cases d with
          | zero =>
            simpa [stepElemDL, stateFieldMax, listFieldMax_cons, tokFieldMax, strictList_eq] using
              (max_left_bump_le_head (listFieldMax L1) (listFieldMax R)
                (listFieldMax (bumpSymR R)) 1 hR)
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


def stepPureIter : Nat → SymState → SymState
  | 0, s => s
  | n+1, s => stepPureIter n (stepPure s)

theorem stepPureIter_field_growth (n : Nat) (s : SymState) :
    stateFieldMax (stepPureIter n s) ≤ stateFieldMax s + n := by
  induction n generalizing s with
  | zero => simp [stepPureIter]
  | succ n ih =>
    calc
      stateFieldMax (stepPureIter (n+1) s) = stateFieldMax (stepPureIter n (stepPure s)) := rfl
      _ ≤ stateFieldMax (stepPure s) + n := ih (stepPure s)
      _ ≤ stateFieldMax s + 1 + n := Nat.add_le_add_right (stepPure_field_growth s) n
      _ = stateFieldMax s + (n+1) := by omega

#print axioms stepPureIter_field_growth

#print axioms stepPure_field_growth



/-!
## Token-length bounds for the CB sweep and BB fallback

The recursive CB sweep consumes at least one right token per recursive call.
Each ordinary run-triggered call adds at most five tokens to the left stack;
the repeat-token calls move the repeat token across while eatFuel adds at
most one token. Consequently the sweep's total token count is at most
|L| + 6|R| ≤ 6(|L|+|R|). If the incoming state has at most 94 tokens,
the sweep output has at most 564. A BB-producing stepElemCB fallback adds
at most six more, giving the 570-token bound for the subsequent BB sweep.
-/

def symPairLen (p : List SymTok × List SymTok) : Nat := p.1.length + p.2.length

theorem bumpSymL_length_le (xs : List SymTok) : (bumpSymL xs).length ≤ xs.length + 5 := by
  induction xs with
  | nil => simp [bumpSymL]
  | cons t xs ih =>
    cases t with
    | item x => cases x <;> simp [bumpSymL, strictNat_eq]
    | repB1 k =>
      cases k with
      | zero => simp [bumpSymL]<;> omega
      | succ k => cases k <;> simp [bumpSymL, strictNat_eq]
    | rep2 p =>
      cases p with
      | zero => simp [bumpSymL]<;> omega
      | succ p => simp [bumpSymL, strictNat_eq]
    | rep12 m =>
      cases m with
      | zero => simp [bumpSymL]<;> omega
      | succ m => simp [bumpSymL, strictNat_eq]

theorem bumpSymR_length_le (xs : List SymTok) : (bumpSymR xs).length ≤ xs.length + 5 := by
  induction xs with
  | nil => simp [bumpSymR]
  | cons t xs ih =>
    cases t with
    | item x => cases x <;> simp [bumpSymR, strictNat_eq]
    | repB1 k =>
      cases k with
      | zero => simp [bumpSymR]<;> omega
      | succ k => cases k <;> simp [bumpSymR, strictNat_eq]
    | rep2 p =>
      cases p with
      | zero => simp [bumpSymR]<;> omega
      | succ p => simp [bumpSymR, strictNat_eq]
    | rep12 m =>
      cases m with
      | zero => simp [bumpSymR]<;> omega
      | succ m => simp [bumpSymR, strictNat_eq]

theorem eatStep_some_length_le (blk : List SymTok) (getRep : SymTok → Option Nat)
    (k k' : Nat) (xs rest : List SymTok)
    (h : eatStep blk getRep k xs = some (k', rest)) : rest.length ≤ xs.length := by
  cases xs with
  | nil => simp [eatStep] at h
  | cons x xs1 =>
    unfold eatStep at h
    cases hget : getRep x with
    | some k2 =>
      simp [hget] at h
      rcases h with ⟨_, hr⟩
      subst rest
      simp
    | none =>
      cases hs : stripPrefixSym blk (x :: xs1) with
      | none => simp [hget, hs] at h
      | some rest2 =>
        simp [hget, hs] at h
        rcases h with ⟨_, hr⟩
        subst rest
        have hprefix := stripPrefixSym_some blk (x :: xs1) rest2 hs
        rw [hprefix, List.length_append]
        omega

theorem eatFuel_length_le (blk : List SymTok) (mkRep : Nat → SymTok)
    (getRep : SymTok → Option Nat) (fuel k : Nat) (xs : List SymTok) :
    (eatFuel blk mkRep getRep fuel k xs).length ≤ xs.length + 1 := by
  induction fuel generalizing k xs with
  | zero => simp [eatFuel]
  | succ fuel ih =>
    cases hs : eatStep blk getRep k xs with
    | none => simp [eatFuel, hs]
    | some pair =>
      rcases pair with ⟨k', rest⟩
      have hlen := eatStep_some_length_le blk getRep k k' xs rest hs
      simp [eatFuel, hs, strictNat_eq]
      exact Nat.le_trans (ih k' rest) (Nat.add_le_add_right hlen 1)

theorem eatB1_length_le (k : Nat) (xs : List SymTok) :
    (eatB1 k xs).length ≤ xs.length + 1 := by
  simpa [eatB1] using
    (eatFuel_length_le [.item (.run 0), .item (.run 1)] .repB1 getRepB1 4 k xs)

theorem eatC2_length_le (k : Nat) (xs : List SymTok) :
    (eatC2 k xs).length ≤ xs.length + 1 := by
  simpa [eatC2] using
    (eatFuel_length_le [.item (.run 1), .item (.run 0), .item (.run 1)] .rep2 getRep2 4 k xs)

theorem eatC12_length_le (k : Nat) (xs : List SymTok) :
    (eatC12 k xs).length ≤ xs.length + 1 := by
  simpa [eatC12] using
    (eatFuel_length_le [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] .rep12 getRep12 4 k xs)

theorem stripPrefixSym_length_suffix (pre xs rest : List SymTok)
    (h : stripPrefixSym pre xs = some rest) : rest.length ≤ xs.length := by
  have hx := stripPrefixSym_some pre xs rest h
  rw [hx, List.length_append]
  omega

theorem sweepCB_length_bound (L R : List SymTok) :
    symPairLen (sweepCB L R) ≤ L.length + R.length + 5 * R.length := by
  generalize hn : R.length = n
  induction n using Nat.strongRecOn generalizing R L with
  | ind n ih =>
    have hlen : R.length = n := hn
    cases R with
    | nil => simp [symPairLen, sweepCB] <;> omega
    | cons t R1 =>
      simp at hlen
      have hR1 : R1.length < n := by omega
      have hrecR1 (L' : List SymTok) :
          symPairLen (sweepCB L' R1) ≤ L'.length + R1.length + 5 * R1.length :=
        ih R1.length (by omega) L' R1 rfl
      cases t with
      | item x =>
        cases x with
        | zero => simp [symPairLen, sweepCB] <;> omega
        | run d =>
          cases d with
          | zero =>
            cases R1 with
            | nil => simp [symPairLen, sweepCB] <;> omega
            | cons t2 R2 =>
              simp at hlen
              have hR2 : R2.length < n := by omega
              have hrecR2 (L' : List SymTok) :
                  symPairLen (sweepCB L' R2) ≤ L'.length + R2.length + 5 * R2.length :=
                ih R2.length (by omega) L' R2 rfl
              cases t2 with
              | item y =>
                cases y with
                | zero => simp [symPairLen, sweepCB] <;> omega
                | run d2 =>
                  cases d2 with
                  | zero => simp [symPairLen, sweepCB] <;> omega
                  | succ d2 =>
                    cases d2 with
                    | zero =>
                      have hb := bumpSymL_length_le L
                      have hL' : (.item (.run 0) :: .item (.run 0) :: bumpSymL L).length ≤ L.length + 7 := by
                        simp
                        omega
                      have hEq : R2.length + 2 = n := by omega
                      calc
                        symPairLen (sweepCB L (.item (.run 0) :: .item (.run 1) :: R2)) =
                            symPairLen (sweepCB (.item (.run 0) :: .item (.run 0) :: bumpSymL L) R2) := by
                          simp [sweepCB, strictList_eq, symPairLen]
                        _ ≤ (.item (.run 0) :: .item (.run 0) :: bumpSymL L).length + R2.length + 5 * R2.length :=
                          hrecR2 (.item (.run 0) :: .item (.run 0) :: bumpSymL L)
                        _ ≤ L.length + n + 5 * n := by rw [← hEq]<;> omega
                    | succ d2 => simp [symPairLen, sweepCB] <;> omega
              | repB1 k => simp [symPairLen, sweepCB] <;> omega
              | rep2 p => simp [symPairLen, sweepCB] <;> omega
              | rep12 m => simp [symPairLen, sweepCB] <;> omega
          | succ d =>
            cases d with
            | zero =>
              have hb := bumpSymL_length_le L
              have hL' : (.item (.run 0) :: bumpSymL L).length ≤ L.length + 6 := by
                simp
                omega
              have hEq : R1.length + 1 = n := by omega
              calc
                symPairLen (sweepCB L (.item (.run 1) :: R1)) =
                    symPairLen (sweepCB (.item (.run 0) :: bumpSymL L) R1) := by
                  simp [sweepCB, strictList_eq, symPairLen]
                _ ≤ (.item (.run 0) :: bumpSymL L).length + R1.length + 5 * R1.length :=
                  hrecR1 (.item (.run 0) :: bumpSymL L)
                _ ≤ L.length + n + 5 * n := by rw [← hEq]<;> omega
            | succ d => simp [symPairLen, sweepCB] <;> omega
      | repB1 k =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairLen, sweepCB, hs] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatB1_length_le k L1
          have hL' : (.item (.run 0) :: eatB1 k L1).length ≤ L.length + 1 := by
            rw [hprefix, List.length_append]
            simp
            omega
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairLen (sweepCB L (.repB1 k :: R1)) = symPairLen (sweepCB (.item (.run 0) :: eatB1 k L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairLen]
            _ ≤ (.item (.run 0) :: eatB1 k L1).length + R1.length + 5 * R1.length :=
              hrecR1 (.item (.run 0) :: eatB1 k L1)
            _ ≤ L.length + n + 5 * n := by rw [← hEq]<;> omega
      | rep2 p =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairLen, sweepCB, hs] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatC2_length_le p L1
          have hL' : (.item (.run 0) :: eatC2 p L1).length ≤ L.length + 1 := by
            rw [hprefix, List.length_append]
            simp
            omega
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairLen (sweepCB L (.rep2 p :: R1)) = symPairLen (sweepCB (.item (.run 0) :: eatC2 p L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairLen]
            _ ≤ (.item (.run 0) :: eatC2 p L1).length + R1.length + 5 * R1.length :=
              hrecR1 (.item (.run 0) :: eatC2 p L1)
            _ ≤ L.length + n + 5 * n := by rw [← hEq]<;> omega
      | rep12 m =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairLen, sweepCB, hs] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatC12_length_le m L1
          have hL' : (.item (.run 0) :: eatC12 m L1).length ≤ L.length + 1 := by
            rw [hprefix, List.length_append]
            simp
            omega
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairLen (sweepCB L (.rep12 m :: R1)) = symPairLen (sweepCB (.item (.run 0) :: eatC12 m L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairLen]
            _ ≤ (.item (.run 0) :: eatC12 m L1).length + R1.length + 5 * R1.length :=
              hrecR1 (.item (.run 0) :: eatC12 m L1)
            _ ≤ L.length + n + 5 * n := by rw [← hEq]<;> omega

theorem sweepCB_length_le_six (L R : List SymTok) :
    symPairLen (sweepCB L R) ≤ 6 * (L.length + R.length) := by
  have h := sweepCB_length_bound L R
  omega

theorem sweepCB_length_le_564 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94) :
    symPairLen (sweepCB L R) ≤ 564 := by
  have h := sweepCB_length_le_six L R
  omega

theorem stepElemCB_BB_length_bound (L R : List SymTok)
    (hmode : (stepElemCB L R).1 = .BB) :
    symPairLen ((stepElemCB L R).2.1, (stepElemCB L R).2.2) ≤ L.length + R.length + 6 := by
  cases R with
  | nil => simp [stepElemCB] at hmode
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero => simp [stepElemCB] at hmode
      | run d =>
        cases d with
        | zero =>
          cases R1 with
          | nil =>
            have hL := bumpSymL_length_le L
            simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairLen]
            omega
          | cons t2 R2 =>
            cases t2 with
            | item y =>
              cases y with
              | zero =>
                have hL := bumpSymL_length_le L
                simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairLen]
                omega
              | run d2 =>
                cases d2 with
                | zero =>
                  have hL := bumpSymL_length_le L
                  simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairLen]
                  omega
                | succ d2 => simp [stepElemCB, stepElemCB_run0] at hmode
            | repB1 k => simp [stepElemCB, stepElemCB_run0] at hmode
            | rep2 p => simp [stepElemCB, stepElemCB_run0] at hmode
            | rep12 m => simp [stepElemCB, stepElemCB_run0] at hmode
        | succ d =>
          cases d with
          | zero => simp [stepElemCB] at hmode
          | succ d =>
            cases d with
            | zero =>
              have hL := bumpSymL_length_le L
              simp [stepElemCB, strictList_eq, symPairLen]
              omega
            | succ d =>
              have hL := bumpSymL_length_le L
              simp [stepElemCB, strictList_eq, symPairLen]
              omega
    | repB1 k => simp [stepElemCB] at hmode
    | rep2 p => simp [stepElemCB] at hmode
    | rep12 m => simp [stepElemCB] at hmode

theorem stepElemCB_after_sweep_570 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94)
    (hBB : (stepElemCB (sweepCB L R).1 (sweepCB L R).2).1 = .BB) :
    symPairLen ((stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1,
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2) ≤ 570 := by
  have hSweep := sweepCB_length_le_six L R
  have hSweep' : (sweepCB L R).1.length + (sweepCB L R).2.length ≤
      6 * (L.length + R.length) := by simpa [symPairLen] using hSweep
  have hElem := stepElemCB_BB_length_bound (sweepCB L R).1 (sweepCB L R).2 hBB
  omega

#print axioms sweepCB_length_bound
#print axioms stepElemCB_BB_length_bound
#print axioms stepElemCB_after_sweep_570



/-!
## CB sweep repeat-counter accounting

tokCounterSum counts the numeric repeat counters, ignoring literal run tokens.
bumpSymL/R never increase this sum. Each eatFuel invocation can increase it
by at most its fuel (four here): consuming an existing repeat token transfers
its counter, while matching a literal block contributes one unit. The CB
sweep makes at most |R| recursive calls, so under the 94-token trace invariant
its output counter sum is at most 94*M + 376.
-/

def tokCounterSum : SymTok → Nat
  | .item _ => 0
  | .repB1 k => k
  | .rep2 p => p
  | .rep12 m => m

def listCounterSum : List SymTok → Nat
  | [] => 0
  | t :: xs => tokCounterSum t + listCounterSum xs

@[simp] theorem listCounterSum_nil : listCounterSum [] = 0 := rfl
@[simp] theorem listCounterSum_cons (t : SymTok) (xs : List SymTok) :
    listCounterSum (t :: xs) = tokCounterSum t + listCounterSum xs := rfl

theorem listCounterSum_append (xs ys : List SymTok) :
    listCounterSum (xs ++ ys) = listCounterSum xs + listCounterSum ys := by
  induction xs with
  | nil => simp [listCounterSum]
  | cons t xs ih => simp [listCounterSum, ih, Nat.add_assoc]

theorem bumpSymL_counter_sum_le (xs : List SymTok) :
    listCounterSum (bumpSymL xs) ≤ listCounterSum xs := by
  induction xs with
  | nil => simp [bumpSymL, listCounterSum, tokCounterSum]
  | cons t xs ih =>
    cases t with
    | item x => cases x <;> simp [bumpSymL, listCounterSum, tokCounterSum]
    | repB1 k =>
      cases k with
      | zero => simpa [bumpSymL, listCounterSum, tokCounterSum] using ih
      | succ k =>
        cases k with
        | zero => simp [bumpSymL, listCounterSum, tokCounterSum]
        | succ k => simp [bumpSymL, listCounterSum, tokCounterSum]<;> omega
    | rep2 p =>
      cases p with
      | zero => simpa [bumpSymL, listCounterSum, tokCounterSum] using ih
      | succ p => simp [bumpSymL, listCounterSum, tokCounterSum]<;> omega
    | rep12 m =>
      cases m with
      | zero => simpa [bumpSymL, listCounterSum, tokCounterSum] using ih
      | succ m => simp [bumpSymL, listCounterSum, tokCounterSum]<;> omega

theorem bumpSymR_counter_sum_le (xs : List SymTok) :
    listCounterSum (bumpSymR xs) ≤ listCounterSum xs := by
  induction xs with
  | nil => simp [bumpSymR, listCounterSum, tokCounterSum]
  | cons t xs ih =>
    cases t with
    | item x => cases x <;> simp [bumpSymR, listCounterSum, tokCounterSum]
    | repB1 k =>
      cases k with
      | zero => simpa [bumpSymR, listCounterSum, tokCounterSum] using ih
      | succ k =>
        cases k with
        | zero => simp [bumpSymR, listCounterSum, tokCounterSum]
        | succ k => simp [bumpSymR, listCounterSum, tokCounterSum]<;> omega
    | rep2 p =>
      cases p with
      | zero => simpa [bumpSymR, listCounterSum, tokCounterSum] using ih
      | succ p => simp [bumpSymR, listCounterSum, tokCounterSum]<;> omega
    | rep12 m =>
      cases m with
      | zero => simpa [bumpSymR, listCounterSum, tokCounterSum] using ih
      | succ m => simp [bumpSymR, listCounterSum, tokCounterSum]<;> omega

theorem eatStep_counter_sum_le (blk : List SymTok) (getRep : SymTok → Option Nat)
    (hblk : listCounterSum blk = 0)
    (hget : ∀ x k2, getRep x = some k2 → tokCounterSum x = k2)
    (k k' : Nat) (xs rest : List SymTok)
    (h : eatStep blk getRep k xs = some (k', rest)) :
    k' + listCounterSum rest ≤ k + listCounterSum xs + 1 := by
  cases xs with
  | nil => simp [eatStep] at h
  | cons x xs1 =>
    unfold eatStep at h
    cases hg : getRep x with
    | some k2 =>
      simp [hg] at h
      rcases h with ⟨rfl, rfl⟩
      simp [listCounterSum, hget x k2 hg]
      omega
    | none =>
      cases hs : stripPrefixSym blk (x :: xs1) with
      | none => simp [hg, hs] at h
      | some rest2 =>
        simp [hg, hs] at h
        rcases h with ⟨rfl, rfl⟩
        have hprefix := stripPrefixSym_some blk (x :: xs1) rest2 hs
        rw [hprefix, listCounterSum_append, hblk]
        simp [listCounterSum]
        omega

theorem eatFuel_counter_sum_le (blk : List SymTok) (mkRep : Nat → SymTok)
    (getRep : SymTok → Option Nat)
    (hblk : listCounterSum blk = 0)
    (hMk : ∀ k, tokCounterSum (mkRep k) = k)
    (hget : ∀ x k2, getRep x = some k2 → tokCounterSum x = k2)
    (fuel k : Nat) (xs : List SymTok) :
    listCounterSum (eatFuel blk mkRep getRep fuel k xs) ≤ k + listCounterSum xs + fuel := by
  induction fuel generalizing k xs with
  | zero => simp [eatFuel, listCounterSum, hMk]
  | succ fuel ih =>
    cases hs : eatStep blk getRep k xs with
    | none => simp [eatFuel, hs, listCounterSum, hMk]
    | some pair =>
      rcases pair with ⟨k', rest⟩
      have hstep := eatStep_counter_sum_le blk getRep hblk hget k k' xs rest hs
      have hrec := ih k' rest
      simp [eatFuel, hs, strictNat_eq]
      calc
        listCounterSum (eatFuel blk mkRep getRep fuel k' rest) ≤ k' + listCounterSum rest + fuel := hrec
        _ ≤ k + listCounterSum xs + 1 + fuel := Nat.add_le_add_right hstep fuel
        _ = k + listCounterSum xs + (fuel + 1) := by omega

theorem getRepB1_counter (x : SymTok) (k : Nat) (h : getRepB1 x = some k) :
    tokCounterSum x = k := by
  cases x with
  | item x => simp [getRepB1] at h
  | repB1 n => simp [getRepB1] at h; simpa [tokCounterSum] using h
  | rep2 p => simp [getRepB1] at h
  | rep12 m => simp [getRepB1] at h

theorem getRep2_counter (x : SymTok) (k : Nat) (h : getRep2 x = some k) :
    tokCounterSum x = k := by
  cases x with
  | item x => simp [getRep2] at h
  | repB1 n => simp [getRep2] at h
  | rep2 p => simp [getRep2] at h; simpa [tokCounterSum] using h
  | rep12 m => simp [getRep2] at h

theorem getRep12_counter (x : SymTok) (k : Nat) (h : getRep12 x = some k) :
    tokCounterSum x = k := by
  cases x with
  | item x => simp [getRep12] at h
  | repB1 n => simp [getRep12] at h
  | rep2 p => simp [getRep12] at h
  | rep12 m => simp [getRep12] at h; simpa [tokCounterSum] using h

theorem eatB1_counter_sum_le (k : Nat) (xs : List SymTok) :
    listCounterSum (eatB1 k xs) ≤ k + listCounterSum xs + 4 := by
  simpa [eatB1] using
    (eatFuel_counter_sum_le [.item (.run 0), .item (.run 1)] .repB1 getRepB1
      (by simp [listCounterSum, tokCounterSum]) (by intro n; simp [tokCounterSum])
      getRepB1_counter 4 k xs)

theorem eatC2_counter_sum_le (k : Nat) (xs : List SymTok) :
    listCounterSum (eatC2 k xs) ≤ k + listCounterSum xs + 4 := by
  simpa [eatC2] using
    (eatFuel_counter_sum_le [.item (.run 1), .item (.run 0), .item (.run 1)] .rep2 getRep2
      (by simp [listCounterSum, tokCounterSum]) (by intro n; simp [tokCounterSum])
      getRep2_counter 4 k xs)

theorem eatC12_counter_sum_le (k : Nat) (xs : List SymTok) :
    listCounterSum (eatC12 k xs) ≤ k + listCounterSum xs + 4 := by
  simpa [eatC12] using
    (eatFuel_counter_sum_le [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] .rep12 getRep12
      (by simp [listCounterSum, tokCounterSum]) (by intro n; simp [tokCounterSum])
      getRep12_counter 4 k xs)

def symPairCounterSum (p : List SymTok × List SymTok) : Nat :=
  listCounterSum p.1 + listCounterSum p.2

theorem sweepCB_counter_sum_bound (L R : List SymTok) :
    symPairCounterSum (sweepCB L R) ≤
      listCounterSum L + listCounterSum R + 4 * R.length := by
  generalize hn : R.length = n
  induction n using Nat.strongRecOn generalizing R L with
  | ind n ih =>
    have hlen : R.length = n := hn
    cases R with
    | nil => simp [symPairCounterSum, sweepCB, listCounterSum] <;> omega
    | cons t R1 =>
      simp at hlen
      have hrecR1 (L' : List SymTok) :
          symPairCounterSum (sweepCB L' R1) ≤
            listCounterSum L' + listCounterSum R1 + 4 * R1.length :=
        ih R1.length (by omega) L' R1 rfl
      cases t with
      | item x =>
        cases x with
        | zero => simp [symPairCounterSum, sweepCB, listCounterSum, tokCounterSum] <;> omega
        | run d =>
          cases d with
          | zero =>
            cases R1 with
            | nil => simp [symPairCounterSum, sweepCB, listCounterSum, tokCounterSum] <;> omega
            | cons t2 R2 =>
              simp at hlen
              have hrecR2 (L' : List SymTok) :
                  symPairCounterSum (sweepCB L' R2) ≤
                    listCounterSum L' + listCounterSum R2 + 4 * R2.length :=
                ih R2.length (by omega) L' R2 rfl
              cases t2 with
              | item y =>
                cases y with
                | zero => simp [symPairCounterSum, sweepCB, listCounterSum, tokCounterSum] <;> omega
                | run d2 =>
                  cases d2 with
                  | zero => simp [symPairCounterSum, sweepCB, listCounterSum, tokCounterSum] <;> omega
                  | succ d2 =>
                    cases d2 with
                    | zero =>
                      have hB := bumpSymL_counter_sum_le L
                      have hEq : R2.length + 2 = n := by omega
                      calc
                        symPairCounterSum (sweepCB L (.item (.run 0) :: .item (.run 1) :: R2)) =
                            symPairCounterSum (sweepCB (.item (.run 0) :: .item (.run 0) :: bumpSymL L) R2) := by
                          simp [sweepCB, strictList_eq, symPairCounterSum, listCounterSum, tokCounterSum]
                        _ ≤ listCounterSum (.item (.run 0) :: .item (.run 0) :: bumpSymL L) +
                              listCounterSum R2 + 4 * R2.length :=
                          hrecR2 (.item (.run 0) :: .item (.run 0) :: bumpSymL L)
                        _ ≤ listCounterSum L + listCounterSum (.item (.run 0) :: .item (.run 1) :: R2) + 4 * n := by
                          simp [listCounterSum, tokCounterSum]
                          omega
                    | succ d2 => simp [symPairCounterSum, sweepCB, listCounterSum, tokCounterSum] <;> omega
              | repB1 k => simp [symPairCounterSum, sweepCB, listCounterSum, tokCounterSum] <;> omega
              | rep2 p => simp [symPairCounterSum, sweepCB, listCounterSum, tokCounterSum] <;> omega
              | rep12 m => simp [symPairCounterSum, sweepCB, listCounterSum, tokCounterSum] <;> omega
          | succ d =>
            cases d with
            | zero =>
              have hB := bumpSymL_counter_sum_le L
              have hEq : R1.length + 1 = n := by omega
              calc
                symPairCounterSum (sweepCB L (.item (.run 1) :: R1)) =
                    symPairCounterSum (sweepCB (.item (.run 0) :: bumpSymL L) R1) := by
                  simp [sweepCB, strictList_eq, symPairCounterSum, listCounterSum, tokCounterSum]
                _ ≤ listCounterSum (.item (.run 0) :: bumpSymL L) + listCounterSum R1 + 4 * R1.length :=
                  hrecR1 (.item (.run 0) :: bumpSymL L)
                _ ≤ listCounterSum L + listCounterSum (.item (.run 1) :: R1) + 4 * n := by
                  simp [listCounterSum, tokCounterSum]
                  omega
            | succ d => simp [symPairCounterSum, sweepCB, listCounterSum, tokCounterSum] <;> omega
      | repB1 k =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairCounterSum, sweepCB, hs, listCounterSum, tokCounterSum] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatB1_counter_sum_le k L1
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairCounterSum (sweepCB L (.repB1 k :: R1)) =
                symPairCounterSum (sweepCB (.item (.run 0) :: eatB1 k L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairCounterSum, listCounterSum, tokCounterSum]
            _ ≤ listCounterSum (.item (.run 0) :: eatB1 k L1) + listCounterSum R1 + 4 * R1.length :=
              hrecR1 (.item (.run 0) :: eatB1 k L1)
            _ ≤ listCounterSum L + listCounterSum (.repB1 k :: R1) + 4 * n := by
              rw [hprefix, listCounterSum_append] at *
              simp [listCounterSum, tokCounterSum]
              omega
      | rep2 p =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairCounterSum, sweepCB, hs, listCounterSum, tokCounterSum] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatC2_counter_sum_le p L1
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairCounterSum (sweepCB L (.rep2 p :: R1)) =
                symPairCounterSum (sweepCB (.item (.run 0) :: eatC2 p L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairCounterSum, listCounterSum, tokCounterSum]
            _ ≤ listCounterSum (.item (.run 0) :: eatC2 p L1) + listCounterSum R1 + 4 * R1.length :=
              hrecR1 (.item (.run 0) :: eatC2 p L1)
            _ ≤ listCounterSum L + listCounterSum (.rep2 p :: R1) + 4 * n := by
              rw [hprefix, listCounterSum_append] at *
              simp [listCounterSum, tokCounterSum]
              omega
      | rep12 m =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairCounterSum, sweepCB, hs, listCounterSum, tokCounterSum] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatC12_counter_sum_le m L1
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairCounterSum (sweepCB L (.rep12 m :: R1)) =
                symPairCounterSum (sweepCB (.item (.run 0) :: eatC12 m L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairCounterSum, listCounterSum, tokCounterSum]
            _ ≤ listCounterSum (.item (.run 0) :: eatC12 m L1) + listCounterSum R1 + 4 * R1.length :=
              hrecR1 (.item (.run 0) :: eatC12 m L1)
            _ ≤ listCounterSum L + listCounterSum (.rep12 m :: R1) + 4 * n := by
              rw [hprefix, listCounterSum_append] at *
              simp [listCounterSum, tokCounterSum]
              omega

theorem listCounterSum_le_length_mul_fieldMax (xs : List SymTok) :
    listCounterSum xs ≤ xs.length * listFieldMax xs := by
  induction xs with
  | nil => simp [listCounterSum, listFieldMax]
  | cons t xs ih =>
    have ht : tokCounterSum t ≤ tokFieldMax t := by
      cases t <;> simp [tokCounterSum, tokFieldMax]
    have ht' : tokCounterSum t ≤ listFieldMax (t :: xs) := by
      calc
        tokCounterSum t ≤ tokFieldMax t := ht
        _ ≤ max (tokFieldMax t) (listFieldMax xs) := Nat.le_max_left _ _
        _ = listFieldMax (t :: xs) := by simp [listFieldMax_cons]
    have htail : listFieldMax xs ≤ listFieldMax (t :: xs) := by
      simpa [listFieldMax_cons] using (Nat.le_max_right (tokFieldMax t) (listFieldMax xs))
    have htail' : listCounterSum xs ≤ xs.length * listFieldMax (t :: xs) :=
      Nat.le_trans ih (Nat.mul_le_mul_left xs.length htail)
    calc
      listCounterSum (t :: xs) = tokCounterSum t + listCounterSum xs := rfl
      _ ≤ listFieldMax (t :: xs) + xs.length * listFieldMax (t :: xs) := Nat.add_le_add ht' htail'
      _ = (xs.length + 1) * listFieldMax (t :: xs) := by
        rw [Nat.add_mul]
        omega

theorem sweepCB_counter_sum_le_94M376 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94) :
    symPairCounterSum (sweepCB L R) ≤ 94 * stateFieldMax (.CB, L, R) + 376 := by
  have hLsum := listCounterSum_le_length_mul_fieldMax L
  have hRsum := listCounterSum_le_length_mul_fieldMax R
  have hLmax : listFieldMax L ≤ stateFieldMax (.CB, L, R) := by
    simpa [stateFieldMax] using (Nat.le_max_left (listFieldMax L) (listFieldMax R))
  have hRmax : listFieldMax R ≤ stateFieldMax (.CB, L, R) := by
    simpa [stateFieldMax] using (Nat.le_max_right (listFieldMax L) (listFieldMax R))
  have hInitial : listCounterSum L + listCounterSum R ≤
      94 * stateFieldMax (.CB, L, R) := by
    calc
      listCounterSum L + listCounterSum R ≤
          L.length * listFieldMax L + R.length * listFieldMax R := Nat.add_le_add hLsum hRsum
      _ ≤ L.length * stateFieldMax (.CB, L, R) + R.length * stateFieldMax (.CB, L, R) :=
        Nat.add_le_add (Nat.mul_le_mul_left L.length hLmax) (Nat.mul_le_mul_left R.length hRmax)
      _ = (L.length + R.length) * stateFieldMax (.CB, L, R) := by rw [Nat.add_mul]
      _ ≤ 94 * stateFieldMax (.CB, L, R) := Nat.mul_le_mul_right _ hT
  have hSweep := sweepCB_counter_sum_bound L R
  have hRlen : R.length ≤ 94 := by omega
  have hFuel : 4 * R.length ≤ 376 := by omega
  omega

#print axioms sweepCB_counter_sum_bound
#print axioms sweepCB_counter_sum_le_94M376



/-!
## BB sweep repeat-counter accounting

The BB sweep is the left/right dual accounting argument. Its recursive
branches consume one left token; bumping the right stack does not increase
counter sum; eatB1/eatB2/eatB12R add at most four; and peelTok does not
increase counter sum. Thus the BB sweep adds at most four times the left
token count.
-/

theorem eatB2_counter_sum_le (k : Nat) (xs : List SymTok) :
    listCounterSum (eatB2 k xs) ≤ k + listCounterSum xs + 4 := by
  simpa [eatB2] using
    (eatFuel_counter_sum_le [.item (.run 0), .item (.run 1), .item (.run 1)] .rep2 getRep2
      (by simp [listCounterSum, tokCounterSum]) (by intro n; simp [tokCounterSum])
      getRep2_counter 4 k xs)

theorem eatB12R_counter_sum_le (k : Nat) (xs : List SymTok) :
    listCounterSum (eatB12R k xs) ≤ k + listCounterSum xs + 4 := by
  simpa [eatB12R] using
    (eatFuel_counter_sum_le [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1)] .rep12 getRep12
      (by simp [listCounterSum, tokCounterSum]) (by intro n; simp [tokCounterSum])
      getRep12_counter 4 k xs)

theorem peelTok_counter_sum_le (t : SymTok) (xs : List SymTok) :
    listCounterSum (peelTok t xs) ≤ tokCounterSum t + listCounterSum xs := by
  cases t with
  | item x => simp [peelTok, tokCounterSum]
  | repB1 k =>
    cases k with
    | zero => simp [peelTok, tokCounterSum]
    | succ k =>
      cases k with
      | zero => simp [peelTok, tokCounterSum]
      | succ k => simp [peelTok, tokCounterSum, strictNat_eq] <;> omega
  | rep2 p =>
    cases p with
    | zero => simp [peelTok, tokCounterSum]
    | succ p =>
      cases p with
      | zero => simp [peelTok, tokCounterSum]
      | succ p => simp [peelTok, tokCounterSum, strictNat_eq] <;> omega
  | rep12 m =>
    cases m with
    | zero => simp [peelTok, tokCounterSum]
    | succ m =>
      cases m with
      | zero => simp [peelTok, tokCounterSum]
      | succ m => simp [peelTok, tokCounterSum, strictNat_eq] <;> omega

def symStateCounterSum (s : SymMode × List SymTok × List SymTok) : Nat :=
  listCounterSum s.2.1 + listCounterSum s.2.2

theorem stepElemBB_counter_sum_le (L R : List SymTok) :
    symStateCounterSum (stepElemBB L R) ≤ listCounterSum L + listCounterSum R := by
  have hR := bumpSymR_counter_sum_le R
  cases L with
  | nil =>
    simp [stepElemBB, strictList_eq, symStateCounterSum, listCounterSum]
    exact hR
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        have hR' := Nat.add_le_add_left hR (listCounterSum L1)
        simpa [stepElemBB, strictList_eq, symStateCounterSum, listCounterSum, tokCounterSum] using hR'
      | run d =>
        cases d with
        | zero => simp [stepElemBB, symStateCounterSum, listCounterSum, tokCounterSum]
        | succ d =>
          cases d with
          | zero =>
            simp [stepElemBB, strictList_eq, symStateCounterSum, listCounterSum, tokCounterSum]
            exact hR
          | succ d =>
            cases d with
            | zero =>
              simp [stepElemBB, strictList_eq, symStateCounterSum, listCounterSum, tokCounterSum]
              exact hR
            | succ d =>
              have hR' := Nat.add_le_add_left hR (listCounterSum L1)
              simpa [stepElemBB, strictList_eq, strictNat_eq,
                symStateCounterSum, listCounterSum, tokCounterSum] using hR'
    | repB1 k => simp [stepElemBB, symStateCounterSum, listCounterSum, tokCounterSum]
    | rep2 p => simp [stepElemBB, symStateCounterSum, listCounterSum, tokCounterSum]
    | rep12 m => simp [stepElemBB, symStateCounterSum, listCounterSum, tokCounterSum]

theorem sweepBB_counter_sum_bound (L R : List SymTok) :
    symStateCounterSum (sweepBB L R) ≤
      listCounterSum L + listCounterSum R + 4 * L.length := by
  generalize hn : L.length = n
  induction n using Nat.strongRecOn generalizing L R with
  | ind n ih =>
    have hlen : L.length = n := hn
    cases L with
    | nil =>
      have h := stepElemBB_counter_sum_le [] R
      calc
        symStateCounterSum (sweepBB [] R) ≤ listCounterSum [] + listCounterSum R := by
          simpa [sweepBB, symStateCounterSum] using h
        _ ≤ listCounterSum [] + listCounterSum R + 4 * n := by omega
    | cons t L1 =>
      simp at hlen hn
      have hrec (R' : List SymTok) :
          symStateCounterSum (sweepBB L1 R') ≤
            listCounterSum L1 + listCounterSum R' + 4 * L1.length :=
        ih L1.length (by omega) L1 R' rfl
      cases t with
      | item x =>
        cases x with
        | zero =>
          have h := stepElemBB_counter_sum_le (.item .zero :: L1) R
          calc
            symStateCounterSum (sweepBB (.item .zero :: L1) R) ≤
                listCounterSum (.item .zero :: L1) + listCounterSum R := by simpa [sweepBB] using h
            _ ≤ listCounterSum (.item .zero :: L1) + listCounterSum R + 4 * n := by omega
        | run d =>
          cases d with
          | zero =>
            calc
              symStateCounterSum (sweepBB (.item (.run 0) :: L1) R) =
                  symStateCounterSum (sweepBB L1 (.item (.run 0) :: R)) := by simp [sweepBB]
              _ ≤ listCounterSum L1 + listCounterSum (.item (.run 0) :: R) + 4 * L1.length :=
                hrec (.item (.run 0) :: R)
              _ ≤ listCounterSum (.item (.run 0) :: L1) + listCounterSum R + 4 * n := by
                simp [listCounterSum, tokCounterSum]
                omega
          | succ d =>
            cases d with
            | zero =>
              have hB := bumpSymR_counter_sum_le R
              calc
                symStateCounterSum (sweepBB (.item (.run 1) :: L1) R) =
                    symStateCounterSum (sweepBB L1 (.item (.run 0) :: bumpSymR R)) := by
                  simp [sweepBB, strictList_eq]
                _ ≤ listCounterSum L1 + listCounterSum (.item (.run 0) :: bumpSymR R) + 4 * L1.length :=
                  hrec (.item (.run 0) :: bumpSymR R)
                _ ≤ listCounterSum (.item (.run 1) :: L1) + listCounterSum R + 4 * n := by
                  simp [listCounterSum, tokCounterSum]
                  omega
            | succ d =>
              have h := stepElemBB_counter_sum_le (.item (.run (d+2)) :: L1) R
              calc
                symStateCounterSum (sweepBB (.item (.run (d+2)) :: L1) R) =
                    symStateCounterSum (stepElemBB (.item (.run (d+2)) :: L1) R) := by
                  simp [sweepBB, strictNat_eq]
                _ ≤ listCounterSum (.item (.run (d+2)) :: L1) + listCounterSum R := h
                _ ≤ listCounterSum (.item (.run (d+2)) :: L1) + listCounterSum R + 4 * n := by omega
      | repB1 k =>
        have hEat := eatB1_counter_sum_le k R
        calc
          symStateCounterSum (sweepBB (.repB1 k :: L1) R) =
              symStateCounterSum (sweepBB L1 (eatB1 k R)) := by simp [sweepBB, strictList_eq]
          _ ≤ listCounterSum L1 + listCounterSum (eatB1 k R) + 4 * L1.length :=
            hrec (eatB1 k R)
          _ ≤ listCounterSum (.repB1 k :: L1) + listCounterSum R + 4 * n := by
            simp [listCounterSum, tokCounterSum]
            omega
      | rep2 p =>
        cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
        | some R2 =>
          have hprefix := stripPrefixSym_some _ R R2 hs
          have hEat := eatB2_counter_sum_le p R2
          calc
            symStateCounterSum (sweepBB (.rep2 p :: L1) R) =
                symStateCounterSum (sweepBB L1 (.item (.run 0) :: .item (.run 1) :: eatB2 p R2)) := by
              simp [sweepBB, hs, strictList_eq]
            _ ≤ listCounterSum L1 + listCounterSum (.item (.run 0) :: .item (.run 1) :: eatB2 p R2) + 4 * L1.length :=
              hrec (.item (.run 0) :: .item (.run 1) :: eatB2 p R2)
            _ ≤ listCounterSum (.rep2 p :: L1) + listCounterSum R + 4 * n := by
              rw [hprefix, listCounterSum_append] at *
              simp [listCounterSum, tokCounterSum]
              omega
        | none =>
          have hPeel := peelTok_counter_sum_le (.rep2 p) L1
          have hStep := stepElemBB_counter_sum_le (peelTok (.rep2 p) L1) R
          calc
            symStateCounterSum (sweepBB (.rep2 p :: L1) R) =
                symStateCounterSum (stepElemBB (peelTok (.rep2 p) L1) R) := by
              simp [sweepBB, hs, strictList_eq]
            _ ≤ listCounterSum (peelTok (.rep2 p) L1) + listCounterSum R := hStep
            _ ≤ listCounterSum (.rep2 p :: L1) + listCounterSum R := by
              simp [listCounterSum, tokCounterSum] at hPeel ⊢
              omega
            _ ≤ listCounterSum (.rep2 p :: L1) + listCounterSum R + 4 * n := by omega
      | rep12 m =>
        cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
        | some R2 =>
          have hprefix := stripPrefixSym_some _ R R2 hs
          have hEat := eatB12R_counter_sum_le m R2
          calc
            symStateCounterSum (sweepBB (.rep12 m :: L1) R) =
                symStateCounterSum (sweepBB L1 (.item (.run 0) :: .item (.run 1) :: eatB12R m R2)) := by
              simp [sweepBB, hs, strictList_eq]
            _ ≤ listCounterSum L1 + listCounterSum (.item (.run 0) :: .item (.run 1) :: eatB12R m R2) + 4 * L1.length :=
              hrec (.item (.run 0) :: .item (.run 1) :: eatB12R m R2)
            _ ≤ listCounterSum (.rep12 m :: L1) + listCounterSum R + 4 * n := by
              rw [hprefix, listCounterSum_append] at *
              simp [listCounterSum, tokCounterSum]
              omega
        | none =>
          have hPeel := peelTok_counter_sum_le (.rep12 m) L1
          have hStep := stepElemBB_counter_sum_le (peelTok (.rep12 m) L1) R
          calc
            symStateCounterSum (sweepBB (.rep12 m :: L1) R) =
                symStateCounterSum (stepElemBB (peelTok (.rep12 m) L1) R) := by
              simp [sweepBB, hs, strictList_eq]
            _ ≤ listCounterSum (peelTok (.rep12 m) L1) + listCounterSum R := hStep
            _ ≤ listCounterSum (.rep12 m :: L1) + listCounterSum R := by
              simp [listCounterSum, tokCounterSum] at hPeel ⊢
              omega
            _ ≤ listCounterSum (.rep12 m :: L1) + listCounterSum R + 4 * n := by omega

theorem sweepBB_counter_sum_le_570M2280 (L R : List SymTok)
    (hT : L.length + R.length ≤ 570) :
    symStateCounterSum (sweepBB L R) ≤ 570 * stateFieldMax (.BB, L, R) + 2280 := by
  have hLsum := listCounterSum_le_length_mul_fieldMax L
  have hRsum := listCounterSum_le_length_mul_fieldMax R
  have hLmax : listFieldMax L ≤ stateFieldMax (.BB, L, R) := by
    simpa [stateFieldMax] using (Nat.le_max_left (listFieldMax L) (listFieldMax R))
  have hRmax : listFieldMax R ≤ stateFieldMax (.BB, L, R) := by
    simpa [stateFieldMax] using (Nat.le_max_right (listFieldMax L) (listFieldMax R))
  have hInitial : listCounterSum L + listCounterSum R ≤
      570 * stateFieldMax (.BB, L, R) := by
    calc
      listCounterSum L + listCounterSum R ≤
          L.length * listFieldMax L + R.length * listFieldMax R := Nat.add_le_add hLsum hRsum
      _ ≤ L.length * stateFieldMax (.BB, L, R) + R.length * stateFieldMax (.BB, L, R) :=
        Nat.add_le_add (Nat.mul_le_mul_left L.length hLmax) (Nat.mul_le_mul_left R.length hRmax)
      _ = (L.length + R.length) * stateFieldMax (.BB, L, R) := by rw [Nat.add_mul]
      _ ≤ 570 * stateFieldMax (.BB, L, R) := Nat.mul_le_mul_right _ hT
  have hSweep := sweepBB_counter_sum_bound L R
  have hLlen : L.length ≤ 570 := by omega
  have hFuel : 4 * L.length ≤ 2280 := by omega
  omega

#print axioms sweepBB_counter_sum_bound
#print axioms sweepBB_counter_sum_le_570M2280



/-- Compose the 94-token CB sweep/fallback bound with the 570-token BB sweep bound. -/
theorem cb_fallback_then_bb_counter_sum (L R : List SymTok)
    (hT : L.length + R.length ≤ 94)
    (hBB : (stepElemCB (sweepCB L R).1 (sweepCB L R).2).1 = .BB) :
    symStateCounterSum (sweepBB
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2) ≤
      570 * stateFieldMax (.BB,
        (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1,
        (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2) + 2280 := by
  have h570 := stepElemCB_after_sweep_570 L R hT hBB
  have h570' :
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1.length +
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2.length ≤ 570 := by
    simpa [symPairLen] using h570
  exact sweepBB_counter_sum_le_570M2280 _ _ h570'

#print axioms cb_fallback_then_bb_counter_sum



theorem stepElemCB_BB_counter_sum_le (L R : List SymTok)
    (hmode : (stepElemCB L R).1 = .BB) :
    symPairCounterSum ((stepElemCB L R).2.1, (stepElemCB L R).2.2) ≤
      listCounterSum L + listCounterSum R := by
  cases R with
  | nil => simp_all [stepElemCB, strictList_eq]
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero => simp_all [stepElemCB, strictList_eq]
      | run d =>
        cases d with
        | zero =>
          cases R1 with
          | nil =>
            have hB := bumpSymL_counter_sum_le L
            simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairCounterSum, listCounterSum, tokCounterSum]
            omega
          | cons t2 R2 =>
            cases t2 with
            | item y =>
              cases y with
              | zero =>
                have hB := bumpSymL_counter_sum_le L
                simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairCounterSum, listCounterSum, tokCounterSum]
                omega
              | run d2 =>
                cases d2 with
                | zero =>
                  have hB := bumpSymL_counter_sum_le L
                  simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairCounterSum, listCounterSum, tokCounterSum]
                  omega
                | succ d2 => simp_all [stepElemCB, stepElemCB_run0, strictList_eq]
            | repB1 k => simp_all [stepElemCB, stepElemCB_run0, strictList_eq]
            | rep2 p => simp_all [stepElemCB, stepElemCB_run0, strictList_eq]
            | rep12 m => simp_all [stepElemCB, stepElemCB_run0, strictList_eq]
        | succ d =>
          cases d with
          | zero => simp_all [stepElemCB, strictList_eq]
          | succ d =>
            cases d with
            | zero =>
              have hB := bumpSymL_counter_sum_le L
              simp [stepElemCB, strictList_eq, symPairCounterSum, listCounterSum, tokCounterSum]
              omega
            | succ d =>
              have hB := bumpSymL_counter_sum_le L
              simp [stepElemCB, strictList_eq, symPairCounterSum, listCounterSum, tokCounterSum]
              omega
    | repB1 k => simp_all [stepElemCB, strictList_eq]
    | rep2 p => simp_all [stepElemCB, strictList_eq]
    | rep12 m => simp_all [stepElemCB, strictList_eq]

/-- The whole CB-sweep / BB-fallback / BB-sweep path has a counter-sum
    bound in terms of the original CB input maximum field. -/
theorem cb_fallback_then_bb_counter_sum_94M2656 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94)
    (hBB : (stepElemCB (sweepCB L R).1 (sweepCB L R).2).1 = .BB) :
    symStateCounterSum (sweepBB
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2) ≤
      94 * stateFieldMax (.CB, L, R) + 2656 := by
  let L2 := (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1
  let R2 := (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2
  have hSweep := sweepCB_counter_sum_le_94M376 L R hT
  have hElem := stepElemCB_BB_counter_sum_le (sweepCB L R).1 (sweepCB L R).2 hBB
  have hBBsum : listCounterSum L2 + listCounterSum R2 ≤
      94 * stateFieldMax (.CB, L, R) + 376 := by
    simpa [L2, R2, symPairCounterSum] using Nat.le_trans hElem hSweep
  have h570 := stepElemCB_after_sweep_570 L R hT hBB
  have h570' : L2.length + R2.length ≤ 570 := by
    simpa [L2, R2, symPairLen] using h570
  have hBBsweep := sweepBB_counter_sum_bound L2 R2
  calc
    symStateCounterSum (sweepBB L2 R2) ≤ listCounterSum L2 + listCounterSum R2 + 4 * L2.length := hBBsweep
    _ ≤ 94 * stateFieldMax (.CB, L, R) + 376 + 4 * 570 := by omega
    _ = 94 * stateFieldMax (.CB, L, R) + 2656 := by omega

#print axioms stepElemCB_BB_counter_sum_le
#print axioms cb_fallback_then_bb_counter_sum_94M2656



theorem sweepCB_counter_sum_le_pow9 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94) :
    symPairCounterSum (sweepCB L R) ≤ 2^9 * (stateFieldMax (.CB, L, R) + 1) := by
  have h := sweepCB_counter_sum_le_94M376 L R hT
  omega

theorem cb_fallback_then_bb_counter_sum_le_pow12 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94)
    (hBB : (stepElemCB (sweepCB L R).1 (sweepCB L R).2).1 = .BB) :
    symStateCounterSum (sweepBB
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2) ≤
      2^12 * (stateFieldMax (.CB, L, R) + 1) := by
  have h := cb_fallback_then_bb_counter_sum_94M2656 L R hT hBB
  omega

#print axioms sweepCB_counter_sum_le_pow9
#print axioms cb_fallback_then_bb_counter_sum_le_pow12



/-!
## Numeric-field sum groundwork

Unlike repeat-counter sum, numeric-field sum also counts literal run lengths.
The bump operations can increase this measure by at most three, while each
fuel-eat operation does not increase it because every matched block contains
at least one unit of literal run length. These lemmas are groundwork for a
direct maximum-field bound through the sweeps; that sweep-level theorem is
not claimed here.
-/

def tokNumSum : SymTok → Nat
  | .item .zero => 0
  | .item (.run d) => d
  | .repB1 k => k
  | .rep2 p => p
  | .rep12 m => m

def listNumSum : List SymTok → Nat
  | [] => 0
  | t :: xs => tokNumSum t + listNumSum xs

theorem listNumSum_append (xs ys : List SymTok) :
    listNumSum (xs ++ ys) = listNumSum xs + listNumSum ys := by
  induction xs with
  | nil => simp [listNumSum]
  | cons t xs ih => simp [listNumSum, ih, Nat.add_assoc]

theorem bumpSymL_num_sum_le (xs : List SymTok) :
    listNumSum (bumpSymL xs) ≤ listNumSum xs + 3 := by
  induction xs with
  | nil => simp [bumpSymL, listNumSum, tokNumSum]
  | cons t xs ih =>
    cases t with
    | item x => cases x <;> simp [bumpSymL, listNumSum, tokNumSum] <;> omega
    | repB1 k =>
      cases k with
      | zero => simpa [bumpSymL, listNumSum, tokNumSum] using Nat.le_trans ih (by omega)
      | succ k =>
        cases k with
        | zero => simp [bumpSymL, listNumSum, tokNumSum] <;> omega
        | succ k => simp [bumpSymL, listNumSum, tokNumSum, strictNat_eq] <;> omega
    | rep2 p =>
      cases p with
      | zero => simpa [bumpSymL, listNumSum, tokNumSum] using Nat.le_trans ih (by omega)
      | succ p => simp [bumpSymL, listNumSum, tokNumSum, strictNat_eq] <;> omega
    | rep12 m =>
      cases m with
      | zero => simpa [bumpSymL, listNumSum, tokNumSum] using Nat.le_trans ih (by omega)
      | succ m => simp [bumpSymL, listNumSum, tokNumSum, strictNat_eq] <;> omega

theorem bumpSymR_num_sum_le (xs : List SymTok) :
    listNumSum (bumpSymR xs) ≤ listNumSum xs + 3 := by
  induction xs with
  | nil => simp [bumpSymR, listNumSum, tokNumSum]
  | cons t xs ih =>
    cases t with
    | item x => cases x <;> simp [bumpSymR, listNumSum, tokNumSum] <;> omega
    | repB1 k =>
      cases k with
      | zero => simpa [bumpSymR, listNumSum, tokNumSum] using Nat.le_trans ih (by omega)
      | succ k =>
        cases k with
        | zero => simp [bumpSymR, listNumSum, tokNumSum] <;> omega
        | succ k => simp [bumpSymR, listNumSum, tokNumSum, strictNat_eq] <;> omega
    | rep2 p =>
      cases p with
      | zero => simpa [bumpSymR, listNumSum, tokNumSum] using Nat.le_trans ih (by omega)
      | succ p => simp [bumpSymR, listNumSum, tokNumSum, strictNat_eq] <;> omega
    | rep12 m =>
      cases m with
      | zero => simpa [bumpSymR, listNumSum, tokNumSum] using Nat.le_trans ih (by omega)
      | succ m => simp [bumpSymR, listNumSum, tokNumSum, strictNat_eq] <;> omega

theorem eatStep_num_sum_le (blk : List SymTok) (getRep : SymTok → Option Nat)
    (hblk : 1 ≤ listNumSum blk)
    (hget : ∀ x k2, getRep x = some k2 → tokNumSum x = k2)
    (k k' : Nat) (xs rest : List SymTok)
    (h : eatStep blk getRep k xs = some (k', rest)) :
    k' + listNumSum rest ≤ k + listNumSum xs := by
  cases xs with
  | nil => simp [eatStep] at h
  | cons x xs1 =>
    unfold eatStep at h
    cases hg : getRep x with
    | some k2 =>
      simp [hg] at h
      rcases h with ⟨rfl, rfl⟩
      simp [listNumSum, hget x k2 hg]
      omega
    | none =>
      cases hs : stripPrefixSym blk (x :: xs1) with
      | none => simp [hg, hs] at h
      | some rest2 =>
        simp [hg, hs] at h
        rcases h with ⟨rfl, rfl⟩
        have hprefix := stripPrefixSym_some blk (x :: xs1) rest2 hs
        rw [hprefix, listNumSum_append]
        omega

theorem eatFuel_num_sum_le (blk : List SymTok) (mkRep : Nat → SymTok)
    (getRep : SymTok → Option Nat)
    (hblk : 1 ≤ listNumSum blk)
    (hMk : ∀ k, tokNumSum (mkRep k) = k)
    (hget : ∀ x k2, getRep x = some k2 → tokNumSum x = k2)
    (fuel k : Nat) (xs : List SymTok) :
    listNumSum (eatFuel blk mkRep getRep fuel k xs) ≤ k + listNumSum xs := by
  induction fuel generalizing k xs with
  | zero => simp [eatFuel, listNumSum, hMk]
  | succ fuel ih =>
    cases hs : eatStep blk getRep k xs with
    | none => simp [eatFuel, hs, listNumSum, hMk]
    | some pair =>
      rcases pair with ⟨k', rest⟩
      have hstep := eatStep_num_sum_le blk getRep hblk hget k k' xs rest hs
      have hrec := ih k' rest
      simp [eatFuel, hs, strictNat_eq]
      exact Nat.le_trans hrec hstep

theorem getRepB1_num (x : SymTok) (k : Nat) (h : getRepB1 x = some k) :
    tokNumSum x = k := by
  cases x with
  | item x => simp [getRepB1] at h
  | repB1 n => simp [getRepB1] at h; simpa [tokNumSum] using h
  | rep2 p => simp [getRepB1] at h
  | rep12 m => simp [getRepB1] at h

theorem getRep2_num (x : SymTok) (k : Nat) (h : getRep2 x = some k) :
    tokNumSum x = k := by
  cases x with
  | item x => simp [getRep2] at h
  | repB1 n => simp [getRep2] at h
  | rep2 p => simp [getRep2] at h; simpa [tokNumSum] using h
  | rep12 m => simp [getRep2] at h

theorem getRep12_num (x : SymTok) (k : Nat) (h : getRep12 x = some k) :
    tokNumSum x = k := by
  cases x with
  | item x => simp [getRep12] at h
  | repB1 n => simp [getRep12] at h
  | rep2 p => simp [getRep12] at h
  | rep12 m => simp [getRep12] at h; simpa [tokNumSum] using h

theorem eatB1_num_sum_le (k : Nat) (xs : List SymTok) :
    listNumSum (eatB1 k xs) ≤ k + listNumSum xs := by
  simpa [eatB1] using
    (eatFuel_num_sum_le [.item (.run 0), .item (.run 1)] .repB1 getRepB1
      (by simp [listNumSum, tokNumSum]) (by intro n; simp [tokNumSum])
      getRepB1_num 4 k xs)

theorem eatC2_num_sum_le (k : Nat) (xs : List SymTok) :
    listNumSum (eatC2 k xs) ≤ k + listNumSum xs := by
  simpa [eatC2] using
    (eatFuel_num_sum_le [.item (.run 1), .item (.run 0), .item (.run 1)] .rep2 getRep2
      (by simp [listNumSum, tokNumSum]) (by intro n; simp [tokNumSum])
      getRep2_num 4 k xs)

theorem eatC12_num_sum_le (k : Nat) (xs : List SymTok) :
    listNumSum (eatC12 k xs) ≤ k + listNumSum xs := by
  simpa [eatC12] using
    (eatFuel_num_sum_le [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] .rep12 getRep12
      (by simp [listNumSum, tokNumSum]) (by intro n; simp [tokNumSum])
      getRep12_num 4 k xs)


#print axioms bumpSymL_num_sum_le
#print axioms bumpSymR_num_sum_le
#print axioms eatFuel_num_sum_le
#print axioms eatB1_num_sum_le
#print axioms eatC2_num_sum_le
#print axioms eatC12_num_sum_le


def symPairNumSum (p : List SymTok × List SymTok) : Nat :=
  listNumSum p.1 + listNumSum p.2

theorem sweepCB_num_sum_bound (L R : List SymTok) :
    symPairNumSum (sweepCB L R) ≤
      listNumSum L + listNumSum R + 3 * R.length := by
  generalize hn : R.length = n
  induction n using Nat.strongRecOn generalizing R L with
  | ind n ih =>
    have hlen : R.length = n := hn
    cases R with
    | nil => simp [symPairNumSum, sweepCB, listNumSum] <;> omega
    | cons t R1 =>
      simp at hlen
      have hrecR1 (L' : List SymTok) :
          symPairNumSum (sweepCB L' R1) ≤
            listNumSum L' + listNumSum R1 + 3 * R1.length :=
        ih R1.length (by omega) L' R1 rfl
      cases t with
      | item x =>
        cases x with
        | zero => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
        | run d =>
          cases d with
          | zero =>
            cases R1 with
            | nil => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
            | cons t2 R2 =>
              simp at hlen
              have hrecR2 (L' : List SymTok) :
                  symPairNumSum (sweepCB L' R2) ≤
                    listNumSum L' + listNumSum R2 + 3 * R2.length :=
                ih R2.length (by omega) L' R2 rfl
              cases t2 with
              | item y =>
                cases y with
                | zero => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
                | run d2 =>
                  cases d2 with
                  | zero => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
                  | succ d2 =>
                    cases d2 with
                    | zero =>
                      have hB := bumpSymL_num_sum_le L
                      have hEq : R2.length + 2 = n := by omega
                      calc
                        symPairNumSum (sweepCB L (.item (.run 0) :: .item (.run 1) :: R2)) =
                            symPairNumSum (sweepCB (.item (.run 0) :: .item (.run 0) :: bumpSymL L) R2) := by
                          simp [sweepCB, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
                        _ ≤ listNumSum (.item (.run 0) :: .item (.run 0) :: bumpSymL L) +
                              listNumSum R2 + 3 * R2.length :=
                          hrecR2 (.item (.run 0) :: .item (.run 0) :: bumpSymL L)
                        _ ≤ listNumSum L + listNumSum (.item (.run 0) :: .item (.run 1) :: R2) + 3 * n := by
                          simp [listNumSum, tokNumSum]
                          omega
                    | succ d2 => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
              | repB1 k => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
              | rep2 p => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
              | rep12 m => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
          | succ d =>
            cases d with
            | zero =>
              have hB := bumpSymL_num_sum_le L
              have hEq : R1.length + 1 = n := by omega
              calc
                symPairNumSum (sweepCB L (.item (.run 1) :: R1)) =
                    symPairNumSum (sweepCB (.item (.run 0) :: bumpSymL L) R1) := by
                  simp [sweepCB, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
                _ ≤ listNumSum (.item (.run 0) :: bumpSymL L) + listNumSum R1 + 3 * R1.length :=
                  hrecR1 (.item (.run 0) :: bumpSymL L)
                _ ≤ listNumSum L + listNumSum (.item (.run 1) :: R1) + 3 * n := by
                  simp [listNumSum, tokNumSum]
                  omega
            | succ d => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
      | repB1 k =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairNumSum, sweepCB, hs, listNumSum, tokNumSum] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatB1_num_sum_le k L1
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairNumSum (sweepCB L (.repB1 k :: R1)) =
                symPairNumSum (sweepCB (.item (.run 0) :: eatB1 k L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
            _ ≤ listNumSum (.item (.run 0) :: eatB1 k L1) + listNumSum R1 + 3 * R1.length :=
              hrecR1 (.item (.run 0) :: eatB1 k L1)
            _ ≤ listNumSum L + listNumSum (.repB1 k :: R1) + 3 * n := by
              rw [hprefix, listNumSum_append] at *
              simp [listNumSum, tokNumSum]
              omega
      | rep2 p =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairNumSum, sweepCB, hs, listNumSum, tokNumSum] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatC2_num_sum_le p L1
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairNumSum (sweepCB L (.rep2 p :: R1)) =
                symPairNumSum (sweepCB (.item (.run 0) :: eatC2 p L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
            _ ≤ listNumSum (.item (.run 0) :: eatC2 p L1) + listNumSum R1 + 3 * R1.length :=
              hrecR1 (.item (.run 0) :: eatC2 p L1)
            _ ≤ listNumSum L + listNumSum (.rep2 p :: R1) + 3 * n := by
              rw [hprefix, listNumSum_append] at *
              simp [listNumSum, tokNumSum]
              omega
      | rep12 m =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairNumSum, sweepCB, hs, listNumSum, tokNumSum] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatC12_num_sum_le m L1
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairNumSum (sweepCB L (.rep12 m :: R1)) =
                symPairNumSum (sweepCB (.item (.run 0) :: eatC12 m L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
            _ ≤ listNumSum (.item (.run 0) :: eatC12 m L1) + listNumSum R1 + 3 * R1.length :=
              hrecR1 (.item (.run 0) :: eatC12 m L1)
            _ ≤ listNumSum L + listNumSum (.rep12 m :: R1) + 3 * n := by
              rw [hprefix, listNumSum_append] at *
              simp [listNumSum, tokNumSum]
              omega


theorem tokNumSum_eq_tokFieldMax (t : SymTok) : tokNumSum t = tokFieldMax t := by
  cases t with
  | item x => cases x <;> rfl
  | repB1 k => rfl
  | rep2 p => rfl
  | rep12 m => rfl

theorem listNumSum_le_length_mul_fieldMax (xs : List SymTok) :
    listNumSum xs ≤ xs.length * listFieldMax xs := by
  induction xs with
  | nil => simp [listNumSum, listFieldMax]
  | cons t xs ih =>
    have ht' : tokNumSum t ≤ listFieldMax (t :: xs) := by
      calc
        tokNumSum t = tokFieldMax t := tokNumSum_eq_tokFieldMax t
        _ ≤ max (tokFieldMax t) (listFieldMax xs) := Nat.le_max_left _ _
        _ = listFieldMax (t :: xs) := by simp [listFieldMax_cons]
    have htail : listFieldMax xs ≤ listFieldMax (t :: xs) := by
      simpa [listFieldMax_cons] using (Nat.le_max_right (tokFieldMax t) (listFieldMax xs))
    have htail' : listNumSum xs ≤ xs.length * listFieldMax (t :: xs) :=
      Nat.le_trans ih (Nat.mul_le_mul_left xs.length htail)
    calc
      listNumSum (t :: xs) = tokNumSum t + listNumSum xs := rfl
      _ ≤ listFieldMax (t :: xs) + xs.length * listFieldMax (t :: xs) := Nat.add_le_add ht' htail'
      _ = (xs.length + 1) * listFieldMax (t :: xs) := by rw [Nat.add_mul]<;> omega

theorem listFieldMax_le_listNumSum (xs : List SymTok) :
    listFieldMax xs ≤ listNumSum xs := by
  induction xs with
  | nil => simp [listFieldMax, listNumSum]
  | cons t xs ih =>
    rw [listFieldMax_cons, listNumSum]
    rw [tokNumSum_eq_tokFieldMax t]
    simp only [Nat.max_le]
    constructor <;> omega

theorem sweepCB_num_sum_le_94M282 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94) :
    symPairNumSum (sweepCB L R) ≤ 94 * stateFieldMax (.CB, L, R) + 282 := by
  have hLsum := listNumSum_le_length_mul_fieldMax L
  have hRsum := listNumSum_le_length_mul_fieldMax R
  have hLmax : listFieldMax L ≤ stateFieldMax (.CB, L, R) := by
    simpa [stateFieldMax] using (Nat.le_max_left (listFieldMax L) (listFieldMax R))
  have hRmax : listFieldMax R ≤ stateFieldMax (.CB, L, R) := by
    simpa [stateFieldMax] using (Nat.le_max_right (listFieldMax L) (listFieldMax R))
  have hInitial : listNumSum L + listNumSum R ≤ 94 * stateFieldMax (.CB, L, R) := by
    calc
      listNumSum L + listNumSum R ≤ L.length * listFieldMax L + R.length * listFieldMax R := Nat.add_le_add hLsum hRsum
      _ ≤ L.length * stateFieldMax (.CB, L, R) + R.length * stateFieldMax (.CB, L, R) :=
        Nat.add_le_add (Nat.mul_le_mul_left L.length hLmax) (Nat.mul_le_mul_left R.length hRmax)
      _ = (L.length + R.length) * stateFieldMax (.CB, L, R) := by rw [Nat.add_mul]
      _ ≤ 94 * stateFieldMax (.CB, L, R) := Nat.mul_le_mul_right _ hT
  have hSweep := sweepCB_num_sum_bound L R
  have hRlen : R.length ≤ 94 := by omega
  have hGrowth : 3 * R.length ≤ 282 := by omega
  omega

theorem sweepCB_stateFieldMax_le_94M282 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94) :
    stateFieldMax (.CB, (sweepCB L R).1, (sweepCB L R).2) ≤
      94 * stateFieldMax (.CB, L, R) + 282 := by
  have hsum := sweepCB_num_sum_le_94M282 L R hT
  have hL := listFieldMax_le_listNumSum (sweepCB L R).1
  have hR := listFieldMax_le_listNumSum (sweepCB L R).2
  have hmax : stateFieldMax (.CB, (sweepCB L R).1, (sweepCB L R).2) ≤
      symPairNumSum (sweepCB L R) := by
    simp [stateFieldMax, symPairNumSum]
    omega
  exact Nat.le_trans hmax hsum

#print axioms sweepCB_num_sum_bound
#print axioms sweepCB_stateFieldMax_le_94M282

theorem stepElemCB_BB_num_sum_le (L R : List SymTok)
    (hmode : (stepElemCB L R).1 = .BB) :
    symPairNumSum ((stepElemCB L R).2.1, (stepElemCB L R).2.2) ≤
      listNumSum L + listNumSum R + 3 := by
  cases R with
  | nil => simp_all [stepElemCB, strictList_eq]
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero => simp_all [stepElemCB, strictList_eq]
      | run d =>
        cases d with
        | zero =>
          cases R1 with
          | nil =>
            have hB := bumpSymL_num_sum_le L
            simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
            omega
          | cons t2 R2 =>
            cases t2 with
            | item y =>
              cases y with
              | zero =>
                have hB := bumpSymL_num_sum_le L
                simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
                omega
              | run d2 =>
                cases d2 with
                | zero =>
                  have hB := bumpSymL_num_sum_le L
                  simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
                  omega
                | succ d2 => simp_all [stepElemCB, stepElemCB_run0, strictList_eq]
            | repB1 k => simp_all [stepElemCB, stepElemCB_run0, strictList_eq]
            | rep2 p => simp_all [stepElemCB, stepElemCB_run0, strictList_eq]
            | rep12 m => simp_all [stepElemCB, stepElemCB_run0, strictList_eq]
        | succ d =>
          cases d with
          | zero => simp_all [stepElemCB, strictList_eq]
          | succ d =>
            cases d with
            | zero =>
              have hB := bumpSymL_num_sum_le L
              simp [stepElemCB, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
              omega
            | succ d =>
              have hB := bumpSymL_num_sum_le L
              simp [stepElemCB, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
              omega
    | repB1 k => simp_all [stepElemCB, strictList_eq]
    | rep2 p => simp_all [stepElemCB, strictList_eq]
    | rep12 m => simp_all [stepElemCB, strictList_eq]


/-- The BB-sweep input maximum field is bounded in terms of the original
    CB input maximum field. -/
theorem cb_fallback_bb_input_field_max_le_94M285 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94)
    (hBB : (stepElemCB (sweepCB L R).1 (sweepCB L R).2).1 = .BB) :
    stateFieldMax (.BB,
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1,
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2) ≤
      94 * stateFieldMax (.CB, L, R) + 285 := by
  let L2 := (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1
  let R2 := (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2
  have hSweep := sweepCB_num_sum_le_94M282 L R hT
  have hElem := stepElemCB_BB_num_sum_le (sweepCB L R).1 (sweepCB L R).2 hBB
  have hSweep' :
      listNumSum (sweepCB L R).1 + listNumSum (sweepCB L R).2 + 3 ≤
        94 * stateFieldMax (.CB, L, R) + 285 := by
    have hS : listNumSum (sweepCB L R).1 + listNumSum (sweepCB L R).2 ≤
        94 * stateFieldMax (.CB, L, R) + 282 := by
      simpa [symPairNumSum] using hSweep
    omega
  have hsum : symPairNumSum (L2, R2) ≤ 94 * stateFieldMax (.CB, L, R) + 285 := by
    simpa [L2, R2, symPairNumSum] using Nat.le_trans hElem hSweep'
  have hL2 := listFieldMax_le_listNumSum L2
  have hR2 := listFieldMax_le_listNumSum R2
  have hmax : stateFieldMax (.BB, L2, R2) ≤ symPairNumSum (L2, R2) := by
    simp [stateFieldMax, symPairNumSum]
    omega
  simpa [L2, R2] using Nat.le_trans hmax hsum

#print axioms stepElemCB_BB_num_sum_le
#print axioms cb_fallback_bb_input_field_max_le_94M285



theorem cb_fallback_bb_input_field_max_le_pow9 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94)
    (hBB : (stepElemCB (sweepCB L R).1 (sweepCB L R).2).1 = .BB) :
    stateFieldMax (.BB,
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1,
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2) ≤
      2^9 * (stateFieldMax (.CB, L, R) + 1) := by
  have h := cb_fallback_bb_input_field_max_le_94M285 L R hT hBB
  omega

#print axioms cb_fallback_bb_input_field_max_le_pow9



theorem peelTok_num_sum_le (t : SymTok) (xs : List SymTok) :
    listNumSum (peelTok t xs) ≤ tokNumSum t + listNumSum xs + 2 := by
  cases t with
  | item x => simp [peelTok, tokNumSum, listNumSum]
  | repB1 k =>
    cases k with
    | zero => simp [peelTok, tokNumSum, listNumSum]
    | succ k =>
      cases k with
      | zero => simp [peelTok, tokNumSum, listNumSum]
      | succ k => simp [peelTok, tokNumSum, listNumSum, strictNat_eq] <;> omega
  | rep2 p =>
    cases p with
    | zero => simp [peelTok, tokNumSum, listNumSum]
    | succ p =>
      cases p with
      | zero => simp [peelTok, tokNumSum, listNumSum] <;> omega
      | succ p => simp [peelTok, tokNumSum, listNumSum, strictNat_eq] <;> omega
  | rep12 m =>
    cases m with
    | zero => simp [peelTok, tokNumSum, listNumSum]
    | succ m =>
      cases m with
      | zero => simp [peelTok, tokNumSum, listNumSum] <;> omega
      | succ m => simp [peelTok, tokNumSum, listNumSum, strictNat_eq] <;> omega

def symStateNumSum (s : SymMode × List SymTok × List SymTok) : Nat :=
  listNumSum s.2.1 + listNumSum s.2.2

theorem stepElemBB_num_sum_le (L R : List SymTok) :
    symStateNumSum (stepElemBB L R) ≤ listNumSum L + listNumSum R + 3 := by
  have hR := bumpSymR_num_sum_le R
  cases L with
  | nil =>
    simp [stepElemBB, strictList_eq, symStateNumSum, listNumSum]
    omega
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero => simp [stepElemBB, strictList_eq, symStateNumSum, listNumSum]<;> omega
      | run d =>
        cases d with
        | zero => simp [stepElemBB, symStateNumSum, listNumSum, tokNumSum]
        | succ d =>
          cases d with
          | zero => simp [stepElemBB, strictList_eq, symStateNumSum, listNumSum, tokNumSum]<;> omega
          | succ d =>
            cases d with
            | zero => simp [stepElemBB, strictList_eq, symStateNumSum, listNumSum, tokNumSum]<;> omega
            | succ d =>
              cases d with
              | zero => simp [stepElemBB, strictList_eq, symStateNumSum, listNumSum, tokNumSum]<;> omega
              | succ d => simp [stepElemBB, strictList_eq, strictNat_eq, symStateNumSum, listNumSum, tokNumSum]<;> omega
    | repB1 k => simp [stepElemBB, symStateNumSum, listNumSum, tokNumSum]
    | rep2 p => simp [stepElemBB, symStateNumSum, listNumSum, tokNumSum]
    | rep12 m => simp [stepElemBB, symStateNumSum, listNumSum, tokNumSum]

#print axioms peelTok_num_sum_le
#print axioms stepElemBB_num_sum_le


end BusyBeaver.SymRunAudit
