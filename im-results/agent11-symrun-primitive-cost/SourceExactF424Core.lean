/-
Exact original-machine primitive-step witnesses, extracted without alteration of proof bodies
from Agent 42's SymRunCostedStepPilot.lean (first source-defined exact-cost section).
Copyright/authorship of original lemmas remains with Agent 42; this isolated copy enables
a standalone Lean 4.36.0-rc2 original-Cryptids CI compile without the unrelated pilot
field-growth/bound code and SymRunTraceStats dependency. Edits: remove SymRunTraceStats import, split at local field-measure section,
close namespace, and import a lightweight byte-identical original F424 transition
table instead of all 18 expensive upstream halting checkpoint certificates.
Pinned source: google-deepmind/cryptids @ 3647718b5df22e1a61462dec0376bd204526285a.
-/
import SourceF424Machine

/-!
# F424 exact primitive-time pilot

This file is specific to the pinned F424 machine module above
(`google-deepmind/cryptids` commit
`3647718b5df22e1a61462dec0376bd204526285a`). Costs must be taken from
that module's `execute n` proofs. In particular, F424 has
`step_CB_run0_zero` and generic `step_BB_run1` at 3 steps; do not
import the different F289 cost table into this namespace.

The file is a draft until compiled against the exact imported upstream
modules under Lean 4.36.0-rc2.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution

open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine

/-- Totalized deterministic successor. The default branch is used only to
    make the function total; every use below carries an isSome proof. -/
def nextCfg (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  (step target_tm c).getD default

theorem step_eq_some_nextCfg (c : Cfg (Fin 2) (Fin 6))
    (hstep : (step target_tm c).isSome) :
    step target_tm c = some (nextCfg c) := by
  cases h : step target_tm c with
  | none => simp [h] at hstep
  | some c' => simp [nextCfg, h]

/-- Successor-indexed reachability avoids an unconstrained intermediate
    configuration metavariable in repeated primitive-step witnesses. -/
theorem reachesIn_step_left_succ {n : Nat} {c₁ c₃ : Cfg (Fin 2) (Fin 6)}
    (hstep : (step target_tm c₁).isSome)
    (hrest : ReachesIn target_tm n (nextCfg c₁) c₃) :
    ReachesIn target_tm (Nat.succ n) c₁ c₃ := by
  have hnext := step_eq_some_nextCfg c₁ hstep
  simpa only [Nat.add_one] using BusyBeaver.ReachesIn.step_left hnext hrest

macro "stepWithin" : tactic => `(tactic| (
  try simp only [isVarA_tm, ite_true, ite_false, dif_pos, dif_neg,
    BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, pow_succ_list, pow_zero_list,
    cons_append_list, nil_append_list, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head, default_tail,
    encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head, cons_one_encLeft_tail,
    encRight_cons_head, cons_one_encRight_tail, encM_cons_run_head, cons_one_encM_cons_run_tail]
  refine reachesIn_step_left_succ ?_ ?_
  · first
    | rfl
    | simp [step, BusyBeaver.init_nil, target_tm, target, machine,
        isVarA_tm, ite_true, ite_false, dif_pos, dif_neg,
        BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,
        pow_succ_list, pow_zero_list, cons_append_list, nil_append_list,
        listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
        Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head,
        default_tail, encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head,
        cons_one_encLeft_tail, encRight_cons_head, cons_one_encRight_tail,
        encM_cons_run_head, cons_one_encM_cons_run_tail]
  · simp only [nextCfg, step, BusyBeaver.init_nil, target_tm, target, machine, Option.getD_some,
      isVarA_tm, ite_true, ite_false, dif_pos, dif_neg,
      BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,
      pow_succ_list, pow_zero_list, cons_append_list, nil_append_list,
      listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head,
      default_tail, encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head,
      cons_one_encLeft_tail, encRight_cons_head, cons_one_encRight_tail,
      encM_cons_run_head, cons_one_encM_cons_run_tail]
))

macro "finishWithin" : tactic => `(tactic| (
  all_goals (
    change multiStep target_tm _ 0 = some _
    simp only [isVarA_tm, ite_true, ite_false, dif_pos, dif_neg,
      BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, pow_succ_list, pow_zero_list,
      cons_append_list, nil_append_list, listblank_append_cons, listblank_append_nil,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zero_cons_default, default_head,
      default_tail, enc1_nil, encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head,
      cons_one_encLeft_tail, encRight_cons_head, cons_one_encRight_tail, encM_cons_run_head,
      cons_one_encM_cons_run_tail, multiStep_zero]
    try rfl
  )
))

macro "executeWithin" n:num : tactic => `(tactic| (
  iterate $n stepWithin
  finishWithin
))

theorem step_BB_nil_exact (R : List MItem) :
    ReachesIn target_tm 1 (cfgBB target_tm [] R) (cfgCB target_tm [] (bumpM R)) := by
  unfold cfgBB cfgCB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  executeWithin 1

theorem step_BB_run0_exact (L1 R : List MItem) :
    ReachesIn target_tm 8 (cfgBB target_tm (.run 0 :: L1) R)
      (cfgBB target_tm L1 (.run 0 :: R)) := by
  unfold cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  executeWithin 8

theorem reachesIn_trans {m n : Nat} {c1 c2 c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : ReachesIn target_tm m c1 c2) (h2 : ReachesIn target_tm n c2 c3) :
    ReachesIn target_tm (m + n) c1 c3 := by
  unfold ReachesIn at *
  exact multiStep_trans h1 h2

/-- A bounded primitive-time reachability relation for this machine. -/
def ReachesWithin (B : Nat) (c c' : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ n, n ≤ B ∧ ReachesIn target_tm n c c'

theorem reachesWithin_mono {B1 B2 : Nat} {c c' : Cfg (Fin 2) (Fin 6)}
    (hB : B1 ≤ B2) (h : ReachesWithin B1 c c') : ReachesWithin B2 c c' := by
  rcases h with ⟨n, hn, hreach⟩
  exact ⟨n, le_trans hn hB, hreach⟩

theorem reachesWithin_trans {B1 B2 : Nat}
    {c1 c2 c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : ReachesWithin B1 c1 c2) (h2 : ReachesWithin B2 c2 c3) :
    ReachesWithin (B1 + B2) c1 c3 := by
  rcases h1 with ⟨m, hm, hreach1⟩
  rcases h2 with ⟨n, hn, hreach2⟩
  refine ⟨m + n, Nat.add_le_add hm hn, reachesIn_trans hreach1 hreach2⟩

theorem reachesWithin_of_exact {n B : Nat} {c c' : Cfg (Fin 2) (Fin 6)}
    (h : n ≤ B) (hreach : ReachesIn target_tm n c c') :
    ReachesWithin B c c' :=
  ⟨n, h, hreach⟩

theorem cyc_R_A_exact (k : Nat) (V s : ListBlank (Fin 2)) :
    ReachesIn target_tm (3 * k)
      (⟨some A, ⟨0, (0 : Fin 2) >> V, (([1] : List (Fin 2)) ^ k) +> s⟩⟩ :
        Cfg (Fin 2) (Fin 6))
      ⟨some A, ⟨0, (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ k) +> V), s⟩⟩ := by
  induction k generalizing V with
  | zero =>
      change multiStep target_tm _ 0 = some _
      simp only [multiStep_zero]
      rfl
  | succ k ih =>
      have h1 :
          ReachesIn target_tm 3
            (⟨some A, ⟨0, (0 : Fin 2) >> V, (([1] : List (Fin 2)) ^ (k + 1)) +> s⟩⟩ :
              Cfg (Fin 2) (Fin 6))
            ⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> V,
              (([1] : List (Fin 2)) ^ k) +> s⟩⟩ := by
        executeWithin 3
      have h2 := ih ((0 : Fin 2) >> V)
      have h12 := reachesIn_trans h1 h2
      have h_eq :
          (([0] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> V) =
            (([0] : List (Fin 2)) ^ (k + 1)) +> V := by
        rw [zeros_append_cons_zero k V]
        simp only [pow_succ_list, cons_append_list, nil_append_list,
          listblank_append_cons]
      rw [h_eq] at h12
      have hlen : 3 + 3 * k = 3 * (k + 1) := by omega
      simpa [hlen] using h12

theorem exit_R_A_exact (W R1 : List MItem) :
    ReachesIn target_tm 13
      (⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encM W,
        (0 : Fin 2) >> encM R1⟩⟩ : Cfg (Fin 2) (Fin 6))
      (cfgCB target_tm (.run 0 :: .run 0 :: W) R1) := by
  unfold cfgCB
  dsimp only [isVarA_tm, ite_true, ite_false]
  executeWithin 13

theorem step_DL_run2_exact (d0 : Nat) (L1 R1 : List MItem) :
    ReachesIn target_tm (3 * d0 + 22)
      (cfgDL target_tm (.run 2 :: L1) (.run d0 :: R1))
      (cfgCB target_tm
        (.run 0 :: .run 0 :: List.replicate (d0 + 1) .zero ++ L1) R1) := by
  unfold cfgDL
  dsimp only [isVarA_tm, ite_true, ite_false]
  have h1 :
      ReachesIn target_tm 6
        (encM (.run 2 :: L1) <{{D}} encM (.run d0 :: R1))
        (⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encM L1,
          (([1] : List (Fin 2)) ^ (d0 + 1)) +> ((0 : Fin 2) >> encM R1)⟩⟩ :
            Cfg (Fin 2) (Fin 6)) := by
    executeWithin 6
  have h2 := cyc_R_A_exact (d0 + 1)
    ((0 : Fin 2) >> (0 : Fin 2) >> encM L1) ((0 : Fin 2) >> encM R1)
  have h12 := reachesIn_trans h1 h2
  have h_z1 := zeros_append_cons_zero (d0 + 1)
    ((0 : Fin 2) >> (0 : Fin 2) >> encM L1)
  have h_z2 := zeros_append_cons_zero (d0 + 1) (encM L1)
  rw [h_z1, h_z2, encM_replicate_zero] at h12
  have h3 := exit_R_A_exact (List.replicate (d0 + 1) .zero ++ L1) R1
  have hfin := reachesIn_trans h12 h3
  convert hfin using 1 <;> omega

theorem step_CB_run0_run_pos_exact (d2 : Nat) (L R2 : List MItem) :
    ReachesIn target_tm (3 * d2 + 21)
      (cfgCB target_tm L (.run 0 :: .run (d2 + 1) :: R2))
      (cfgCB target_tm
        (.run 0 :: .run 0 :: List.replicate d2 .zero ++ bumpM L) R2) := by
  unfold cfgCB
  dsimp only [isVarA_tm, ite_true, ite_false]
  have h1 :
      ReachesIn target_tm 5
        (⟨some C, ⟨0, encM L, encM (.run 0 :: .run (d2 + 1) :: R2)⟩⟩ :
          Cfg (Fin 2) (Fin 6))
        (⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> encM (bumpM L),
          (([1] : List (Fin 2)) ^ (d2 + 1)) +> ((0 : Fin 2) >> encM R2)⟩⟩ :
          Cfg (Fin 2) (Fin 6)) := by
    rw [← encM_bumpM L]
    executeWithin 5
  have h2 := cyc_R_A_exact (d2 + 1)
    ((0 : Fin 2) >> encM (bumpM L)) ((0 : Fin 2) >> encM R2)
  have h12 := reachesIn_trans h1 h2
  have h_z1 := zeros_append_cons_zero (d2 + 1) (encM (bumpM L))
  have h_z2 :
      ((([0] : List (Fin 2)) ^ (d2 + 1)) +> encM (bumpM L)) =
        (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ d2) +> encM (bumpM L)) := by
    simp only [pow_succ_list, cons_append_list, nil_append_list, listblank_append_cons]
  rw [h_z1, h_z2, encM_replicate_zero] at h12
  have h3 := exit_R_A_exact (List.replicate d2 .zero ++ bumpM L) R2
  have hfin := reachesIn_trans h12 h3
  convert hfin using 1 <;> omega


/-- The C-zero / nil case exits directly to BB in three primitive steps. -/
theorem step_CB_run0_nil_exact (L : List MItem) :
    ReachesIn target_tm 3 (cfgCB target_tm L [.run 0])
      (cfgBB target_tm (.run 0 :: bumpM L) []) := by
  unfold cfgCB cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM L]
  executeWithin 3

/-- The C-zero / zero case exits directly to BB in three primitive steps. -/
theorem step_CB_run0_zero_exact (L R2 : List MItem) :
    ReachesIn target_tm 3 (cfgCB target_tm L (.run 0 :: .zero :: R2))
      (cfgBB target_tm (.run 0 :: bumpM L) R2) := by
  unfold cfgCB cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM L]
  executeWithin 3



/-- B-succ followed by BR-nil: the empty right stack is bumped in 3 steps. -/
theorem step_BB_run1_nil_exact (L1 : List MItem) :
    ReachesIn target_tm 3 (cfgBB target_tm (.run 1 :: L1) [])
      (cfgBB target_tm L1 (.run 0 :: bumpM [])) := by
  unfold cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM []]
  executeWithin 3

/-- B-succ followed by BR-zero: the zero-headed right stack is bumped in 3 steps. -/
theorem step_BB_run1_zero_exact (L1 R2 : List MItem) :
    ReachesIn target_tm 3 (cfgBB target_tm (.run 1 :: L1) (.zero :: R2))
      (cfgBB target_tm L1 (.run 0 :: bumpM (.zero :: R2))) := by
  unfold cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM (.zero :: R2)]
  executeWithin 3



/-- Generic B-succ: the right stack is bumped in exactly three steps. -/
theorem step_BB_run1_exact (L1 R : List MItem) :
    ReachesIn target_tm 3 (cfgBB target_tm (.run 1 :: L1) R)
      (cfgBB target_tm L1 (.run 0 :: bumpM R)) := by
  unfold cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM R]
  executeWithin 3


#print axioms reachesWithin_mono
#print axioms reachesWithin_trans
#print axioms reachesWithin_of_exact
#print axioms step_BB_nil_exact
#print axioms step_BB_run0_exact
#print axioms cyc_R_A_exact
#print axioms exit_R_A_exact
#print axioms step_DL_run2_exact
#print axioms step_CB_run0_run_pos_exact

#print axioms step_CB_run0_nil_exact
#print axioms step_CB_run0_zero_exact

#print axioms step_BB_run1_exact
#print axioms step_BB_run1_nil_exact
#print axioms step_BB_run1_zero_exact



/-- The BB zero-run branch is one primitive step. -/
theorem step_BB_zero_exact (L1 R : List MItem) :
    ReachesIn target_tm 1 (cfgBB target_tm (.zero :: L1) R)
      (cfgCB target_tm L1 (bumpM R)) := by
  unfold cfgBB cfgCB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  executeWithin 1

/-- The BB run-two branch costs five primitive steps. -/
theorem step_BB_run2_exact (L1 R : List MItem) :
    ReachesIn target_tm 5 (cfgBB target_tm (.run 2 :: L1) R)
      (cfgDL target_tm L1 (.run 0 :: .run 0 :: bumpM R)) := by
  unfold cfgBB cfgDL
  dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  executeWithin 5

/-- The BB run-three branch costs nine primitive steps. -/
theorem step_BB_run3_exact (L1 R : List MItem) :
    ReachesIn target_tm 9 (cfgBB target_tm (.run 3 :: L1) R)
      (cfgBB target_tm (.run 0 :: .zero :: .zero :: L1) (bumpM R)) := by
  unfold cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run, encM_cons_zero]
  rw [← encM_bumpM]
  executeWithin 9

/-- Every BB run of length at least four has a uniform nine-step transition. -/
theorem step_BB_run_ge4_exact (d : Nat) (L1 R : List MItem) :
    ReachesIn target_tm 9 (cfgBB target_tm (.run (d + 4) :: L1) R)
      (cfgBB target_tm (.run 0 :: .zero :: .run d :: L1) (bumpM R)) := by
  unfold cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run, encM_cons_zero]
  rw [← encM_bumpM]
  executeWithin 9

/-- The DL run-zero branch costs one primitive step. -/
theorem step_DL_run0_exact (L1 R : List MItem) :
    ReachesIn target_tm 1 (cfgDL target_tm (.run 0 :: L1) R)
      (cfgBB target_tm L1 (bumpM R)) := by
  unfold cfgDL cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  executeWithin 1

/-- The DL run-one branch costs three primitive steps. -/
theorem step_DL_run1_exact (L1 R : List MItem) :
    ReachesIn target_tm 3 (cfgDL target_tm (.run 1 :: L1) R)
      (cfgDL target_tm L1 (.run 0 :: bumpM R)) := by
  unfold cfgDL
  dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  executeWithin 3

/-- The CB empty-right branch costs two primitive steps. -/
theorem step_CB_nil_exact (L : List MItem) :
    ReachesIn target_tm 2 (cfgCB target_tm L [])
      (cfgDL target_tm (bumpM L) [.run 0]) := by
  unfold cfgCB cfgDL
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  executeWithin 2

/-- The CB leading-zero branch costs two primitive steps. -/
theorem step_CB_zero_exact (L R1 : List MItem) :
    ReachesIn target_tm 2 (cfgCB target_tm L (.zero :: R1))
      (cfgDL target_tm (bumpM L) (bumpM R1)) := by
  unfold cfgCB cfgDL
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM L, ← encM_bumpM R1]
  executeWithin 2

/-- The CB run-zero / run-zero branch costs six primitive steps. -/
theorem step_CB_run0_run0_exact (L R2 : List MItem) :
    ReachesIn target_tm 6 (cfgCB target_tm L (.run 0 :: .run 0 :: R2))
      (cfgBB target_tm (.run 0 :: .zero :: bumpM L) R2) := by
  unfold cfgCB cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run, encM_cons_zero]
  rw [← encM_bumpM]
  executeWithin 6

/-- The CB run-two branch costs five primitive steps. -/
theorem step_CB_run2_exact (L R1 : List MItem) :
    ReachesIn target_tm 5 (cfgCB target_tm L (.run 2 :: R1))
      (cfgBB target_tm (bumpM L) (.run 0 :: .zero :: R1)) := by
  unfold cfgCB cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  executeWithin 5

/-- Every CB run of length at least three costs five primitive steps. -/
theorem step_CB_run_ge3_exact (d : Nat) (L R1 : List MItem) :
    ReachesIn target_tm 5 (cfgCB target_tm L (.run (d + 3) :: R1))
      (cfgBB target_tm (bumpM L) (.run 0 :: .run d :: R1)) := by
  unfold cfgCB cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  executeWithin 5

theorem step_CB_run1_exact (L R1 : List MItem) :
    ReachesIn target_tm 3 (cfgCB target_tm L (.run 1 :: R1))
      (cfgCB target_tm (.run 0 :: bumpM L) R1) := by
  unfold cfgCB
  dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  executeWithin 3

/-- The two-token BB transfer costs 8+3 = 11 primitive steps. -/
theorem step_BB_r0_r1_exact (L R : List MItem) :
    ReachesIn target_tm 11
      (cfgBB target_tm (.run 0 :: .run 1 :: L) R)
      (cfgBB target_tm L (.run 0 :: .run 1 :: R)) := by
  have h1 := step_BB_run0_exact (.run 1 :: L) R
  have h2 := step_BB_run1_exact L (.run 0 :: R)
  simpa [bumpM] using reachesIn_trans h1 h2

/-- The BB commutation transfer costs 3+8+3 = 14 primitive steps. -/
theorem step_BB_r1_r0_r1_comm_exact (L R : List MItem) :
    ReachesIn target_tm 14
      (cfgBB target_tm (.run 1 :: .run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: R))
      (cfgBB target_tm L
        (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)) := by
  have h1 := step_BB_run1_exact (.run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: R)
  have h1' :
      ReachesIn target_tm 3
        (cfgBB target_tm (.run 1 :: .run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: R))
        (cfgBB target_tm (.run 0 :: .run 1 :: L)
          (.run 0 :: .run 1 :: .run 1 :: R)) := by
    simpa [bumpM] using h1
  have h2 := step_BB_run0_exact (.run 1 :: L) (.run 0 :: .run 1 :: .run 1 :: R)
  have h3 := step_BB_run1_exact L (.run 0 :: .run 0 :: .run 1 :: .run 1 :: R)
  have h3' :
      ReachesIn target_tm 3
        (cfgBB target_tm (.run 1 :: L) (.run 0 :: .run 0 :: .run 1 :: .run 1 :: R))
        (cfgBB target_tm L
          (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)) := by
    simpa [bumpM] using h3
  simpa using reachesIn_trans (reachesIn_trans h1' h2) h3'

/-- F424 BB/B1 sweep: exactly 11 primitive steps per repeated block. -/
theorem sweep_BB_B1_exact (k : Nat) (L R : List MItem) :
    ReachesIn target_tm (11 * k)
      (cfgBB target_tm (repBlock [.run 0, .run 1] k ++ L) R)
      (cfgBB target_tm L (repBlock [.run 0, .run 1] k ++ R)) := by
  induction k generalizing R with
  | zero =>
      change multiStep target_tm _ 0 = some _
      simp only [multiStep_zero]
      rfl
  | succ k ih =>
    have h_eq : repBlock [.run 0, .run 1] (k + 1) ++ R =
        repBlock [.run 0, .run 1] k ++ (.run 0 :: .run 1 :: R) := by
      rw [repBlock_succ_right, List.append_assoc]
      rfl
    rw [h_eq]
    have h1 := step_BB_r0_r1_exact (repBlock [.run 0, .run 1] k ++ L) R
    have h2 := ih (.run 0 :: .run 1 :: R)
    convert reachesIn_trans h1 h2 using 1
    all_goals (try simp only [repBlock_succ_right, List.append_assoc])
    all_goals omega

/-- F424 BB/C2 sweep: exactly 14 primitive steps per repeated block. -/
theorem sweep_BB_C2_exact (p : Nat) (L R : List MItem) :
    ReachesIn target_tm (14 * p)
      (cfgBB target_tm (repBlock [.run 1, .run 0, .run 1] p ++ L)
        (.run 0 :: .run 1 :: R))
      (cfgBB target_tm L
        (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] p ++ R)) := by
  induction p generalizing R with
  | zero =>
      change multiStep target_tm _ 0 = some _
      simp only [multiStep_zero]
      rfl
  | succ p ih =>
    have h_eq :
        (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] (p + 1) ++ R) =
        (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] p ++
          (.run 0 :: .run 1 :: .run 1 :: R)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 := step_BB_r1_r0_r1_comm_exact (repBlock [.run 1, .run 0, .run 1] p ++ L) R
    have h2 := ih (.run 0 :: .run 1 :: .run 1 :: R)
    convert reachesIn_trans h1 h2 using 1
    all_goals (try simp only [repBlock_succ_right, List.append_assoc])
    all_goals omega

/-- F424 BB/C12 sweep: exactly 25 primitive steps per repeated block. -/
theorem sweep_BB_C12_exact (m : Nat) (L R : List MItem) :
    ReachesIn target_tm (25 * m)
      (cfgBB target_tm
        (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L)
        (.run 0 :: .run 1 :: R))
      (cfgBB target_tm L
        (.run 0 :: .run 1 ::
          repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)) := by
  induction m generalizing R with
  | zero =>
      change multiStep target_tm _ 0 = some _
      simp only [multiStep_zero]
      rfl
  | succ m ih =>
    have h_eq :
        (.run 0 :: .run 1 ::
          repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] (m + 1) ++ R) =
        (.run 0 :: .run 1 ::
          repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++
          (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 := step_BB_r1_r0_r1_comm_exact
      (.run 0 :: .run 1 ::
        (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L)) R
    have h2 := step_BB_r0_r1_exact
      (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L)
      (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)
    have h3 := ih (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)
    have h12 := reachesIn_trans h1 h2
    convert reachesIn_trans h12 h3 using 1
    all_goals (try simp only [repBlock_succ_right, List.append_assoc])
    all_goals omega

/-- F424 CB/B1 sweep: exactly 21 primitive steps per repeated block. -/
theorem sweep_CB_B1_exact (k : Nat) (L R : List MItem) :
    ReachesIn target_tm (21 * k)
      (cfgCB target_tm (.run 0 :: L)
        (repBlock [.run 0, .run 1] k ++ R))
      (cfgCB target_tm (.run 0 :: repBlock [.run 0, .run 1] k ++ L) R) := by
  induction k generalizing L with
  | zero =>
      change multiStep target_tm _ 0 = some _
      simp only [multiStep_zero]
      rfl
  | succ k ih =>
    have h_eq :
        (.run 0 :: repBlock [.run 0, .run 1] (k + 1) ++ L) =
        (.run 0 :: repBlock [.run 0, .run 1] k ++ (.run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 : ReachesIn target_tm 21
        (cfgCB target_tm (.run 0 :: L)
          (.run 0 :: .run 1 :: repBlock [.run 0, .run 1] k ++ R))
        (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
          (repBlock [.run 0, .run 1] k ++ R)) := by
      simpa [bumpM] using
        step_CB_run0_run_pos_exact 0 (.run 0 :: L)
          (repBlock [.run 0, .run 1] k ++ R)
    have h2 := ih (.run 0 :: .run 1 :: L)
    convert reachesIn_trans h1 h2 using 1
    all_goals (try simp only [repBlock_succ_right, List.append_assoc])
    all_goals omega

/-- F424 CB/B2 sweep: exactly 24 primitive steps per repeated block. -/
theorem sweep_CB_B2_exact (p : Nat) (L R : List MItem) :
    ReachesIn target_tm (24 * p)
      (cfgCB target_tm (.run 0 :: L)
        (repBlock [.run 0, .run 1, .run 1] p ++ R))
      (cfgCB target_tm
        (.run 0 :: repBlock [.run 1, .run 0, .run 1] p ++ L) R) := by
  induction p generalizing L with
  | zero =>
      change multiStep target_tm _ 0 = some _
      simp only [multiStep_zero]
      rfl
  | succ p ih =>
    have h_eq :
        (.run 0 :: repBlock [.run 1, .run 0, .run 1] (p + 1) ++ L) =
        (.run 0 :: repBlock [.run 1, .run 0, .run 1] p ++
          (.run 1 :: .run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 :
        ReachesIn target_tm 21
          (cfgCB target_tm (.run 0 :: L)
            (.run 0 :: .run 1 :: .run 1 ::
              (repBlock [.run 0, .run 1, .run 1] p ++ R)))
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
            (.run 1 :: (repBlock [.run 0, .run 1, .run 1] p ++ R))) := by
      simpa [bumpM] using
        step_CB_run0_run_pos_exact 0 (.run 0 :: L)
          (.run 1 :: (repBlock [.run 0, .run 1, .run 1] p ++ R))
    have h2 :
        ReachesIn target_tm 3
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
            (.run 1 :: (repBlock [.run 0, .run 1, .run 1] p ++ R)))
          (cfgCB target_tm (.run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
            (repBlock [.run 0, .run 1, .run 1] p ++ R)) := by
      simpa [bumpM] using
        step_CB_run1_exact (.run 0 :: .run 0 :: .run 1 :: L)
          (repBlock [.run 0, .run 1, .run 1] p ++ R)
    have h3 := ih (.run 1 :: .run 0 :: .run 1 :: L)
    have h12 := reachesIn_trans h1 h2
    convert reachesIn_trans h12 h3 using 1
    all_goals (try simp only [repBlock_succ_right, List.append_assoc])
    all_goals omega

/-- F424 CB/B12R sweep: exactly 45 primitive steps per repeated block. -/
theorem sweep_CB_B12R_exact (m : Nat) (L R : List MItem) :
    ReachesIn target_tm (45 * m)
      (cfgCB target_tm (.run 0 :: L)
        (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))
      (cfgCB target_tm
        (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L) R) := by
  induction m generalizing L with
  | zero =>
      change multiStep target_tm _ 0 = some _
      simp only [multiStep_zero]
      rfl
  | succ m ih =>
    have h_eq :
        (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] (m + 1) ++ L) =
        (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++
          (.run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 :
        ReachesIn target_tm 21
          (cfgCB target_tm (.run 0 :: L)
            (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 ::
              (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)))
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
            (.run 0 :: .run 1 :: .run 1 ::
              (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))) := by
      simpa [bumpM] using
        step_CB_run0_run_pos_exact 0 (.run 0 :: L)
          (.run 0 :: .run 1 :: .run 1 ::
            (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))
    have h2 :
        ReachesIn target_tm 21
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
            (.run 0 :: .run 1 :: .run 1 ::
              (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)))
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
            (.run 1 ::
              (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))) := by
      simpa [bumpM] using
        step_CB_run0_run_pos_exact 0 (.run 0 :: .run 0 :: .run 1 :: L)
          (.run 1 ::
            (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))
    have h3 :
        ReachesIn target_tm 3
          (cfgCB target_tm
            (.run 0 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
            (.run 1 ::
              (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)))
          (cfgCB target_tm
            (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
            (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)) := by
      simpa [bumpM] using
        step_CB_run1_exact
          (.run 0 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
          (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)
    have h3' := ih (.run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
    have h12 := reachesIn_trans (reachesIn_trans h1 h2) h3
    convert reachesIn_trans h12 h3' using 1
    all_goals (try simp only [repBlock_succ_right, List.append_assoc])
    all_goals omega

#print axioms step_BB_zero_exact
#print axioms step_BB_run2_exact
#print axioms step_BB_run3_exact
#print axioms step_BB_run_ge4_exact
#print axioms step_DL_run0_exact
#print axioms step_DL_run1_exact
#print axioms step_CB_nil_exact
#print axioms step_CB_zero_exact
#print axioms step_CB_run0_run0_exact
#print axioms step_CB_run2_exact
#print axioms step_CB_run_ge3_exact
#print axioms step_CB_run1_exact
#print axioms step_BB_r0_r1_exact
#print axioms step_BB_r1_r0_r1_comm_exact
#print axioms sweep_BB_B1_exact
#print axioms sweep_BB_C2_exact
#print axioms sweep_BB_C12_exact
#print axioms sweep_CB_B1_exact
#print axioms sweep_CB_B2_exact
#print axioms sweep_CB_B12R_exact





end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution
