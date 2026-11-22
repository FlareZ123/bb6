/-
Scratch pilot: turn the upstream execute tactic into an exact ReachesIn proof.
Pinned source: google-deepmind/cryptids @ 3647718b5df22e1a61462dec0376bd204526285a.
-/
import BusyBeaver.BB6.Halt.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH
import SymRunTraceStats

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

macro "stepWithin" : tactic => `(tactic| (
  try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, pow_succ_list, pow_zero_list,
    cons_append_list, nil_append_list, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head, default_tail,
    encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head, cons_one_encLeft_tail,
    encRight_cons_head, cons_one_encRight_tail, encM_cons_run_head, cons_one_encM_cons_run_tail]
  apply BusyBeaver.ReachesIn.step_left
  · rfl
  · simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,
      pow_succ_list, pow_zero_list, cons_append_list, nil_append_list,
      listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head,
      default_tail, encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head,
      cons_one_encLeft_tail, encRight_cons_head, cons_one_encRight_tail,
      encM_cons_run_head, cons_one_encM_cons_run_tail]
))

macro "finishWithin" : tactic => `(tactic| (
  change multiStep target_tm _ 0 = some _
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, pow_succ_list, pow_zero_list,
    cons_append_list, nil_append_list, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zero_cons_default, default_head,
    default_tail, enc1_nil, encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head,
    cons_one_encLeft_tail, encRight_cons_head, cons_one_encRight_tail, encM_cons_run_head,
    cons_one_encM_cons_run_tail, multiStep_zero]
  try rfl
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



/-- The F424 C-run1 rule has an exact three-step realization. -/
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
    convert reachesIn_trans h1 h2 using 1 <;> omega

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
    convert reachesIn_trans h1 h2 using 1 <;> omega

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
    convert reachesIn_trans h12 h3 using 1 <;> omega

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
    convert reachesIn_trans h1 h2 using 1 <;> omega

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
    convert reachesIn_trans h12 h3 using 1 <;> omega

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
    convert reachesIn_trans h12 h3' using 1 <;> omega

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




/-! A local field measure and constructor-complete costed one-element
    semantics. These bounds are machine-specific to F424 through the exact
    ReachesIn witnesses above. -/

def pilotTokFieldMax : SymTok → Nat
  | .item .zero => 0
  | .item (.run d) => d
  | .repB1 k => k
  | .rep2 p => p
  | .rep12 m => m

def pilotListFieldMax : List SymTok → Nat
  | [] => 0
  | t :: xs => max (pilotTokFieldMax t) (pilotListFieldMax xs)

def pilotStateFieldMax (s : SymMode × List SymTok × List SymTok) : Nat :=
  max (pilotListFieldMax s.2.1) (pilotListFieldMax s.2.2)

theorem pilot_reachesIn_refl (c : Cfg (Fin 2) (Fin 6)) :
    ReachesIn target_tm 0 c c := by
  change multiStep target_tm c 0 = some c
  simp only [multiStep_zero]

theorem pilot_peelPureTok_field_growth (t : SymTok) (xs : List SymTok) :
    pilotListFieldMax (peelPureTok t xs) ≤
      max (pilotTokFieldMax t) (pilotListFieldMax xs) := by
  cases t with
  | item x =>
    cases x <;> simp [peelPureTok, pilotListFieldMax, pilotTokFieldMax]
  | repB1 k =>
    cases k <;> simp [peelPureTok, pilotListFieldMax, pilotTokFieldMax] <;> omega
  | rep2 p =>
    cases p <;> simp [peelPureTok, pilotListFieldMax, pilotTokFieldMax] <;> omega
  | rep12 m =>
    cases m <;> simp [peelPureTok, pilotListFieldMax, pilotTokFieldMax] <;> omega

theorem pilotStateFieldMax_left_mono (mode : SymMode) (L' L R : List SymTok)
    (hL : pilotListFieldMax L' ≤ pilotListFieldMax L) :
    pilotStateFieldMax (mode, L', R) ≤ pilotStateFieldMax (mode, L, R) := by
  simp only [pilotStateFieldMax]
  apply Nat.max_le.mpr
  constructor
  · exact Nat.le_trans hL (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

theorem pilotStateFieldMax_right_mono (mode : SymMode) (L R' R : List SymTok)
    (hR : pilotListFieldMax R' ≤ pilotListFieldMax R) :
    pilotStateFieldMax (mode, L, R') ≤ pilotStateFieldMax (mode, L, R) := by
  simp only [pilotStateFieldMax]
  apply Nat.max_le.mpr
  constructor
  · exact Nat.le_max_left _ _
  · exact Nat.le_trans hR (Nat.le_max_right _ _)


/-- The source `peelTok` operation never exposes a numeric field larger
    than the head token it expands or the untouched suffix. -/
theorem pilot_peelTok_field_growth (t : SymTok) (xs : List SymTok) :
    pilotListFieldMax (peelTok t xs) ≤
      max (pilotTokFieldMax t) (pilotListFieldMax xs) := by
  cases t with
  | item x =>
    cases x <;> simp [peelTok, pilotListFieldMax, pilotTokFieldMax]
  | repB1 k =>
    cases k <;> simp [peelTok, pilotListFieldMax, pilotTokFieldMax, strictNat_eq] <;> omega
  | rep2 p =>
    cases p <;> simp [peelTok, pilotListFieldMax, pilotTokFieldMax, strictNat_eq] <;> omega
  | rep12 m =>
    cases m <;> simp [peelTok, pilotListFieldMax, pilotTokFieldMax, strictNat_eq] <;> omega

theorem pilot_peelL_field_growth (L : List SymTok) :
    pilotListFieldMax (peelL L) ≤ pilotListFieldMax L := by
  cases L with
  | nil => simp [peelL, pilotListFieldMax]
  | cons t xs =>
    simpa [peelL, pilotListFieldMax] using pilot_peelTok_field_growth t xs

theorem pilot_peelTok_length_le (t : SymTok) (xs : List SymTok) :
    (peelTok t xs).length ≤ xs.length + 6 := by
  cases t with
  | item x =>
    cases x <;> simp [peelTok, strictNat_eq]
  | repB1 k =>
    cases k <;> simp [peelTok, strictNat_eq] <;> omega
  | rep2 p =>
    cases p <;> simp [peelTok, strictNat_eq] <;> omega
  | rep12 m =>
    cases m <;> simp [peelTok, strictNat_eq] <;> omega

theorem pilot_peelL_length_le (L : List SymTok) :
    (peelL L).length ≤ L.length + 5 := by
  cases L with
  | nil => simp [peelL]
  | cons t xs =>
    have h := pilot_peelTok_length_le t xs
    simp only [peelL, List.length_cons]
    omega

theorem pilotStateFieldMax_peelL_left_mono (mode : SymMode) (L R : List SymTok) :
    pilotStateFieldMax (mode, peelL L, R) ≤
      pilotStateFieldMax (mode, L, R) := by
  apply pilotStateFieldMax_left_mono
  exact pilot_peelL_field_growth L

theorem stepElemBB_within (L R : List SymTok) :
    ReachesWithin (50 * (pilotStateFieldMax (.BB, L, R) + 1))
      ((evalSym target_tm) (.BB, L, R))
      ((evalSym target_tm) (stepElemBB L R)) := by
  unfold ReachesWithin
  cases L with
  | nil =>
    refine ⟨1, by omega, ?_⟩
    simpa only [stepElemBB, strictList_eq, evalSym, evalM, encSymL, encSymR_bumpSymR] using
      step_BB_nil_exact (encSymR R)
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        refine ⟨1, by omega, ?_⟩
        simpa only [stepElemBB, strictList_eq, evalSym, evalM, encSymL, encSymR_bumpSymR] using
          step_BB_zero_exact (encSymL L1) (encSymR R)
      | run d =>
        rcases d with _ | _ | _ | _ | d
        · refine ⟨8, by omega, ?_⟩
          simpa only [stepElemBB, strictList_eq, strictNat_eq, evalSym, evalM,
            encSymL, encSymR, encSymR_bumpSymR] using
            step_BB_run0_exact (encSymL L1) (encSymR R)
        · refine ⟨3, by omega, ?_⟩
          simpa only [stepElemBB, strictList_eq, strictNat_eq, evalSym, evalM,
            encSymL, encSymR, encSymR_bumpSymR] using
            step_BB_run1_exact (encSymL L1) (encSymR R)
        · refine ⟨5, by omega, ?_⟩
          simpa only [stepElemBB, strictList_eq, strictNat_eq, evalSym, evalM,
            encSymL, encSymR, encSymR_bumpSymR] using
            step_BB_run2_exact (encSymL L1) (encSymR R)
        · refine ⟨9, by omega, ?_⟩
          simpa only [stepElemBB, strictList_eq, strictNat_eq, evalSym, evalM,
            encSymL, encSymR, encSymR_bumpSymR] using
            step_BB_run3_exact (encSymL L1) (encSymR R)
        · refine ⟨9, by omega, ?_⟩
          simpa only [stepElemBB, strictList_eq, strictNat_eq, evalSym, evalM,
            encSymL, encSymR, encSymR_bumpSymR] using
            step_BB_run_ge4_exact d (encSymL L1) (encSymR R)
    | repB1 k =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemBB] using
        pilot_reachesIn_refl ((evalSym target_tm) (.BB, .repB1 k :: L1, R))
    | rep2 p =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemBB] using
        pilot_reachesIn_refl ((evalSym target_tm) (.BB, .rep2 p :: L1, R))
    | rep12 m =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemBB] using
        pilot_reachesIn_refl ((evalSym target_tm) (.BB, .rep12 m :: L1, R))

theorem stepElemDL_within (L R : List SymTok) :
    ReachesWithin (50 * (pilotStateFieldMax (.DL, L, R) + 1))
      ((evalSym target_tm) (.DL, L, R))
      ((evalSym target_tm) (stepElemDL L R)) := by
  unfold ReachesWithin
  cases L with
  | nil =>
    refine ⟨0, by omega, ?_⟩
    simpa [stepElemDL] using pilot_reachesIn_refl ((evalSym target_tm) (.DL, [], R))
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        refine ⟨0, by omega, ?_⟩
        simpa [stepElemDL] using
          pilot_reachesIn_refl ((evalSym target_tm) (.DL, .item .zero :: L1, R))
      | run d =>
        rcases d with _ | _ | _ | d
        · refine ⟨1, by omega, ?_⟩
          simpa only [stepElemDL, strictList_eq, evalSym, evalM, encSymL, encSymR_bumpSymR] using
            step_DL_run0_exact (encSymL L1) (encSymR R)
        · refine ⟨3, by omega, ?_⟩
          simpa only [stepElemDL, strictList_eq, evalSym, evalM, encSymL, encSymR,
            encSymR_bumpSymR] using
            step_DL_run1_exact (encSymL L1) (encSymR R)
        · cases R with
          | nil =>
            refine ⟨0, by omega, ?_⟩
            simpa [stepElemDL] using
              pilot_reachesIn_refl ((evalSym target_tm) (.DL, .item (.run 2) :: L1, []))
          | cons rt R1 =>
            cases rt with
            | item it =>
              cases it with
              | zero =>
                refine ⟨0, by omega, ?_⟩
                simpa [stepElemDL] using
                  pilot_reachesIn_refl
                    ((evalSym target_tm) (.DL, .item (.run 2) :: L1, .item .zero :: R1))
              | run d0 =>
                refine ⟨3 * d0 + 22, ?_, ?_⟩
                · have hd : d0 ≤
                      pilotStateFieldMax (.DL, .item (.run 2) :: L1, .item (.run d0) :: R1) := by
                    simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax] <;> omega
                  omega
                · simpa only [stepElemDL, strictList_eq, evalSym, evalM, encSymL, encSymR,
                    encSymL_prependZeroSym] using
                    step_DL_run2_exact d0 (encSymL L1) (encSymR R1)
            | repB1 k =>
              refine ⟨0, by omega, ?_⟩
              simpa [stepElemDL] using
                pilot_reachesIn_refl
                  ((evalSym target_tm) (.DL, .item (.run 2) :: L1, .repB1 k :: R1))
            | rep2 p =>
              refine ⟨0, by omega, ?_⟩
              simpa [stepElemDL] using
                pilot_reachesIn_refl
                  ((evalSym target_tm) (.DL, .item (.run 2) :: L1, .rep2 p :: R1))
            | rep12 m =>
              refine ⟨0, by omega, ?_⟩
              simpa [stepElemDL] using
                pilot_reachesIn_refl
                  ((evalSym target_tm) (.DL, .item (.run 2) :: L1, .rep12 m :: R1))
        · refine ⟨0, by omega, ?_⟩
          simpa [stepElemDL] using
            pilot_reachesIn_refl
              ((evalSym target_tm) (.DL, .item (.run (d + 3)) :: L1, R))
    | repB1 k =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemDL] using
        pilot_reachesIn_refl ((evalSym target_tm) (.DL, .repB1 k :: L1, R))
    | rep2 p =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemDL] using
        pilot_reachesIn_refl ((evalSym target_tm) (.DL, .rep2 p :: L1, R))
    | rep12 m =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemDL] using
        pilot_reachesIn_refl ((evalSym target_tm) (.DL, .rep12 m :: L1, R))


theorem stepElemDL_within25 (L R : List SymTok) :
    ReachesWithin (25 * (pilotStateFieldMax (.DL, L, R) + 1))
      ((evalSym target_tm) (.DL, L, R))
      ((evalSym target_tm) (stepElemDL L R)) := by
  unfold ReachesWithin
  cases L with
  | nil =>
    refine ⟨0, by omega, ?_⟩
    simpa [stepElemDL] using pilot_reachesIn_refl ((evalSym target_tm) (.DL, [], R))
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        refine ⟨0, by omega, ?_⟩
        simpa [stepElemDL] using
          pilot_reachesIn_refl ((evalSym target_tm) (.DL, .item .zero :: L1, R))
      | run d =>
        rcases d with _ | _ | _ | d
        · refine ⟨1, by omega, ?_⟩
          simpa only [stepElemDL, strictList_eq, evalSym, evalM, encSymL, encSymR_bumpSymR] using
            step_DL_run0_exact (encSymL L1) (encSymR R)
        · refine ⟨3, by omega, ?_⟩
          simpa only [stepElemDL, strictList_eq, evalSym, evalM, encSymL, encSymR,
            encSymR_bumpSymR] using
            step_DL_run1_exact (encSymL L1) (encSymR R)
        · cases R with
          | nil =>
            refine ⟨0, by omega, ?_⟩
            simpa [stepElemDL] using
              pilot_reachesIn_refl ((evalSym target_tm) (.DL, .item (.run 2) :: L1, []))
          | cons rt R1 =>
            cases rt with
            | item it =>
              cases it with
              | zero =>
                refine ⟨0, by omega, ?_⟩
                simpa [stepElemDL] using
                  pilot_reachesIn_refl
                    ((evalSym target_tm) (.DL, .item (.run 2) :: L1, .item .zero :: R1))
              | run d0 =>
                refine ⟨3 * d0 + 22, ?_, ?_⟩
                · have hd : d0 ≤
                      pilotStateFieldMax (.DL, .item (.run 2) :: L1, .item (.run d0) :: R1) := by
                    simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax] <;> omega
                  omega
                · simpa only [stepElemDL, strictList_eq, evalSym, evalM, encSymL, encSymR,
                    encSymL_prependZeroSym] using
                    step_DL_run2_exact d0 (encSymL L1) (encSymR R1)
            | repB1 k =>
              refine ⟨0, by omega, ?_⟩
              simpa [stepElemDL] using
                pilot_reachesIn_refl
                  ((evalSym target_tm) (.DL, .item (.run 2) :: L1, .repB1 k :: R1))
            | rep2 p =>
              refine ⟨0, by omega, ?_⟩
              simpa [stepElemDL] using
                pilot_reachesIn_refl
                  ((evalSym target_tm) (.DL, .item (.run 2) :: L1, .rep2 p :: R1))
            | rep12 m =>
              refine ⟨0, by omega, ?_⟩
              simpa [stepElemDL] using
                pilot_reachesIn_refl
                  ((evalSym target_tm) (.DL, .item (.run 2) :: L1, .rep12 m :: R1))
        · refine ⟨0, by omega, ?_⟩
          simpa [stepElemDL] using
            pilot_reachesIn_refl
              ((evalSym target_tm) (.DL, .item (.run (d + 3)) :: L1, R))
    | repB1 k =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemDL] using
        pilot_reachesIn_refl ((evalSym target_tm) (.DL, .repB1 k :: L1, R))
    | rep2 p =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemDL] using
        pilot_reachesIn_refl ((evalSym target_tm) (.DL, .rep2 p :: L1, R))
    | rep12 m =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemDL] using
        pilot_reachesIn_refl ((evalSym target_tm) (.DL, .rep12 m :: L1, R))

theorem stepElemCB_run0_within (L R1 : List SymTok) :
    ReachesWithin (50 * (pilotStateFieldMax (.CB, L, .item (.run 0) :: R1) + 1))
      ((evalSym target_tm) (.CB, L, .item (.run 0) :: R1))
      ((evalSym target_tm) (stepElemCB_run0 L R1)) := by
  unfold ReachesWithin
  cases R1 with
  | nil =>
    refine ⟨3, by omega, ?_⟩
    simpa only [stepElemCB_run0, strictList_eq, evalSym, evalM, encSymL, encSymR,
      encSymL_bumpSymL] using
      step_CB_run0_nil_exact (encSymL L)
  | cons rt R2 =>
    cases rt with
    | item it =>
      cases it with
      | zero =>
        refine ⟨3, by omega, ?_⟩
        simpa only [stepElemCB_run0, strictList_eq, evalSym, evalM, encSymL, encSymR,
          encSymL_bumpSymL] using
          step_CB_run0_zero_exact (encSymL L) (encSymR R2)
      | run d2 =>
        rcases d2 with _ | d2
        · refine ⟨6, by omega, ?_⟩
          simpa only [stepElemCB_run0, strictList_eq, evalSym, evalM, encSymL, encSymR,
            encSymL_bumpSymL, encSymL_prependZeroSym] using
            step_CB_run0_run0_exact (encSymL L) (encSymR R2)
        · refine ⟨3 * d2 + 21, ?_, ?_⟩
          · have hd : d2 ≤ pilotStateFieldMax
                (.CB, L, .item (.run 0) :: .item (.run (d2 + 1)) :: R2) := by
              simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax] <;> omega
            omega
          · simpa only [stepElemCB_run0, strictList_eq, evalSym, evalM, encSymL, encSymR,
              encSymL_bumpSymL, encSymL_prependZeroSym] using
              step_CB_run0_run_pos_exact d2 (encSymL L) (encSymR R2)
    | repB1 k =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemCB_run0] using
        pilot_reachesIn_refl
          ((evalSym target_tm) (.CB, L, .item (.run 0) :: .repB1 k :: R2))
    | rep2 p =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemCB_run0] using
        pilot_reachesIn_refl
          ((evalSym target_tm) (.CB, L, .item (.run 0) :: .rep2 p :: R2))
    | rep12 m =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemCB_run0] using
        pilot_reachesIn_refl
          ((evalSym target_tm) (.CB, L, .item (.run 0) :: .rep12 m :: R2))



theorem stepElemCB_run0_within25 (L R1 : List SymTok) :
    ReachesWithin (25 * (pilotStateFieldMax (.CB, L, .item (.run 0) :: R1) + 1))
      ((evalSym target_tm) (.CB, L, .item (.run 0) :: R1))
      ((evalSym target_tm) (stepElemCB_run0 L R1)) := by
  unfold ReachesWithin
  cases R1 with
  | nil =>
    refine ⟨3, by omega, ?_⟩
    simpa only [stepElemCB_run0, strictList_eq, evalSym, evalM, encSymL, encSymR,
      encSymL_bumpSymL] using
      step_CB_run0_nil_exact (encSymL L)
  | cons rt R2 =>
    cases rt with
    | item it =>
      cases it with
      | zero =>
        refine ⟨3, by omega, ?_⟩
        simpa only [stepElemCB_run0, strictList_eq, evalSym, evalM, encSymL, encSymR,
          encSymL_bumpSymL] using
          step_CB_run0_zero_exact (encSymL L) (encSymR R2)
      | run d2 =>
        rcases d2 with _ | d2
        · refine ⟨6, by omega, ?_⟩
          simpa only [stepElemCB_run0, strictList_eq, evalSym, evalM, encSymL, encSymR,
            encSymL_bumpSymL, encSymL_prependZeroSym] using
            step_CB_run0_run0_exact (encSymL L) (encSymR R2)
        · refine ⟨3 * d2 + 21, ?_, ?_⟩
          · have hd : d2 ≤ pilotStateFieldMax
                (.CB, L, .item (.run 0) :: .item (.run (d2 + 1)) :: R2) := by
              simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax] <;> omega
            omega
          · simpa only [stepElemCB_run0, strictList_eq, evalSym, evalM, encSymL, encSymR,
              encSymL_bumpSymL, encSymL_prependZeroSym] using
              step_CB_run0_run_pos_exact d2 (encSymL L) (encSymR R2)
    | repB1 k =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemCB_run0] using
        pilot_reachesIn_refl
          ((evalSym target_tm) (.CB, L, .item (.run 0) :: .repB1 k :: R2))
    | rep2 p =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemCB_run0] using
        pilot_reachesIn_refl
          ((evalSym target_tm) (.CB, L, .item (.run 0) :: .rep2 p :: R2))
    | rep12 m =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemCB_run0] using
        pilot_reachesIn_refl
          ((evalSym target_tm) (.CB, L, .item (.run 0) :: .rep12 m :: R2))

theorem stepElemCB_within (L R : List SymTok) :
    ReachesWithin (50 * (pilotStateFieldMax (.CB, L, R) + 1))
      ((evalSym target_tm) (.CB, L, R))
      ((evalSym target_tm) (stepElemCB L R)) := by
  unfold ReachesWithin
  cases R with
  | nil =>
    refine ⟨2, by omega, ?_⟩
    simpa only [stepElemCB, strictList_eq, evalSym, evalM, encSymL_bumpSymL] using
      step_CB_nil_exact (encSymL L)
  | cons t R1 =>
    cases t with
    | item it =>
      cases it with
      | zero =>
        refine ⟨2, by omega, ?_⟩
        simpa only [stepElemCB, strictList_eq, evalSym, evalM, encSymL_bumpSymL,
          encSymR_bumpSymR] using
          step_CB_zero_exact (encSymL L) (encSymR R1)
      | run d =>
        rcases d with _ | _ | _ | d
        · simpa [stepElemCB] using stepElemCB_run0_within L R1
        · refine ⟨3, by omega, ?_⟩
          simpa only [stepElemCB, strictList_eq, evalSym, evalM, encSymL, encSymR,
            encSymL_bumpSymL] using
            step_CB_run1_exact (encSymL L) (encSymR R1)
        · refine ⟨5, by omega, ?_⟩
          simpa only [stepElemCB, strictList_eq, evalSym, evalM, encSymL, encSymR,
            encSymL_bumpSymL] using
            step_CB_run2_exact (encSymL L) (encSymR R1)
        · refine ⟨5, by omega, ?_⟩
          simpa only [stepElemCB, strictList_eq, strictNat_eq, evalSym, evalM,
            encSymL, encSymR, encSymL_bumpSymL] using
            step_CB_run_ge3_exact d (encSymL L) (encSymR R1)
    | repB1 k =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemCB] using
        pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, .repB1 k :: R1))
    | rep2 p =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemCB] using
        pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, .rep2 p :: R1))
    | rep12 m =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemCB] using
        pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, .rep12 m :: R1))

#print axioms stepElemBB_within
#print axioms stepElemDL_within
#print axioms stepElemCB_run0_within
#print axioms stepElemCB_within






theorem stepElemCB_within25 (L R : List SymTok) :
    ReachesWithin (25 * (pilotStateFieldMax (.CB, L, R) + 1))
      ((evalSym target_tm) (.CB, L, R))
      ((evalSym target_tm) (stepElemCB L R)) := by
  unfold ReachesWithin
  cases R with
  | nil =>
    refine ⟨2, by omega, ?_⟩
    simpa only [stepElemCB, strictList_eq, evalSym, evalM, encSymL_bumpSymL] using
      step_CB_nil_exact (encSymL L)
  | cons t R1 =>
    cases t with
    | item it =>
      cases it with
      | zero =>
        refine ⟨2, by omega, ?_⟩
        simpa only [stepElemCB, strictList_eq, evalSym, evalM, encSymL_bumpSymL,
          encSymR_bumpSymR] using
          step_CB_zero_exact (encSymL L) (encSymR R1)
      | run d =>
        rcases d with _ | _ | _ | d
        · simpa [stepElemCB] using stepElemCB_run0_within25 L R1
        · refine ⟨3, by omega, ?_⟩
          simpa only [stepElemCB, strictList_eq, evalSym, evalM, encSymL, encSymR,
            encSymL_bumpSymL] using
            step_CB_run1_exact (encSymL L) (encSymR R1)
        · refine ⟨5, by omega, ?_⟩
          simpa only [stepElemCB, strictList_eq, evalSym, evalM, encSymL, encSymR,
            encSymL_bumpSymL] using
            step_CB_run2_exact (encSymL L) (encSymR R1)
        · refine ⟨5, by omega, ?_⟩
          simpa only [stepElemCB, strictList_eq, strictNat_eq, evalSym, evalM,
            encSymL, encSymR, encSymL_bumpSymL] using
            step_CB_run_ge3_exact d (encSymL L) (encSymR R1)
    | repB1 k =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemCB] using
        pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, .repB1 k :: R1))
    | rep2 p =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemCB] using
        pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, .rep2 p :: R1))
    | rep12 m =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemCB] using
        pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, .rep12 m :: R1))

#print axioms stepElemBB_within
#print axioms stepElemDL_within
#print axioms stepElemCB_run0_within
#print axioms stepElemCB_within




theorem pilotTokFieldMax_le_state_left (mode : SymMode) (t : SymTok)
    (L R : List SymTok) :
    pilotTokFieldMax t ≤ pilotStateFieldMax (mode, t :: L, R) := by
  simp [pilotStateFieldMax, pilotListFieldMax]

theorem pilotTokFieldMax_le_state_right (mode : SymMode) (L : List SymTok)
    (t : SymTok) (R : List SymTok) :
    pilotTokFieldMax t ≤ pilotStateFieldMax (mode, L, t :: R) := by
  simp [pilotStateFieldMax, pilotListFieldMax]

theorem pilotStateFieldMax_peel_left_mono (mode : SymMode) (t : SymTok)
    (L R : List SymTok) :
    pilotStateFieldMax (mode, peelPureTok t L, R) ≤
      pilotStateFieldMax (mode, t :: L, R) := by
  apply pilotStateFieldMax_left_mono
  simpa [pilotListFieldMax] using pilot_peelPureTok_field_growth t L

theorem stepPureBB_within (L R : List SymTok) :
    ReachesWithin (50 * (pilotStateFieldMax (.BB, L, R) + 1))
      ((evalSym target_tm) (.BB, L, R))
      ((evalSym target_tm) (stepPureBB L R)) := by
  cases L with
  | nil =>
    simpa [stepPureBB] using stepElemBB_within [] R
  | cons t L1 =>
    cases t with
    | item x =>
      simpa [stepPureBB] using stepElemBB_within (.item x :: L1) R
    | repB1 k =>
      unfold ReachesWithin
      refine ⟨11 * k, ?_, ?_⟩
      · have hk := pilotTokFieldMax_le_state_left .BB (.repB1 k) L1 R
        omega
      · exact sweep_BB_B1_exact k (encSymL L1) (encSymR R)
    | rep2 p =>
      simp only [stepPureBB]
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hs
        rw [hR]
        unfold ReachesWithin
        refine ⟨14 * p, ?_, ?_⟩
        · simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax] <;> omega
        · simp only [evalSym, evalM, encSymL, encSymR, List.cons_append, List.nil_append]
          exact sweep_BB_C2_exact p (encSymL L1) (encSymR R2)
      | none =>
        have heq : (evalSym target_tm) (.BB, .rep2 p :: L1, R) =
            (evalSym target_tm) (.BB, peelPureTok (.rep2 p) L1, R) := by
          simp only [evalSym, encSymL_peelPureTok]
        rw [heq]
        have hm := pilotStateFieldMax_peel_left_mono .BB (.rep2 p) L1 R
        have hstep := stepElemBB_within (peelPureTok (.rep2 p) L1) R
        have hB :
            50 * (pilotStateFieldMax (.BB, peelPureTok (.rep2 p) L1, R) + 1) ≤
              50 * (pilotStateFieldMax (.BB, .rep2 p :: L1, R) + 1) :=
          Nat.mul_le_mul_left 50 (Nat.add_le_add_right hm 1)
        exact reachesWithin_mono hB hstep
    | rep12 m =>
      simp only [stepPureBB]
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hs
        rw [hR]
        unfold ReachesWithin
        refine ⟨25 * m, ?_, ?_⟩
        · simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax] <;> omega
        · simp only [evalSym, evalM, encSymL, encSymR, List.cons_append, List.nil_append]
          exact sweep_BB_C12_exact m (encSymL L1) (encSymR R2)
      | none =>
        have heq : (evalSym target_tm) (.BB, .rep12 m :: L1, R) =
            (evalSym target_tm) (.BB, peelPureTok (.rep12 m) L1, R) := by
          simp only [evalSym, encSymL_peelPureTok]
        rw [heq]
        have hm := pilotStateFieldMax_peel_left_mono .BB (.rep12 m) L1 R
        have hstep := stepElemBB_within (peelPureTok (.rep12 m) L1) R
        have hB :
            50 * (pilotStateFieldMax (.BB, peelPureTok (.rep12 m) L1, R) + 1) ≤
              50 * (pilotStateFieldMax (.BB, .rep12 m :: L1, R) + 1) :=
          Nat.mul_le_mul_left 50 (Nat.add_le_add_right hm 1)
        exact reachesWithin_mono hB hstep

theorem stepPureDL_within (L R : List SymTok) :
    ReachesWithin (50 * (pilotStateFieldMax (.DL, L, R) + 1))
      ((evalSym target_tm) (.DL, L, R))
      ((evalSym target_tm) (stepPureDL L R)) := by
  cases L with
  | nil =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [stepPureDL] using pilot_reachesIn_refl ((evalSym target_tm) (.DL, [], R))
  | cons t L1 =>
    have heq : (evalSym target_tm) (.DL, t :: L1, R) =
        (evalSym target_tm) (.DL, peelPureTok t L1, R) := by
      simp only [evalSym, encSymL_peelPureTok]
    rw [heq]
    have hm := pilotStateFieldMax_peel_left_mono .DL t L1 R
    have hstep := stepElemDL_within (peelPureTok t L1) R
    have hB :
        50 * (pilotStateFieldMax (.DL, peelPureTok t L1, R) + 1) ≤
          50 * (pilotStateFieldMax (.DL, t :: L1, R) + 1) :=
      Nat.mul_le_mul_left 50 (Nat.add_le_add_right hm 1)
    simpa [stepPureDL] using reachesWithin_mono hB hstep

theorem stepPureCB_within (L R : List SymTok) :
    ReachesWithin (50 * (pilotStateFieldMax (.CB, L, R) + 1))
      ((evalSym target_tm) (.CB, L, R))
      ((evalSym target_tm) (stepPureCB L R)) := by
  cases R with
  | nil =>
    simpa [stepPureCB] using stepElemCB_within L []
  | cons t R1 =>
    cases t with
    | item it =>
      cases it with
      | zero =>
        simpa [stepPureCB] using stepElemCB_within L (.item .zero :: R1)
      | run d =>
        rcases d with _ | _ | _ | d
        · simpa [stepPureCB] using stepElemCB_run0_within L R1
        · simpa [stepPureCB] using stepElemCB_within L (.item (.run 1) :: R1)
        · simpa [stepPureCB] using stepElemCB_within L (.item (.run 2) :: R1)
        · unfold ReachesWithin
          refine ⟨5, by omega, ?_⟩
          simpa only [stepPureCB, evalSym, evalM, encSymR, encSymL_bumpSymL] using
            step_CB_run_ge3_exact d (encSymL L) (encSymR R1)
    | repB1 k =>
      simp only [stepPureCB]
      cases hs2 : stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1)] L with
      | some L2 =>
        have hL := stripPrefixSym_some _ L L2 hs2
        rw [hL]
        unfold ReachesWithin
        refine ⟨21 * k, ?_, ?_⟩
        · simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax] <;> omega
        · simp only [evalSym, evalM, encSymL, encSymR, List.cons_append, List.nil_append,
            repBlock_succ_right, List.append_assoc]
          exact sweep_CB_B1_exact k (.run 0 :: .run 1 :: encSymL L2) (encSymR R1)
      | none =>
        cases hs1 : stripPrefixSym [.item (.run 0)] L with
        | some L1 =>
          have hL := stripPrefixSym_some _ L L1 hs1
          rw [hL]
          unfold ReachesWithin
          refine ⟨21 * k, ?_, ?_⟩
          · simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax] <;> omega
          · simp only [evalSym, evalM, encSymL, encSymR, List.cons_append, List.nil_append]
            exact sweep_CB_B1_exact k (encSymL L1) (encSymR R1)
        | none =>
          unfold ReachesWithin
          refine ⟨0, by omega, ?_⟩
          simpa [stepPureCB, hs2, hs1] using
            pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, .repB1 k :: R1))
    | rep2 p =>
      simp only [stepPureCB]
      cases hs2 : stripPrefixSym
          [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] L with
      | some L2 =>
        have hL := stripPrefixSym_some _ L L2 hs2
        rw [hL]
        unfold ReachesWithin
        refine ⟨24 * p, ?_, ?_⟩
        · simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax] <;> omega
        · simp only [evalSym, evalM, encSymL, encSymR, List.cons_append, List.nil_append,
            repBlock_succ_right, List.append_assoc]
          exact sweep_CB_B2_exact p (.run 1 :: .run 0 :: .run 1 :: encSymL L2) (encSymR R1)
      | none =>
        cases hs1 : stripPrefixSym [.item (.run 0)] L with
        | some L1 =>
          have hL := stripPrefixSym_some _ L L1 hs1
          rw [hL]
          unfold ReachesWithin
          refine ⟨24 * p, ?_, ?_⟩
          · simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax] <;> omega
          · simp only [evalSym, evalM, encSymL, encSymR, List.cons_append, List.nil_append]
            exact sweep_CB_B2_exact p (encSymL L1) (encSymR R1)
        | none =>
          unfold ReachesWithin
          refine ⟨0, by omega, ?_⟩
          simpa [stepPureCB, hs2, hs1] using
            pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, .rep2 p :: R1))
    | rep12 m =>
      simp only [stepPureCB]
      cases hs1 : stripPrefixSym [.item (.run 0)] L with
      | some L1 =>
        have hL := stripPrefixSym_some _ L L1 hs1
        rw [hL]
        unfold ReachesWithin
        refine ⟨45 * m, ?_, ?_⟩
        · simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax] <;> omega
        · simp only [evalSym, evalM, encSymL, encSymR, List.cons_append, List.nil_append]
          exact sweep_CB_B12R_exact m (encSymL L1) (encSymR R1)
      | none =>
        unfold ReachesWithin
        refine ⟨0, by omega, ?_⟩
        simpa [stepPureCB, hs1] using
          pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, .rep12 m :: R1))

theorem stepPure_within (s : SymMode × List SymTok × List SymTok) :
    ReachesWithin (50 * (pilotStateFieldMax s + 1))
      ((evalSym target_tm) s)
      ((evalSym target_tm) (stepPure s)) := by
  rcases s with ⟨mode, L, R⟩
  cases mode with
  | BB => simpa [stepPure] using stepPureBB_within L R
  | DL => simpa [stepPure] using stepPureDL_within L R
  | CB => simpa [stepPure] using stepPureCB_within L R
  | HALT =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [stepPure] using pilot_reachesIn_refl ((evalSym target_tm) (.HALT, L, R))

#print axioms stepPureBB_within
#print axioms stepPureDL_within
#print axioms stepPureCB_within
#print axioms stepPure_within



/-- The pilot's local field measure is definitionally the source-audit
measure used by the kernel-checked one-step growth theorem. -/
theorem pilotStateFieldMax_eq_source (s : SymMode × List SymTok × List SymTok) :
    pilotStateFieldMax s = BusyBeaver.SymRunAudit.stateFieldMax s := rfl

/-- Exact primitive cost for any finite iteration of stepPure. The coarse
bound is the maximum per-call cost summed over the monotonically growing
field maximum. -/
theorem stepPure_iter_within (n : Nat) (s : SymMode × List SymTok × List SymTok) :
    ReachesWithin (50 * n * (pilotStateFieldMax s + n + 1))
      ((evalSym target_tm) s)
      ((evalSym target_tm) (iterStep stepPure n s)) := by
  induction n generalizing s with
  | zero =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [iterStep] using pilot_reachesIn_refl ((evalSym target_tm) s)
  | succ n ih =>
    let M := pilotStateFieldMax s
    have hfirst : ReachesWithin (50 * (M + 1))
        ((evalSym target_tm) s)
        ((evalSym target_tm) (stepPure s)) := by
      simpa [M] using stepPure_within s
    have hgrowth : pilotStateFieldMax (stepPure s) ≤ M + 1 := by
      change BusyBeaver.SymRunAudit.stateFieldMax (stepPure s) ≤
        BusyBeaver.SymRunAudit.stateFieldMax s + 1
      exact BusyBeaver.SymRunAudit.stepPure_field_growth s
    have htail := ih (stepPure s)
    have htailBound :
        pilotStateFieldMax (stepPure s) + n + 1 ≤ M + n + 2 := by omega
    have htail' : ReachesWithin (50 * n * (M + n + 2))
        ((evalSym target_tm) (stepPure s))
        ((evalSym target_tm) (iterStep stepPure n (stepPure s))) :=
      reachesWithin_mono (Nat.mul_le_mul_left (50 * n) htailBound) htail
    have hcomp := reachesWithin_trans hfirst htail'
    have hM : M + 1 ≤ M + n + 2 := by omega
    have hB :
        50 * (M + 1) + 50 * n * (M + n + 2) ≤
          50 * (n + 1) * (M + n + 2) := by
      calc
        50 * (M + 1) + 50 * n * (M + n + 2) ≤
            50 * (M + n + 2) + 50 * n * (M + n + 2) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left 50 hM) _
        _ = 50 * (n + 1) * (M + n + 2) := by ring
    have hcomp' := reachesWithin_mono hB hcomp
    simpa [M, iterStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcomp'

/-- If a rule-A/B/C macro starts with field maximum at most
512 (M0+1) and performs at most 64,512 (M0+1) pure steps, its entire
primitive cost is below 2^38 (M0+1)^2. -/
theorem stepPure_iter_within_2pow38
    (n M0 : Nat) (s : SymMode × List SymTok × List SymTok)
    (hM : pilotStateFieldMax s ≤ 512 * (M0 + 1))
    (hn : n ≤ 64512 * (M0 + 1)) :
    ReachesWithin (2^38 * (M0 + 1)^2)
      ((evalSym target_tm) s)
      ((evalSym target_tm) (iterStep stepPure n s)) := by
  have hfield : pilotStateFieldMax s + n + 1 ≤ 65025 * (M0 + 1) := by omega
  have hiter := stepPure_iter_within n s
  have hprod : n * (pilotStateFieldMax s + n + 1) ≤
      (64512 * (M0 + 1)) * (65025 * (M0 + 1)) :=
    Nat.mul_le_mul hn hfield
  have hconst : 50 * 64512 * 65025 ≤ 2^38 := by norm_num
  have hcost : 50 * n * (pilotStateFieldMax s + n + 1) ≤
      2^38 * (M0 + 1)^2 := by
    calc
      50 * n * (pilotStateFieldMax s + n + 1) =
          50 * (n * (pilotStateFieldMax s + n + 1)) := by ring
      _ ≤ 50 * ((64512 * (M0 + 1)) * (65025 * (M0 + 1))) :=
        Nat.mul_le_mul_left 50 hprod
      _ = (50 * 64512 * 65025) * (M0 + 1)^2 := by ring
      _ ≤ 2^38 * (M0 + 1)^2 := Nat.mul_le_mul_right ((M0 + 1)^2) hconst
  exact reachesWithin_mono hcost hiter

#print axioms pilotStateFieldMax_eq_source
#print axioms stepPure_iter_within
#print axioms stepPure_iter_within_2pow38



/-! A compact arithmetic lemma for charging one bounded sweep step plus a
    recursively processed suffix. -/

theorem pilot_budget_cons (M M' n c : Nat)
    (hM : M' ≤ M) (hc : c ≤ 50 * (M + 1)) :
    c + 50 * (M' + 1) * (n + 1) ≤ 50 * (M + 1) * (n + 2) := by
  have hfactor : 50 * (M' + 1) ≤ 50 * (M + 1) :=
    Nat.mul_le_mul_left 50 (Nat.add_le_add_right hM 1)
  have hrest :
      50 * (M' + 1) * (n + 1) ≤ 50 * (M + 1) * (n + 1) :=
    Nat.mul_le_mul_right (n + 1) hfactor
  calc
    c + 50 * (M' + 1) * (n + 1) ≤
        50 * (M + 1) + 50 * (M + 1) * (n + 1) :=
      Nat.add_le_add hc hrest
    _ = 50 * (M + 1) * (n + 2) := by ring

theorem pilot_budget_cons2 (M M' n c : Nat)
    (hM : M' ≤ M) (hc : c ≤ 50 * (M + 1)) :
    c + 50 * (M' + 1) * (n + 1) ≤ 50 * (M + 1) * (n + 3) := by
  have h := pilot_budget_cons M M' n c hM hc
  calc
    c + 50 * (M' + 1) * (n + 1) ≤ 50 * (M + 1) * (n + 2) := h
    _ ≤ 50 * (M + 1) * (n + 3) :=
      Nat.mul_le_mul_left (50 * (M + 1)) (by omega)

/-- BB element processing has a uniform 9-step bound, independent of fields. -/
theorem stepElemBB_within9 (L R : List SymTok) :
    ReachesWithin 9
      ((evalSym target_tm) (.BB, L, R))
      ((evalSym target_tm) (stepElemBB L R)) := by
  unfold ReachesWithin
  cases L with
  | nil =>
    refine ⟨1, by omega, ?_⟩
    simpa only [stepElemBB, strictList_eq, evalSym, evalM, encSymL, encSymR_bumpSymR] using
      step_BB_nil_exact (encSymR R)
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        refine ⟨1, by omega, ?_⟩
        simpa only [stepElemBB, strictList_eq, evalSym, evalM, encSymL, encSymR_bumpSymR] using
          step_BB_zero_exact (encSymL L1) (encSymR R)
      | run d =>
        rcases d with _ | _ | _ | _ | d
        · refine ⟨8, by omega, ?_⟩
          simpa only [stepElemBB, strictList_eq, strictNat_eq, evalSym, evalM,
            encSymL, encSymR, encSymR_bumpSymR] using
            step_BB_run0_exact (encSymL L1) (encSymR R)
        · refine ⟨3, by omega, ?_⟩
          simpa only [stepElemBB, strictList_eq, strictNat_eq, evalSym, evalM,
            encSymL, encSymR, encSymR_bumpSymR] using
            step_BB_run1_exact (encSymL L1) (encSymR R)
        · refine ⟨5, by omega, ?_⟩
          simpa only [stepElemBB, strictList_eq, strictNat_eq, evalSym, evalM,
            encSymL, encSymR, encSymR_bumpSymR] using
            step_BB_run2_exact (encSymL L1) (encSymR R)
        · refine ⟨9, by omega, ?_⟩
          simpa only [stepElemBB, strictList_eq, strictNat_eq, evalSym, evalM,
            encSymL, encSymR, encSymR_bumpSymR] using
            step_BB_run3_exact (encSymL L1) (encSymR R)
        · refine ⟨9, by omega, ?_⟩
          simpa only [stepElemBB, strictList_eq, strictNat_eq, evalSym, evalM,
            encSymL, encSymR, encSymR_bumpSymR] using
            step_BB_run_ge4_exact d (encSymL L1) (encSymR R)
    | repB1 k =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemBB] using
        pilot_reachesIn_refl ((evalSym target_tm) (.BB, .repB1 k :: L1, R))
    | rep2 p =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemBB] using
        pilot_reachesIn_refl ((evalSym target_tm) (.BB, .rep2 p :: L1, R))
    | rep12 m =>
      refine ⟨0, by omega, ?_⟩
      simpa [stepElemBB] using
        pilot_reachesIn_refl ((evalSym target_tm) (.BB, .rep12 m :: L1, R))

#print axioms pilot_budget_cons
#print axioms pilot_budget_cons2
#print axioms stepElemBB_within9




theorem pilot_budget_floor (M n : Nat) :
    9 ≤ 50 * (M + 1) * (n + 1) := by
  have hM : 1 ≤ M + 1 := by omega
  have hn : 1 ≤ n + 1 := by omega
  have hprod : 1 ≤ (M + 1) * (n + 1) := by
    calc
      1 = 1 * 1 := by omega
      _ ≤ (M + 1) * (n + 1) := Nat.mul_le_mul hM hn
  have h50 : 50 ≤ 50 * ((M + 1) * (n + 1)) :=
    Nat.mul_le_mul_left 50 hprod
  have h50' : 50 ≤ 50 * (M + 1) * (n + 1) := by
    simpa [Nat.mul_assoc] using h50
  omega

/-- Costed outer BB sweep: each consumed left token charges at most
    50*(left maximum field + 1), including repeated-block transfers. -/
theorem sweepBB_within (L R : List SymTok) :
    ReachesWithin
      (50 * (pilotListFieldMax L + 1) * (L.length + 1))
      ((evalSym target_tm) (.BB, L, R))
      ((evalSym target_tm) (sweepBB L R)) := by
  induction L generalizing R with
  | nil =>
    have h := stepElemBB_within9 [] R
    have h' : ReachesWithin 9
        ((evalSym target_tm) (.BB, [], R))
        ((evalSym target_tm) (sweepBB [] R)) := by
      simpa [sweepBB] using h
    exact reachesWithin_mono (by norm_num [pilotListFieldMax]) h'
  | cons t L1 ih =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        have h := stepElemBB_within9 (.item .zero :: L1) R
        have h' : ReachesWithin 9
            ((evalSym target_tm) (.BB, .item .zero :: L1, R))
            ((evalSym target_tm) (sweepBB (.item .zero :: L1) R)) := by
          simpa [sweepBB] using h
        exact reachesWithin_mono
          (pilot_budget_floor (pilotListFieldMax (.item .zero :: L1))
            ((.item .zero :: L1).length)) h'
      | run d =>
        rcases d with _ | _ | d
        · have h1 : ReachesWithin 8
              ((evalSym target_tm) (.BB, .item (.run 0) :: L1, R))
              ((evalSym target_tm) (.BB, L1, .item (.run 0) :: R)) :=
            reachesWithin_of_exact (by omega)
              (by
                simpa only [evalSym, evalM, encSymL, encSymR] using
                  step_BB_run0_exact (encSymL L1) (encSymR R))
          have h2 := ih (.item (.run 0) :: R)
          have hM : pilotListFieldMax L1 ≤
              pilotListFieldMax (.item (.run 0) :: L1) := by
            simp [pilotListFieldMax, pilotTokFieldMax]
          have hcost : 8 ≤ 50 * (pilotListFieldMax (.item (.run 0) :: L1) + 1) := by
            omega
          have hbudget := pilot_budget_cons
            (pilotListFieldMax (.item (.run 0) :: L1)) (pilotListFieldMax L1)
            L1.length 8 hM hcost
          have hcomp := reachesWithin_trans h1 h2
          have hfinal := reachesWithin_mono
            (by simpa [List.length] using hbudget) hcomp
          simpa [sweepBB] using hfinal
        · have h1 : ReachesWithin 3
              ((evalSym target_tm) (.BB, .item (.run 1) :: L1, R))
              ((evalSym target_tm) (.BB, L1, .item (.run 0) :: bumpSymR R)) :=
            reachesWithin_of_exact (by omega)
              (by
                simpa only [evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR] using
                  step_BB_run1_exact (encSymL L1) (encSymR R))
          have h2 := ih (.item (.run 0) :: bumpSymR R)
          have hM : pilotListFieldMax L1 ≤
              pilotListFieldMax (.item (.run 1) :: L1) := by
            simp [pilotListFieldMax, pilotTokFieldMax]
          have hcost : 3 ≤ 50 * (pilotListFieldMax (.item (.run 1) :: L1) + 1) := by
            omega
          have hbudget := pilot_budget_cons
            (pilotListFieldMax (.item (.run 1) :: L1)) (pilotListFieldMax L1)
            L1.length 3 hM hcost
          have hcomp := reachesWithin_trans h1 h2
          have hfinal := reachesWithin_mono
            (by simpa [List.length] using hbudget) hcomp
          simpa only [sweepBB, strictList_eq] using hfinal
        · have h := stepElemBB_within9 (.item (.run (d + 2)) :: L1) R
          have h' : ReachesWithin 9
              ((evalSym target_tm) (.BB, .item (.run (d + 2)) :: L1, R))
              ((evalSym target_tm) (sweepBB (.item (.run (d + 2)) :: L1) R)) := by
            simpa [sweepBB, strictNat_eq] using h
          exact reachesWithin_mono
            (pilot_budget_floor (pilotListFieldMax (.item (.run (d + 2)) :: L1))
              ((.item (.run (d + 2)) :: L1).length)) h'
    | repB1 k =>
      have h1 : ReachesWithin (11 * k)
          ((evalSym target_tm) (.BB, .repB1 k :: L1, R))
          ((evalSym target_tm) (.BB, L1, eatB1 k R)) :=
        reachesWithin_of_exact (by omega) (by
          simp only [evalSym, evalM, encSymL, encSymR_eatB1]
          exact sweep_BB_B1_exact k (encSymL L1) (encSymR R))
      have h2 := ih (eatB1 k R)
      have hM : pilotListFieldMax L1 ≤ pilotListFieldMax (.repB1 k :: L1) := by
        simp [pilotListFieldMax, pilotTokFieldMax]
      have hk : k ≤ pilotListFieldMax (.repB1 k :: L1) := by
        simp [pilotListFieldMax, pilotTokFieldMax]
      have hcost : 11 * k ≤ 50 * (pilotListFieldMax (.repB1 k :: L1) + 1) := by
        omega
      have hbudget := pilot_budget_cons
        (pilotListFieldMax (.repB1 k :: L1)) (pilotListFieldMax L1)
        L1.length (11 * k) hM hcost
      have hcomp := reachesWithin_trans h1 h2
      have hfinal := reachesWithin_mono
        (by simpa [List.length] using hbudget) hcomp
      simpa only [sweepBB, strictList_eq] using hfinal
    | rep2 p =>
      simp only [sweepBB]
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hs
        have h1 : ReachesWithin (14 * p)
            ((evalSym target_tm) (.BB, .rep2 p :: L1, R))
            ((evalSym target_tm)
              (.BB, L1, .item (.run 0) :: .item (.run 1) :: eatB2 p R2)) :=
          reachesWithin_of_exact (by omega) (by
            rw [hR]
            simp only [evalSym, evalM, encSymL, encSymR, encSymR_eatB2,
              List.cons_append, List.nil_append]
            exact sweep_BB_C2_exact p (encSymL L1) (encSymR R2))
        have h2 := ih (.item (.run 0) :: .item (.run 1) :: eatB2 p R2)
        have hM : pilotListFieldMax L1 ≤ pilotListFieldMax (.rep2 p :: L1) := by
          simp [pilotListFieldMax, pilotTokFieldMax]
        have hcost : 14 * p ≤ 50 * (pilotListFieldMax (.rep2 p :: L1) + 1) := by
          have hp : p ≤ pilotListFieldMax (.rep2 p :: L1) := by
            simp [pilotListFieldMax, pilotTokFieldMax]
          omega
        have hbudget := pilot_budget_cons
          (pilotListFieldMax (.rep2 p :: L1)) (pilotListFieldMax L1)
          L1.length (14 * p) hM hcost
        have hcomp := reachesWithin_trans h1 h2
        have hfinal := reachesWithin_mono
          (by simpa [List.length] using hbudget) hcomp
        simpa only [strictList_eq] using hfinal
      | none =>
        have heq : (evalSym target_tm) (.BB, .rep2 p :: L1, R) =
            (evalSym target_tm) (.BB, peelTok (.rep2 p) L1, R) := by
          simp only [evalSym, encSymL_peelTok]
        rw [heq]
        have h := stepElemBB_within9 (peelTok (.rep2 p) L1) R
        have h' : ReachesWithin 9
            ((evalSym target_tm) (.BB, peelTok (.rep2 p) L1, R))
            ((evalSym target_tm) (sweepBB (.rep2 p :: L1) R)) := by
          simpa [sweepBB, strictList_eq] using h
        exact reachesWithin_mono
          (pilot_budget_floor (pilotListFieldMax (.rep2 p :: L1))
            ((.rep2 p :: L1).length)) h'
    | rep12 m =>
      simp only [sweepBB]
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hs
        have h1 : ReachesWithin (25 * m)
            ((evalSym target_tm) (.BB, .rep12 m :: L1, R))
            ((evalSym target_tm)
              (.BB, L1, .item (.run 0) :: .item (.run 1) :: eatB12R m R2)) :=
          reachesWithin_of_exact (by omega) (by
            rw [hR]
            simp only [evalSym, evalM, encSymL, encSymR, encSymR_eatB12R,
              List.cons_append, List.nil_append]
            exact sweep_BB_C12_exact m (encSymL L1) (encSymR R2))
        have h2 := ih (.item (.run 0) :: .item (.run 1) :: eatB12R m R2)
        have hM : pilotListFieldMax L1 ≤ pilotListFieldMax (.rep12 m :: L1) := by
          simp [pilotListFieldMax, pilotTokFieldMax]
        have hcost : 25 * m ≤ 50 * (pilotListFieldMax (.rep12 m :: L1) + 1) := by
          have hm : m ≤ pilotListFieldMax (.rep12 m :: L1) := by
            simp [pilotListFieldMax, pilotTokFieldMax]
          omega
        have hbudget := pilot_budget_cons
          (pilotListFieldMax (.rep12 m :: L1)) (pilotListFieldMax L1)
          L1.length (25 * m) hM hcost
        have hcomp := reachesWithin_trans h1 h2
        have hfinal := reachesWithin_mono
          (by simpa [List.length] using hbudget) hcomp
        simpa only [strictList_eq] using hfinal
      | none =>
        have heq : (evalSym target_tm) (.BB, .rep12 m :: L1, R) =
            (evalSym target_tm) (.BB, peelTok (.rep12 m) L1, R) := by
          simp only [evalSym, encSymL_peelTok]
        rw [heq]
        have h := stepElemBB_within9 (peelTok (.rep12 m) L1) R
        have h' : ReachesWithin 9
            ((evalSym target_tm) (.BB, peelTok (.rep12 m) L1, R))
            ((evalSym target_tm) (sweepBB (.rep12 m :: L1) R)) := by
          simpa [sweepBB, strictList_eq] using h
        exact reachesWithin_mono
          (pilot_budget_floor (pilotListFieldMax (.rep12 m :: L1))
            ((.rep12 m :: L1).length)) h'

#print axioms pilot_budget_floor
#print axioms sweepBB_within




/-- Costed outer CB sweep. Its recursion consumes only the right stack, so
    every run/repeat parameter charged by a branch is bounded by the initial
    right-stack maximum field. -/

/-- Finishing a symbolic element transition only runs a BB sweep when
    the intermediate mode is BB. -/

/-- The BB branch of the outer stepSym map inherits the linear sweep cost
    when the input trace has at most 94 symbolic tokens. -/
theorem stepSym_BB_within (L R : List SymTok)
    (hT : L.length + R.length ≤ 94) :
    ReachesWithin
      (2^13 * (pilotStateFieldMax (.BB, L, R) + 1))
      ((evalSym target_tm) (.BB, L, R))
      ((evalSym target_tm) (stepSym (.BB, L, R))) := by
  let M := pilotStateFieldMax (.BB, L, R)
  have hL : L.length ≤ 94 := by omega
  have hField : pilotListFieldMax L ≤ M := Nat.le_max_left _ _
  have hprod :
      (pilotListFieldMax L + 1) * (L.length + 1) ≤ (M + 1) * 95 :=
    Nat.mul_le_mul (Nat.add_le_add_right hField 1) (by omega)
  have hconst : 50 * 95 ≤ 2^13 := by norm_num
  have hbudget :
      50 * (pilotListFieldMax L + 1) * (L.length + 1) ≤ 2^13 * (M + 1) := by
    calc
      50 * (pilotListFieldMax L + 1) * (L.length + 1)
        = 50 * ((pilotListFieldMax L + 1) * (L.length + 1)) := by ring
      _ ≤ 50 * ((M + 1) * 95) := Nat.mul_le_mul_left 50 hprod
      _ = (50 * 95) * (M + 1) := by ring
      _ ≤ 2^13 * (M + 1) := Nat.mul_le_mul_right (M + 1) hconst
  have h := sweepBB_within L R
  have h' := reachesWithin_mono (by simpa [M] using hbudget) h
  simpa [stepSym, M] using h'

#print axioms stepSym_BB_within

theorem finishThenBB_within (s : SymMode × List SymTok × List SymTok) :
    ReachesWithin
      (if s.1 = .BB then
        50 * (pilotListFieldMax s.2.1 + 1) * (s.2.1.length + 1)
       else 0)
      ((evalSym target_tm) s)
      ((evalSym target_tm) (finishThenBB s)) := by
  rcases s with ⟨mode, L, R⟩
  cases mode with
  | BB =>
    simpa [finishThenBB] using sweepBB_within L R
  | DL =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [finishThenBB] using
      pilot_reachesIn_refl ((evalSym target_tm) (.DL, L, R))
  | CB =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [finishThenBB] using
      pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, R))
  | HALT =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [finishThenBB] using
      pilot_reachesIn_refl ((evalSym target_tm) (.HALT, L, R))

/-- A BB result from one DL element transition can only come from a
    leading run-0 token; in that case the BB sweep sees its unchanged tail. -/
theorem stepElemDL_BB_left_bounds (L R : List SymTok)
    (hBB : (stepElemDL L R).1 = .BB) :
    pilotListFieldMax (stepElemDL L R).2.1 ≤ pilotListFieldMax L ∧
      (stepElemDL L R).2.1.length + 1 ≤ L.length := by
  cases L with
  | nil => simp [stepElemDL] at hBB
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero => simp [stepElemDL] at hBB
      | run d =>
        cases d with
        | zero =>
          simp [stepElemDL, strictList_eq, pilotListFieldMax, pilotTokFieldMax] at hBB ⊢
        | succ d =>
          cases d with
          | zero => simp [stepElemDL] at hBB
          | succ d =>
            cases d with
            | zero =>
              cases R with
              | nil => simp [stepElemDL] at hBB
              | cons rt R1 =>
                cases rt with
                | item it =>
                  cases it with
                  | zero => simp [stepElemDL] at hBB
                  | run d0 => simp [stepElemDL, strictList_eq] at hBB
                | repB1 k => simp [stepElemDL] at hBB
                | rep2 p => simp [stepElemDL] at hBB
                | rep12 m => simp [stepElemDL] at hBB
            | succ d => simp [stepElemDL] at hBB
    | repB1 k => simp [stepElemDL] at hBB
    | rep2 p => simp [stepElemDL] at hBB
    | rep12 m => simp [stepElemDL] at hBB

/-- One DL element followed by its optional BB sweep. -/
theorem stepElemThenBB_DL_within (L R : List SymTok) :
    ReachesWithin
      (50 * (pilotStateFieldMax (.DL, L, R) + 1) * (L.length + 2))
      ((evalSym target_tm) (.DL, L, R))
      ((evalSym target_tm) (stepElemThenBB .DL L R)) := by
  let M := pilotStateFieldMax (.DL, L, R)
  have h1 := stepElemDL_within25 L R
  have h1' : ReachesWithin (25 * (M + 1))
      ((evalSym target_tm) (.DL, L, R))
      ((evalSym target_tm) (stepElemDL L R)) := by
    simpa [M] using h1
  have h2 := finishThenBB_within (stepElemDL L R)
  have hcomp := reachesWithin_trans h1' h2
  have h1Budget : 25 * (M + 1) ≤ 50 * (M + 1) := by omega
  have h2Budget :
      (if (stepElemDL L R).1 = .BB then
        50 * (pilotListFieldMax (stepElemDL L R).2.1 + 1) *
          ((stepElemDL L R).2.1.length + 1)
       else 0) ≤ 50 * (M + 1) * L.length := by
    by_cases hBB : (stepElemDL L R).1 = .BB
    · have hBounds := stepElemDL_BB_left_bounds L R hBB
      have hField : pilotListFieldMax (stepElemDL L R).2.1 ≤ M :=
        Nat.le_trans hBounds.1 (Nat.le_max_left _ _)
      have hLen : (stepElemDL L R).2.1.length + 1 ≤ L.length := hBounds.2
      simp [hBB]
      have hprod := Nat.mul_le_mul
        (Nat.add_le_add_right hField 1) hLen
      calc
        50 * (pilotListFieldMax (stepElemDL L R).2.1 + 1) *
            ((stepElemDL L R).2.1.length + 1)
          = 50 * ((pilotListFieldMax (stepElemDL L R).2.1 + 1) *
              ((stepElemDL L R).2.1.length + 1)) := by ring
        _ ≤ 50 * ((M + 1) * L.length) := Nat.mul_le_mul_left 50 hprod
        _ = 50 * (M + 1) * L.length := by ring
    · simp [hBB]
  have htotal :
      50 * (M + 1) + 50 * (M + 1) * L.length ≤
        50 * (M + 1) * (L.length + 2) := by
    calc
      _ = 50 * (M + 1) * (L.length + 1) := by ring
      _ ≤ 50 * (M + 1) * (L.length + 2) :=
        Nat.mul_le_mul_left (50 * (M + 1)) (by omega)
  have hbudget := Nat.add_le_add h1Budget h2Budget
  have hcomp' : ReachesWithin
      (25 * (M + 1) +
        (if (stepElemDL L R).1 = .BB then
          50 * (pilotListFieldMax (stepElemDL L R).2.1 + 1) *
            ((stepElemDL L R).2.1.length + 1)
         else 0))
      ((evalSym target_tm) (.DL, L, R))
      ((evalSym target_tm) (finishThenBB (stepElemDL L R))) := by
    simpa [M] using hcomp
  have hfinal := reachesWithin_mono (Nat.le_trans hbudget htotal) hcomp'
  simpa [stepElemThenBB, stepElemSym, M] using hfinal

/-- The DL branch of the outer stepSym map has a linear primitive-time
    bound whenever the trace token count is at most 94. -/

/-- When a CB element transition finishes in BB, its new left stack grows
    by at most two tokens (the run-0 exit can prepend two literals). -/
theorem stepElemCB_BB_left_length (L R : List SymTok)
    (hBB : (stepElemCB L R).1 = .BB) :
    (stepElemCB L R).2.1.length ≤ L.length + 3 := by
  cases R with
  | nil => simp [stepElemCB] at hBB
  | cons t R1 =>
    cases t with
    | item it =>
      cases it with
      | zero => simp [stepElemCB] at hBB
      | run d =>
        cases d with
        | zero =>
          cases R1 with
          | nil =>
            simp [stepElemCB, stepElemCB_run0, strictList_eq, bumpSymL] at hBB ⊢
          | cons rt R2 =>
            cases rt with
            | item it2 =>
              cases it2 with
              | zero =>
                simp [stepElemCB, stepElemCB_run0, strictList_eq, bumpSymL] at hBB ⊢
              | run d2 =>
                cases d2 with
                | zero =>
                  simp [stepElemCB, stepElemCB_run0, strictList_eq, bumpSymL] at hBB ⊢
                | succ d2 =>
                  simp [stepElemCB, stepElemCB_run0, strictList_eq] at hBB
            | repB1 k => simp [stepElemCB, stepElemCB_run0] at hBB
            | rep2 p => simp [stepElemCB, stepElemCB_run0] at hBB
            | rep12 m => simp [stepElemCB, stepElemCB_run0] at hBB
        | succ d =>
          cases d with
          | zero => simp [stepElemCB] at hBB
          | succ d =>
            cases d with
            | zero =>
              simp [stepElemCB, strictList_eq, bumpSymL] at hBB ⊢
            | succ d =>
              simp [stepElemCB, strictList_eq, strictNat_eq, bumpSymL] at hBB ⊢
    | repB1 k => simp [stepElemCB] at hBB
    | rep2 p => simp [stepElemCB] at hBB
    | rep12 m => simp [stepElemCB] at hBB

/-- A CB element followed by its optional BB sweep has a simple cost in
    terms of the input field maximum and left-stack length. -/
theorem stepElemThenBB_CB_within (L R : List SymTok) :
    ReachesWithin
      (2^9 * (pilotStateFieldMax (.CB, L, R) + 1) * (L.length + 4))
      ((evalSym target_tm) (.CB, L, R))
      ((evalSym target_tm) (stepElemThenBB .CB L R)) := by
  let M := pilotStateFieldMax (.CB, L, R)
  have h1 := stepElemCB_within25 L R
  have h1' : ReachesWithin (25 * (M + 1))
      ((evalSym target_tm) (.CB, L, R))
      ((evalSym target_tm) (stepElemCB L R)) := by
    simpa [M] using h1
  have h2 := finishThenBB_within (stepElemCB L R)
  have hcomp := reachesWithin_trans h1' h2
  have hGrowth : pilotStateFieldMax (stepElemCB L R) ≤ M + 1 := by
    change BusyBeaver.SymRunAudit.stateFieldMax (stepPure (.CB, L, R)) ≤
      BusyBeaver.SymRunAudit.stateFieldMax (.CB, L, R) + 1
    exact BusyBeaver.SymRunAudit.stepPure_field_growth (.CB, L, R)
  have hField :
      pilotListFieldMax (stepElemCB L R).2.1 ≤ M + 1 :=
    Nat.le_trans (Nat.le_max_left _ _) hGrowth
  have h2Budget :
      (if (stepElemCB L R).1 = .BB then
        50 * (pilotListFieldMax (stepElemCB L R).2.1 + 1) *
          ((stepElemCB L R).2.1.length + 1)
       else 0) ≤ 100 * (M + 1) * (L.length + 4) := by
    by_cases hBB : (stepElemCB L R).1 = .BB
    · have hLen :
          (stepElemCB L R).2.1.length + 1 ≤ L.length + 4 := by
        have h := stepElemCB_BB_left_length L R hBB
        omega
      have hprod := Nat.mul_le_mul
        (Nat.add_le_add_right hField 1) hLen
      simp [hBB]
      calc
        50 * (pilotListFieldMax (stepElemCB L R).2.1 + 1) *
            ((stepElemCB L R).2.1.length + 1)
          = 50 * ((pilotListFieldMax (stepElemCB L R).2.1 + 1) *
              ((stepElemCB L R).2.1.length + 1)) := by ring
        _ ≤ 50 * ((M + 2) * (L.length + 4)) :=
          Nat.mul_le_mul_left 50 hprod
        _ ≤ 100 * (M + 1) * (L.length + 3) := by
          have hM : M + 2 ≤ 2 * (M + 1) := by omega
          have hmul := Nat.mul_le_mul_right (L.length + 3) hM
          calc
            50 * ((M + 2) * (L.length + 3))
              = 50 * ((M + 2) * (L.length + 3)) := rfl
            _ ≤ 50 * (2 * (M + 1) * (L.length + 3)) :=
              Nat.mul_le_mul_left 50 hmul
            _ = 100 * (M + 1) * (L.length + 3) := by ring
    · simp [hBB]
  have h1Budget :
      25 * (M + 1) ≤ 25 * (M + 1) * (L.length + 3) := by
    exact Nat.mul_le_mul_left (25 * (M + 1)) (by omega)
  have htotal :
      25 * (M + 1) * (L.length + 3) +
        100 * (M + 1) * (L.length + 4) ≤
          2^9 * (M + 1) * (L.length + 3) := by
    calc
      _ = 125 * (M + 1) * (L.length + 3) := by ring
      _ ≤ 2^9 * (M + 1) * (L.length + 3) := by
        exact Nat.mul_le_mul_right ((M + 1) * (L.length + 3)) (by norm_num)
  have hbudget := Nat.add_le_add h1Budget h2Budget
  have hcomp' : ReachesWithin
      (25 * (M + 1) +
        (if (stepElemCB L R).1 = .BB then
          50 * (pilotListFieldMax (stepElemCB L R).2.1 + 1) *
            ((stepElemCB L R).2.1.length + 1)
         else 0))
      ((evalSym target_tm) (.CB, L, R))
      ((evalSym target_tm) (finishThenBB (stepElemCB L R))) := by
    simpa [M] using hcomp
  have hfinal := reachesWithin_mono (Nat.le_trans hbudget htotal) hcomp'
  simpa [stepElemThenBB, stepElemSym, M] using hfinal

#print axioms stepElemCB_run0_within25
#print axioms stepElemCB_within25
#print axioms stepElemCB_BB_left_length
#print axioms stepElemThenBB_CB_within

theorem stepSym_DL_within (L R : List SymTok)
    (hT : L.length + R.length ≤ 94) :
    ReachesWithin
      (2^13 * (pilotStateFieldMax (.DL, L, R) + 1))
      ((evalSym target_tm) (.DL, L, R))
      ((evalSym target_tm) (stepSym (.DL, L, R))) := by
  let M := pilotStateFieldMax (.DL, L, R)
  have hField := pilotStateFieldMax_peelL_left_mono .DL L R
  have hLen := pilot_peelL_length_le L
  have hL : L.length ≤ 94 := by omega
  have hFactor : (peelL L).length + 2 ≤ 101 := by omega
  have hprod :
      (pilotStateFieldMax (.DL, peelL L, R) + 1) *
          ((peelL L).length + 2) ≤ (M + 1) * 101 :=
    Nat.mul_le_mul (Nat.add_le_add_right hField 1) hFactor
  have hconst : 50 * 101 ≤ 2^13 := by norm_num
  have hbudget :
      50 * (pilotStateFieldMax (.DL, peelL L, R) + 1) *
          ((peelL L).length + 2) ≤ 2^13 * (M + 1) := by
    calc
      50 * (pilotStateFieldMax (.DL, peelL L, R) + 1) *
          ((peelL L).length + 2)
        = 50 * ((pilotStateFieldMax (.DL, peelL L, R) + 1) *
            ((peelL L).length + 2)) := by ring
      _ ≤ 50 * ((M + 1) * 101) := Nat.mul_le_mul_left 50 hprod
      _ = (50 * 101) * (M + 1) := by ring
      _ ≤ 2^13 * (M + 1) := Nat.mul_le_mul_right (M + 1) hconst
  have hstep := stepElemThenBB_DL_within (peelL L) R
  have hstep' := reachesWithin_mono (by simpa [M] using hbudget) hstep
  simpa [stepSym, strictList_eq, M] using hstep'

#print axioms stepElemDL_within25
#print axioms finishThenBB_within
#print axioms stepElemDL_BB_left_bounds
#print axioms stepElemThenBB_DL_within
#print axioms stepSym_DL_within


theorem sweepCB_within (L R : List SymTok) :
    ReachesWithin
      (50 * (pilotListFieldMax R + 1) * (R.length + 1))
      ((evalSym target_tm) (.CB, L, R))
      ((evalSym target_tm) (.CB, (sweepCB L R).1, (sweepCB L R).2)) := by
  induction L, R using sweepCB.induct with
  | case1 L =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [sweepCB] using pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, []))
  | case2 L R1 =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [sweepCB] using
      pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, .item .zero :: R1))
  | case3 L R2 ih =>
    simp only [sweepCB, strictList_eq]
    have h1 : ReachesWithin 21
        ((evalSym target_tm) (.CB, L, .item (.run 0) :: .item (.run 1) :: R2))
        ((evalSym target_tm)
          (.CB, .item (.run 0) :: .item (.run 0) :: bumpSymL L, R2)) :=
      reachesWithin_of_exact (by omega) (by
        simp only [evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL]
        simpa using
          step_CB_run0_run_pos_exact 0 (encSymL L) (encSymR R2))
    have h2 := ih (bumpSymL L)
    have hM : pilotListFieldMax R2 ≤
        pilotListFieldMax (.item (.run 0) :: .item (.run 1) :: R2) := by
      simp [pilotListFieldMax, pilotTokFieldMax]
    have hcost : 21 ≤
        50 * (pilotListFieldMax (.item (.run 0) :: .item (.run 1) :: R2) + 1) := by
      omega
    have hbudget := pilot_budget_cons2
      (pilotListFieldMax (.item (.run 0) :: .item (.run 1) :: R2))
      (pilotListFieldMax R2) R2.length 21 hM hcost
    have hcomp := reachesWithin_trans h1 h2
    exact reachesWithin_mono (by simpa [List.length] using hbudget) hcomp
  | case4 L R1 hnot =>
    have heq : sweepCB L (.item (.run 0) :: R1) = (L, .item (.run 0) :: R1) := by
      cases R1 with
      | nil => rfl
      | cons y R2 =>
        cases y with
        | item it =>
          cases it with
          | zero => rfl
          | run d =>
            rcases d with _ | _ | d
            · rfl
            · exfalso
              exact hnot R2 rfl
            · rfl
        | repB1 _ => rfl
        | rep2 _ => rfl
        | rep12 _ => rfl
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    rw [heq]
    exact pilot_reachesIn_refl
      ((evalSym target_tm) (.CB, L, .item (.run 0) :: R1))
  | case5 L R1 ih =>
    simp only [sweepCB, strictList_eq]
    have h1 : ReachesWithin 3
        ((evalSym target_tm) (.CB, L, .item (.run 1) :: R1))
        ((evalSym target_tm) (.CB, .item (.run 0) :: bumpSymL L, R1)) :=
      reachesWithin_of_exact (by omega) (by
        simp only [evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL]
        exact step_CB_run1_exact (encSymL L) (encSymR R1))
    have h2 := ih (bumpSymL L)
    have hM : pilotListFieldMax R1 ≤
        pilotListFieldMax (.item (.run 1) :: R1) := by
      simp [pilotListFieldMax, pilotTokFieldMax]
    have hcost : 3 ≤ 50 * (pilotListFieldMax (.item (.run 1) :: R1) + 1) := by
      omega
    have hbudget := pilot_budget_cons
      (pilotListFieldMax (.item (.run 1) :: R1)) (pilotListFieldMax R1)
      R1.length 3 hM hcost
    have hcomp := reachesWithin_trans h1 h2
    exact reachesWithin_mono (by simpa [List.length] using hbudget) hcomp
  | case6 L d R1 =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [sweepCB] using
      pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, .item (.run (d + 2)) :: R1))
  | case7 L k R1 L1 hstrip ih =>
    have hL := stripPrefixSym_some _ L L1 hstrip
    simp only [sweepCB, hstrip, strictList_eq]
    have h1 : ReachesWithin (21 * k)
        ((evalSym target_tm) (.CB, L, .repB1 k :: R1))
        ((evalSym target_tm) (.CB, .item (.run 0) :: eatB1 k L1, R1)) := by
      rw [hL]
      apply reachesWithin_of_exact (by omega)
      simp only [evalSym, evalM, encSymL, encSymR, encSymL_eatB1,
        List.cons_append, List.nil_append]
      exact sweep_CB_B1_exact k (encSymL L1) (encSymR R1)
    have h2 := ih (eatB1 k L1)
    have hM : pilotListFieldMax R1 ≤ pilotListFieldMax (.repB1 k :: R1) := by
      simp [pilotListFieldMax, pilotTokFieldMax]
    have hk : k ≤ pilotListFieldMax (.repB1 k :: R1) := by
      simp [pilotListFieldMax, pilotTokFieldMax]
    have hcost : 21 * k ≤ 50 * (pilotListFieldMax (.repB1 k :: R1) + 1) := by
      omega
    have hbudget := pilot_budget_cons
      (pilotListFieldMax (.repB1 k :: R1)) (pilotListFieldMax R1)
      R1.length (21 * k) hM hcost
    have hcomp := reachesWithin_trans h1 h2
    exact reachesWithin_mono (by simpa [List.length] using hbudget) hcomp
  | case8 L k R1 hstrip =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [sweepCB, hstrip] using
      pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, .repB1 k :: R1))
  | case9 L p R1 L1 hstrip ih =>
    have hL := stripPrefixSym_some _ L L1 hstrip
    simp only [sweepCB, hstrip, strictList_eq]
    have h1 : ReachesWithin (24 * p)
        ((evalSym target_tm) (.CB, L, .rep2 p :: R1))
        ((evalSym target_tm) (.CB, .item (.run 0) :: eatC2 p L1, R1)) := by
      rw [hL]
      apply reachesWithin_of_exact (by omega)
      simp only [evalSym, evalM, encSymL, encSymR, encSymL_eatC2,
        List.cons_append, List.nil_append]
      exact sweep_CB_B2_exact p (encSymL L1) (encSymR R1)
    have h2 := ih (eatC2 p L1)
    have hM : pilotListFieldMax R1 ≤ pilotListFieldMax (.rep2 p :: R1) := by
      simp [pilotListFieldMax, pilotTokFieldMax]
    have hp : p ≤ pilotListFieldMax (.rep2 p :: R1) := by
      simp [pilotListFieldMax, pilotTokFieldMax]
    have hcost : 24 * p ≤ 50 * (pilotListFieldMax (.rep2 p :: R1) + 1) := by
      omega
    have hbudget := pilot_budget_cons
      (pilotListFieldMax (.rep2 p :: R1)) (pilotListFieldMax R1)
      R1.length (24 * p) hM hcost
    have hcomp := reachesWithin_trans h1 h2
    exact reachesWithin_mono (by simpa [List.length] using hbudget) hcomp
  | case10 L p R1 hstrip =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [sweepCB, hstrip] using
      pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, .rep2 p :: R1))
  | case11 L m R1 L1 hstrip ih =>
    have hL := stripPrefixSym_some _ L L1 hstrip
    simp only [sweepCB, hstrip, strictList_eq]
    have h1 : ReachesWithin (45 * m)
        ((evalSym target_tm) (.CB, L, .rep12 m :: R1))
        ((evalSym target_tm) (.CB, .item (.run 0) :: eatC12 m L1, R1)) := by
      rw [hL]
      apply reachesWithin_of_exact (by omega)
      simp only [evalSym, evalM, encSymL, encSymR, encSymL_eatC12,
        List.cons_append, List.nil_append]
      exact sweep_CB_B12R_exact m (encSymL L1) (encSymR R1)
    have h2 := ih (eatC12 m L1)
    have hM : pilotListFieldMax R1 ≤ pilotListFieldMax (.rep12 m :: R1) := by
      simp [pilotListFieldMax, pilotTokFieldMax]
    have hm : m ≤ pilotListFieldMax (.rep12 m :: R1) := by
      simp [pilotListFieldMax, pilotTokFieldMax]
    have hcost : 45 * m ≤ 50 * (pilotListFieldMax (.rep12 m :: R1) + 1) := by
      omega
    have hbudget := pilot_budget_cons
      (pilotListFieldMax (.rep12 m :: R1)) (pilotListFieldMax R1)
      R1.length (45 * m) hM hcost
    have hcomp := reachesWithin_trans h1 h2
    exact reachesWithin_mono (by simpa [List.length] using hbudget) hcomp
  | case12 L m R1 hstrip =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [sweepCB, hstrip] using
      pilot_reachesIn_refl ((evalSym target_tm) (.CB, L, .rep12 m :: R1))

#print axioms sweepCB_within



theorem iterStep_stepPure_within_eq (n : Nat)
    (s t : SymMode × List SymTok × List SymTok)
    (h : (evalSym target_tm) (iterStep stepPure n s) =
      (evalSym target_tm) t) :
    ReachesWithin
      (50 * n * (pilotStateFieldMax s + n + 1))
      ((evalSym target_tm) s)
      ((evalSym target_tm) t) := by
  simpa [h] using stepPure_iter_within n s

theorem pilot_stateA_field_growth (m k d : Nat) (R_tail : List SymTok) :
    pilotStateFieldMax (stateA (m + 1) k d R_tail) ≤
      pilotStateFieldMax (stateA m (k + 1) (d + 6) R_tail) + 1 := by
  simp [stateA, pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax]
  omega

theorem pilot_stateC_field_growth (p k d2 : Nat) (R_tail : List SymTok) :
    pilotStateFieldMax (stateC (p + 2) (k + 3) (d2 + 2) R_tail) ≤
      pilotStateFieldMax (stateC (p + 3) (k + 1) d2 R_tail) + 2 := by
  simp [stateC, pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax]
  omega

theorem ruleA_step_within (m k d : Nat) (R_tail : List SymTok) :
    ReachesWithin
      (50 * 66 * (pilotStateFieldMax (stateA m (k + 1) (d + 6) R_tail) + 67))
      ((evalSym target_tm) (stateA m (k + 1) (d + 6) R_tail))
      ((evalSym target_tm) (stateA (m + 1) k d R_tail)) := by
  exact iterStep_stepPure_within_eq 66
    (stateA m (k + 1) (d + 6) R_tail)
    (stateA (m + 1) k d R_tail)
    (ruleA_step_eq m k d R_tail)

theorem ruleC_step_within (p k d2 : Nat) (R_tail : List SymTok) :
    ReachesWithin
      (50 * 46 * (pilotStateFieldMax (stateC (p + 3) (k + 1) d2 R_tail) + 47))
      ((evalSym target_tm) (stateC (p + 3) (k + 1) d2 R_tail))
      ((evalSym target_tm) (stateC (p + 2) (k + 3) (d2 + 2) R_tail)) := by
  exact iterStep_stepPure_within_eq 46
    (stateC (p + 3) (k + 1) d2 R_tail)
    (stateC (p + 2) (k + 3) (d2 + 2) R_tail)
    (ruleC_step_eq p k d2 R_tail)

theorem ruleA_iter_within (n m k d : Nat) (R_tail : List SymTok) :
    ReachesWithin
      (50 * 66 * n *
        (pilotStateFieldMax (stateA m (k + n) (d + 6 * n) R_tail) + n + 67))
      ((evalSym target_tm) (stateA m (k + n) (d + 6 * n) R_tail))
      ((evalSym target_tm) (stateA (m + n) k d R_tail)) := by
  induction n generalizing m k d with
  | zero =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [stateA] using pilot_reachesIn_refl
      ((evalSym target_tm) (stateA m k d R_tail))
  | succ n ih =>
    have h1eq : k + (n + 1) = (k + n) + 1 := by omega
    have h2eq : d + 6 * (n + 1) = (d + 6 * n) + 6 := by omega
    have h3eq : m + (n + 1) = (m + 1) + n := by omega
    rw [h1eq, h2eq, h3eq]
    have h1 := ruleA_step_within m (k + n) (d + 6 * n) R_tail
    have h2 := ih (m + 1) k d
    have hM := pilot_stateA_field_growth m (k + n) (d + 6 * n) R_tail
    let M := pilotStateFieldMax (stateA m ((k + n) + 1) ((d + 6 * n) + 6) R_tail)
    have h1Budget :
        50 * 66 * (pilotStateFieldMax
          (stateA m ((k + n) + 1) ((d + 6 * n) + 6) R_tail) + 67) ≤
          50 * 66 * (M + n + 68) := by
      simp [M]
      omega
    have h2Factor :
        pilotStateFieldMax (stateA (m + 1) (k + n) (d + 6 * n) R_tail) + n + 67 ≤
          M + n + 68 := by
      simpa [M, Nat.add_assoc] using Nat.add_le_add_right hM (n + 67)
    have h2Budget :
        50 * 66 * n *
          (pilotStateFieldMax (stateA (m + 1) (k + n) (d + 6 * n) R_tail) + n + 67) ≤
          50 * 66 * n * (M + n + 68) :=
      Nat.mul_le_mul_left (50 * 66 * n) h2Factor
    have hcomp := reachesWithin_trans
      (reachesWithin_mono h1Budget h1)
      (reachesWithin_mono h2Budget h2)
    have htotal :
        50 * 66 * (M + n + 68) +
          50 * 66 * n * (M + n + 68) ≤
            50 * 66 * (n + 1) * (M + n + 68) := by
      have heq :
          50 * 66 * (M + n + 68) +
            50 * 66 * n * (M + n + 68) =
              50 * 66 * (n + 1) * (M + n + 68) := by ring
      omega
    have hfinal := reachesWithin_mono htotal hcomp
    simpa [M, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal

theorem ruleC_iter_within (n p k d2 : Nat) (R_tail : List SymTok)
    (hk : 1 ≤ k) :
    ReachesWithin
      (50 * 46 * n *
        (pilotStateFieldMax (stateC (p + n + 2) k d2 R_tail) + 2 * n + 47))
      ((evalSym target_tm) (stateC (p + n + 2) k d2 R_tail))
      ((evalSym target_tm) (stateC (p + 2) (k + 2 * n) (d2 + 2 * n) R_tail)) := by
  induction n generalizing p k d2 with
  | zero =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [stateC] using pilot_reachesIn_refl
      ((evalSym target_tm) (stateC (p + 2) k d2 R_tail))
  | succ n ih =>
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    have h1eq : p + (n + 1) + 2 = (p + n) + 3 := by omega
    have h2eq : k0 + 1 + 2 * (n + 1) = (k0 + 3) + 2 * n := by omega
    have h3eq : d2 + 2 * (n + 1) = (d2 + 2) + 2 * n := by omega
    rw [h1eq, h2eq, h3eq]
    have h1 := ruleC_step_within (p + n) k0 d2 R_tail
    have h2 := ih p (k0 + 3) (d2 + 2) (by omega)
    have hM := pilot_stateC_field_growth (p + n) k0 d2 R_tail
    let M := pilotStateFieldMax (stateC ((p + n) + 3) (k0 + 1) d2 R_tail)
    have h1Budget :
        50 * 46 * (pilotStateFieldMax
          (stateC ((p + n) + 3) (k0 + 1) d2 R_tail) + 47) ≤
          50 * 46 * (M + 2 * n + 49) := by
      simp [M]
      omega
    have h2Factor :
        pilotStateFieldMax (stateC (p + n + 2) (k0 + 3) (d2 + 2) R_tail) +
            2 * n + 47 ≤ M + 2 * n + 49 := by
      simpa [M, Nat.add_assoc] using Nat.add_le_add_right hM (2 * n + 47)
    have h2Budget :
        50 * 46 * n *
          (pilotStateFieldMax (stateC (p + n + 2) (k0 + 3) (d2 + 2) R_tail) +
            2 * n + 47) ≤
          50 * 46 * n * (M + 2 * n + 49) :=
      Nat.mul_le_mul_left (50 * 46 * n) h2Factor
    have hcomp := reachesWithin_trans
      (reachesWithin_mono h1Budget h1)
      (reachesWithin_mono h2Budget h2)
    have htotal :
        50 * 46 * (M + 2 * n + 49) +
          50 * 46 * n * (M + 2 * n + 49) ≤
            50 * 46 * (n + 1) * (M + 2 * n + 49) := by
      have heq :
          50 * 46 * (M + 2 * n + 49) +
            50 * 46 * n * (M + 2 * n + 49) =
              50 * 46 * (n + 1) * (M + 2 * n + 49) := by ring
      omega
    have hfinal := reachesWithin_mono htotal hcomp
    simpa [M, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal

#print axioms ruleA_step_within
#print axioms ruleC_step_within
#print axioms ruleA_iter_within
#print axioms ruleC_iter_within


/-- The missing Rule-A initialization is exactly 46 pure symbolic transitions.
    The equality is definitional in the pinned upstream source. -/
theorem ruleA0_step_within (k d : Nat) (R_tail : List SymTok) :
    ReachesWithin
      (50 * 46 * (pilotStateFieldMax (stateA0 (k + 1) (d + 6) R_tail) + 47))
      ((evalSym target_tm) (stateA0 (k + 1) (d + 6) R_tail))
      ((evalSym target_tm) (stateA 0 k d R_tail)) := by
  exact iterStep_stepPure_within_eq 46
    (stateA0 (k + 1) (d + 6) R_tail)
    (stateA 0 k d R_tail)
    (by rfl)

/-- Compose the 46-step Rule-A initialization with n ordinary 66-step
    Rule-A blocks.  The initial maximum field M controls the whole chain. -/
theorem ruleA0_iter_within (n k d : Nat) (R_tail : List SymTok) :
    ReachesWithin
      (50 * 66 * (n + 1) *
        (pilotStateFieldMax (stateA0 (k + n + 1) (d + 6 * n + 6) R_tail) + n + 113))
      ((evalSym target_tm) (stateA0 (k + n + 1) (d + 6 * n + 6) R_tail))
      ((evalSym target_tm) (stateA n k d R_tail)) := by
  let M := pilotStateFieldMax (stateA0 (k + n + 1) (d + 6 * n + 6) R_tail)
  have h0 : ReachesWithin (50 * 46 * (M + 47))
      ((evalSym target_tm) (stateA0 (k + n + 1) (d + 6 * n + 6) R_tail))
      ((evalSym target_tm) (stateA 0 (k + n) (d + 6 * n) R_tail)) := by
    simpa [M, Nat.add_assoc] using
      (ruleA0_step_within (k + n) (d + 6 * n) R_tail)
  have hfield :
      pilotStateFieldMax (stateA 0 (k + n) (d + 6 * n) R_tail) ≤ M := by
    simp [M, stateA0, stateA, pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax]
    omega
  have hiter := ruleA_iter_within n 0 k d R_tail
  have hiterFactor :
      pilotStateFieldMax (stateA 0 (k + n) (d + 6 * n) R_tail) + n + 67 ≤
        M + n + 113 := by omega
  have hiterBudget := Nat.mul_le_mul_left (50 * 66 * n) hiterFactor
  have hiter' := reachesWithin_mono hiterBudget hiter
  have h0Budget : 50 * 46 * (M + 47) ≤ 50 * 66 * (M + n + 113) := by omega
  have h0' := reachesWithin_mono h0Budget h0
  have hcomp := reachesWithin_trans h0' hiter'
  have htotal :
      50 * 66 * (M + n + 113) + 50 * 66 * n * (M + n + 113) ≤
        50 * 66 * (n + 1) * (M + n + 113) := by
    calc
      _ = 50 * 66 * (n + 1) * (M + n + 113) := by ring
      _ ≤ 50 * 66 * (n + 1) * (M + n + 113) := Nat.le_refl _
  exact reachesWithin_mono htotal hcomp

/-- If the repeated-block count n is no larger than the starting field M,
    the complete Rule-A chain (including its 46-step prelude) costs less
    than 2^19 (M+1)^2 primitive steps. -/
theorem ruleA0_iter_within_2pow19 (n k d : Nat) (R_tail : List SymTok)
    (hn : n ≤ pilotStateFieldMax
      (stateA0 (k + n + 1) (d + 6 * n + 6) R_tail)) :
    ReachesWithin
      (2^19 *
        (pilotStateFieldMax (stateA0 (k + n + 1) (d + 6 * n + 6) R_tail) + 1)^2)
      ((evalSym target_tm) (stateA0 (k + n + 1) (d + 6 * n + 6) R_tail))
      ((evalSym target_tm) (stateA n k d R_tail)) := by
  let M := pilotStateFieldMax (stateA0 (k + n + 1) (d + 6 * n + 6) R_tail)
  have hbase := ruleA0_iter_within n k d R_tail
  have hbase' : ReachesWithin (50 * 66 * (n + 1) * (M + n + 113))
      ((evalSym target_tm) (stateA0 (k + n + 1) (d + 6 * n + 6) R_tail))
      ((evalSym target_tm) (stateA n k d R_tail)) := by
    simpa [M] using hbase
  have hn' : n + 1 ≤ M + 1 := by omega
  have hfield : M + n + 113 ≤ 115 * (M + 1) := by omega
  have hprod := Nat.mul_le_mul hn' hfield
  have hconst : 50 * 66 * 115 ≤ 2^19 := by norm_num
  have hbudget :
      50 * 66 * (n + 1) * (M + n + 113) ≤ 2^19 * (M + 1)^2 := by
    calc
      50 * 66 * (n + 1) * (M + n + 113) =
          50 * 66 * ((n + 1) * (M + n + 113)) := by ring
      _ ≤ 50 * 66 * ((M + 1) * (115 * (M + 1))) :=
        Nat.mul_le_mul_left (50 * 66) hprod
      _ = (50 * 66 * 115) * (M + 1)^2 := by ring
      _ ≤ 2^19 * (M + 1)^2 :=
        Nat.mul_le_mul_right ((M + 1)^2) hconst
  exact reachesWithin_mono (by simpa [M] using hbudget) hbase'

#print axioms ruleA0_step_within
#print axioms ruleA0_iter_within
#print axioms ruleA0_iter_within_2pow19
#print axioms pilot_peelTok_field_growth
#print axioms pilot_peelL_field_growth
#print axioms pilot_peelTok_length_le
#print axioms pilot_peelL_length_le
#print axioms pilotStateFieldMax_peelL_left_mono




theorem pilot_iter_budget_mono (n N M : Nat) (hn : n ≤ N) :
    50 * n * (M + n + 1) ≤ 50 * N * (M + N + 1) := by
  have hfactor : M + n + 1 ≤ M + N + 1 := by omega
  have hmul : n * (M + n + 1) ≤ N * (M + N + 1) :=
    Nat.mul_le_mul hn hfactor
  calc
    50 * n * (M + n + 1) = 50 * (n * (M + n + 1)) := by ring
    _ ≤ 50 * (N * (M + N + 1)) := Nat.mul_le_mul_left 50 hmul
    _ = 50 * N * (M + N + 1) := by ring

theorem pilotListFieldMax_append (xs ys : List SymTok) :
    pilotListFieldMax (xs ++ ys) =
      max (pilotListFieldMax xs) (pilotListFieldMax ys) := by
  induction xs with
  | nil => simp [pilotListFieldMax]
  | cons t xs ih =>
    simp [pilotListFieldMax, ih, Nat.max_assoc]

set_option maxRecDepth 2000000 in
theorem ruleB_step_AA_within (p m k d2 : Nat) (R_tail : List SymTok) :
    ReachesWithin
      (50 * 126 * (pilotStateFieldMax
        (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail) + 127))
      ((evalSym target_tm) (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail))
      ((evalSym target_tm) (stateB sep3A sep3A (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  have hrfl : iterStep stepPure 126
      (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : (evalSym target_tm)
      (iterStep stepPure 126
        (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)) =
      (evalSym target_tm)
        (stateB sep3A sep3A (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3A, evalSym, encSymL, List.cons_append, List.nil_append,
      repBlock12_snoc]
  exact iterStep_stepPure_within_eq 126
    (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)
    (stateB sep3A sep3A (p + 3) (m + 1) k (d2 + 4) R_tail) heq

set_option maxRecDepth 2000000 in
theorem ruleB_step_AB_within (p m k d2 : Nat) (R_tail : List SymTok) :
    ReachesWithin
      (50 * 118 * (pilotStateFieldMax
        (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail) + 119))
      ((evalSym target_tm) (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail))
      ((evalSym target_tm) (stateB sep3A sep3B (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  have hrfl : iterStep stepPure 118
      (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : (evalSym target_tm)
      (iterStep stepPure 118
        (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)) =
      (evalSym target_tm)
        (stateB sep3A sep3B (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3A, sep3B, evalSym, encSymL, List.cons_append, List.nil_append,
      repBlock12_snoc]
  exact iterStep_stepPure_within_eq 118
    (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)
    (stateB sep3A sep3B (p + 3) (m + 1) k (d2 + 4) R_tail) heq

set_option maxRecDepth 2000000 in
theorem ruleB_step_BA_within (p m k d2 : Nat) (R_tail : List SymTok) :
    ReachesWithin
      (50 * 106 * (pilotStateFieldMax
        (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail) + 107))
      ((evalSym target_tm) (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail))
      ((evalSym target_tm) (stateB sep3B sep3A (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  have hrfl : iterStep stepPure 106
      (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : (evalSym target_tm)
      (iterStep stepPure 106
        (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)) =
      (evalSym target_tm)
        (stateB sep3B sep3A (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3A, sep3B, evalSym, encSymL, List.cons_append, List.nil_append,
      repBlock12_snoc]
  exact iterStep_stepPure_within_eq 106
    (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)
    (stateB sep3B sep3A (p + 3) (m + 1) k (d2 + 4) R_tail) heq

set_option maxRecDepth 2000000 in
theorem ruleB_step_BB_within (p m k d2 : Nat) (R_tail : List SymTok) :
    ReachesWithin
      (50 * 98 * (pilotStateFieldMax
        (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail) + 99))
      ((evalSym target_tm) (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail))
      ((evalSym target_tm) (stateB sep3B sep3B (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  have hrfl : iterStep stepPure 98
      (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : (evalSym target_tm)
      (iterStep stepPure 98
        (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)) =
      (evalSym target_tm)
        (stateB sep3B sep3B (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3B, evalSym, encSymL, List.cons_append, List.nil_append,
      repBlock12_snoc]
  exact iterStep_stepPure_within_eq 98
    (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)
    (stateB sep3B sep3B (p + 3) (m + 1) k (d2 + 4) R_tail) heq

theorem ruleB_step_within (s_sep m_sep : List SymTok)
    (hs : s_sep = sep3A ∨ s_sep = sep3B)
    (hm : m_sep = sep3A ∨ m_sep = sep3B)
    (p m k d2 : Nat) (R_tail : List SymTok) :
    ReachesWithin
      (50 * 126 * (pilotStateFieldMax
        (stateB s_sep m_sep (p + 1) (m + 2) (k + 1) d2 R_tail) + 127))
      ((evalSym target_tm)
        (stateB s_sep m_sep (p + 1) (m + 2) (k + 1) d2 R_tail))
      ((evalSym target_tm)
        (stateB s_sep m_sep (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  rcases hs with rfl | rfl <;> rcases hm with rfl | rfl
  · exact reachesWithin_mono (by simp) (ruleB_step_AA_within p m k d2 R_tail)
  · have h := ruleB_step_AB_within p m k d2 R_tail
    exact reachesWithin_mono
      (pilot_iter_budget_mono 118 126
        (pilotStateFieldMax (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail))
        (by omega)) h
  · have h := ruleB_step_BA_within p m k d2 R_tail
    exact reachesWithin_mono
      (pilot_iter_budget_mono 106 126
        (pilotStateFieldMax (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail))
        (by omega)) h
  · have h := ruleB_step_BB_within p m k d2 R_tail
    exact reachesWithin_mono
      (pilot_iter_budget_mono 98 126
        (pilotStateFieldMax (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail))
        (by omega)) h

theorem pilot_stateB_field_growth (s_sep m_sep : List SymTok)
    (p m k d2 : Nat) (R_tail : List SymTok) :
    pilotStateFieldMax
      (stateB s_sep m_sep (p + 3) (m + 1) k (d2 + 4) R_tail) ≤
    pilotStateFieldMax
      (stateB s_sep m_sep (p + 1) (m + 2) (k + 1) d2 R_tail) + 4 := by
  simp [stateB, pilotStateFieldMax, pilotListFieldMax_append,
    pilotListFieldMax, pilotTokFieldMax, Nat.max_assoc, Nat.max_comm, Nat.max_left_comm]
  omega

theorem ruleB_iter_within (s_sep m_sep : List SymTok)
    (hs : s_sep = sep3A ∨ s_sep = sep3B)
    (hm : m_sep = sep3A ∨ m_sep = sep3B)
    (n p m k d2 : Nat) (R_tail : List SymTok) :
    ReachesWithin
      (50 * 126 * n *
        (pilotStateFieldMax
          (stateB s_sep m_sep (p + 1) (m + n + 1) (k + n) d2 R_tail) +
          4 * n + 127))
      ((evalSym target_tm)
        (stateB s_sep m_sep (p + 1) (m + n + 1) (k + n) d2 R_tail))
      ((evalSym target_tm)
        (stateB s_sep m_sep (p + 1 + 2 * n) (m + 1) k (d2 + 4 * n) R_tail)) := by
  induction n generalizing p m k d2 with
  | zero =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [stateB] using pilot_reachesIn_refl
      ((evalSym target_tm) (stateB s_sep m_sep (p + 1) (m + 1) k d2 R_tail))
  | succ n ih =>
    have h1eq : m + (n + 1) + 1 = (m + n) + 2 := by omega
    have h2eq : k + (n + 1) = (k + n) + 1 := by omega
    have h3eq : p + 1 + 2 * (n + 1) = (p + 2) + 1 + 2 * n := by omega
    have h4eq : d2 + 4 * (n + 1) = (d2 + 4) + 4 * n := by omega
    rw [h1eq, h2eq, h3eq, h4eq]
    have h1 := ruleB_step_within s_sep m_sep hs hm p (m + n) (k + n) d2 R_tail
    have h2 := ih (p + 2) m k (d2 + 4)
    have hM := pilot_stateB_field_growth s_sep m_sep p (m + n) (k + n) d2 R_tail
    let M := pilotStateFieldMax
      (stateB s_sep m_sep (p + 1) ((m + n) + 2) ((k + n) + 1) d2 R_tail)
    have h1Budget :
        50 * 126 * (pilotStateFieldMax
          (stateB s_sep m_sep (p + 1) ((m + n) + 2) ((k + n) + 1) d2 R_tail) + 127) ≤
          50 * 126 * (M + 4 * n + 131) := by
      simp [M]
      omega
    have h2Factor :
        pilotStateFieldMax
          (stateB s_sep m_sep (p + 3) (m + n + 1) (k + n) (d2 + 4) R_tail) +
          4 * n + 127 ≤ M + 4 * n + 131 := by
      simpa [M, Nat.add_assoc] using Nat.add_le_add_right hM (4 * n + 127)
    have h2Budget :
        50 * 126 * n *
          (pilotStateFieldMax
            (stateB s_sep m_sep (p + 3) (m + n + 1) (k + n) (d2 + 4) R_tail) +
            4 * n + 127) ≤
          50 * 126 * n * (M + 4 * n + 131) :=
      Nat.mul_le_mul_left (50 * 126 * n) h2Factor
    have hcomp := reachesWithin_trans
      (reachesWithin_mono h1Budget h1)
      (reachesWithin_mono h2Budget h2)
    have htotal :
        50 * 126 * (M + 4 * n + 131) +
          50 * 126 * n * (M + 4 * n + 131) ≤
            50 * 126 * (n + 1) * (M + 4 * n + 131) := by
      have heq :
          50 * 126 * (M + 4 * n + 131) +
            50 * 126 * n * (M + 4 * n + 131) =
              50 * 126 * (n + 1) * (M + 4 * n + 131) := by ring
      omega
    have hfinal := reachesWithin_mono htotal hcomp
    simpa [M, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal

#print axioms ruleB_step_within
#print axioms ruleB_iter_within


end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution
