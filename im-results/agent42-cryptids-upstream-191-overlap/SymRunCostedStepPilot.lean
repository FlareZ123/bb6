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



@[simp] theorem pilotListFieldMax_nil : pilotListFieldMax [] = 0 := rfl

@[simp] theorem pilotListFieldMax_cons (t : SymTok) (xs : List SymTok) :
    pilotListFieldMax (t :: xs) = max (pilotTokFieldMax t) (pilotListFieldMax xs) := rfl

theorem pilotListFieldMax_append (xs ys : List SymTok) :
    pilotListFieldMax (xs ++ ys) =
      max (pilotListFieldMax xs) (pilotListFieldMax ys) := by
  induction xs with
  | nil => simp [pilotListFieldMax]
  | cons t xs ih =>
    simp [pilotListFieldMax, ih, Nat.max_assoc]

theorem pilotListFieldMax_suffix (pre xs : List SymTok) :
    pilotListFieldMax xs ≤ pilotListFieldMax (pre ++ xs) := by
  rw [pilotListFieldMax_append]
  exact Nat.le_max_right _ _

theorem pilot_bumpSymL_field_growth (xs : List SymTok) :
    pilotListFieldMax (bumpSymL xs) ≤ pilotListFieldMax xs + 1 := by
  induction xs with
  | nil => simp [bumpSymL, pilotListFieldMax, pilotTokFieldMax]
  | cons t xs ih =>
    cases t with
    | item x =>
      cases x with
      | zero => simp [bumpSymL, pilotListFieldMax_cons, pilotTokFieldMax]
      | run d => simp [bumpSymL, pilotListFieldMax_cons, pilotTokFieldMax]; omega
    | repB1 k =>
      cases k with
      | zero => simpa [bumpSymL, pilotListFieldMax_cons, pilotTokFieldMax] using ih
      | succ k =>
        cases k with
        | zero => simp [bumpSymL, pilotListFieldMax_cons, pilotTokFieldMax]; omega
        | succ k => simp [bumpSymL, pilotListFieldMax_cons, pilotTokFieldMax]; omega
    | rep2 p =>
      cases p with
      | zero => simpa [bumpSymL, pilotListFieldMax_cons, pilotTokFieldMax] using ih
      | succ p => simp [bumpSymL, pilotListFieldMax_cons, pilotTokFieldMax]; omega
    | rep12 m =>
      cases m with
      | zero => simpa [bumpSymL, pilotListFieldMax_cons, pilotTokFieldMax] using ih
      | succ m => simp [bumpSymL, pilotListFieldMax_cons, pilotTokFieldMax]; omega

theorem pilot_bumpSymR_field_growth (xs : List SymTok) :
    pilotListFieldMax (bumpSymR xs) ≤ pilotListFieldMax xs + 1 := by
  induction xs with
  | nil => simp [bumpSymR, pilotListFieldMax, pilotTokFieldMax]
  | cons t xs ih =>
    cases t with
    | item x =>
      cases x with
      | zero => simp [bumpSymR, pilotListFieldMax_cons, pilotTokFieldMax]
      | run d => simp [bumpSymR, pilotListFieldMax_cons, pilotTokFieldMax]; omega
    | repB1 k =>
      cases k with
      | zero => simpa [bumpSymR, pilotListFieldMax_cons, pilotTokFieldMax] using ih
      | succ k =>
        cases k with
        | zero => simp [bumpSymR, pilotListFieldMax_cons, pilotTokFieldMax]; omega
        | succ k => simp [bumpSymR, pilotListFieldMax_cons, pilotTokFieldMax]; omega
    | rep2 p =>
      cases p with
      | zero => simpa [bumpSymR, pilotListFieldMax_cons, pilotTokFieldMax] using ih
      | succ p => simp [bumpSymR, pilotListFieldMax_cons, pilotTokFieldMax]; omega
    | rep12 m =>
      cases m with
      | zero => simpa [bumpSymR, pilotListFieldMax_cons, pilotTokFieldMax] using ih
      | succ m => simp [bumpSymR, pilotListFieldMax_cons, pilotTokFieldMax]; omega

theorem pilot_prependZeroSym_field_max (n : Nat) (xs : List SymTok) :
    pilotListFieldMax (prependZeroSym n xs) = pilotListFieldMax xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [prependZeroSym, ih]
    simp [pilotListFieldMax_cons, pilotTokFieldMax]

theorem pilot_max_le_max_plus_one {a b a' b' : Nat}
    (ha : a' ≤ a+1) (hb : b' ≤ b+1) : max a' b' ≤ max a b + 1 := by omega

theorem pilot_max_left_bump_le (l r r' : Nat) (hr : r' ≤ r+1) :
    max l r' ≤ max l r + 1 := by
  apply Nat.max_le.mpr
  constructor
  · exact Nat.le_trans (Nat.le_max_left l r) (Nat.le_add_right (max l r) 1)
  · exact Nat.le_trans hr (Nat.add_le_add_right (Nat.le_max_right l r) 1)

theorem pilot_stepElemBB_field_growth (L R : List SymTok) :
    pilotStateFieldMax (stepElemBB L R) ≤ pilotStateFieldMax (.BB, L, R) + 1 := by
  have hR := pilot_bumpSymR_field_growth R
  cases L with
  | nil => simpa [stepElemBB, pilotStateFieldMax, strictList_eq] using hR
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero => simp [stepElemBB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax, strictList_eq] <;> omega
      | run d =>
        cases d with
        | zero => simp [stepElemBB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
        | succ d =>
          cases d with
          | zero =>
            have hm := pilot_max_left_bump_le (pilotListFieldMax L1) (pilotListFieldMax R) (pilotListFieldMax (bumpSymR R)) hR
            simp [stepElemBB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
            exact Nat.le_trans hm (Nat.add_le_add_right (Nat.le_max_right 1 (max (pilotListFieldMax L1) (pilotListFieldMax R))) 1)
          | succ d =>
            cases d with
            | zero =>
              have hm := pilot_max_left_bump_le (pilotListFieldMax L1) (pilotListFieldMax R) (pilotListFieldMax (bumpSymR R)) hR
              simp [stepElemBB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
              exact Nat.le_trans hm (Nat.add_le_add_right (Nat.le_max_right 2 (max (pilotListFieldMax L1) (pilotListFieldMax R))) 1)
            | succ d =>
              cases d with
              | zero => simp [stepElemBB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax] <;> omega
              | succ d => simp [stepElemBB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax] <;> omega
    | repB1 k => simp [stepElemBB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
    | rep2 p => simp [stepElemBB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
    | rep12 m => simp [stepElemBB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]

theorem pilot_stepElemDL_field_growth (L R : List SymTok) :
    pilotStateFieldMax (stepElemDL L R) ≤ pilotStateFieldMax (.DL, L, R) + 1 := by
  have hR := pilot_bumpSymR_field_growth R
  cases L with
  | nil => simp [stepElemDL, pilotStateFieldMax]
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero => simp [stepElemDL, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
      | run d =>
        cases d with
        | zero =>
          have hm := pilot_max_left_bump_le (pilotListFieldMax L1) (pilotListFieldMax R) (pilotListFieldMax (bumpSymR R)) hR
          simp [stepElemDL, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
          exact hm
        | succ d =>
          cases d with
          | zero =>
            have hm := pilot_max_left_bump_le (pilotListFieldMax L1) (pilotListFieldMax R) (pilotListFieldMax (bumpSymR R)) hR
            simp [stepElemDL, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
            exact Nat.le_trans hm (Nat.add_le_add_right (Nat.le_max_right 1 (max (pilotListFieldMax L1) (pilotListFieldMax R))) 1)
          | succ d =>
            cases d with
            | zero =>
              cases R with
              | nil => simp [stepElemDL, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
              | cons r R1 =>
                cases r with
                | item y =>
                  cases y with
                  | zero => simp [stepElemDL, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
                  | run d0 =>
                    simp [stepElemDL, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax, pilot_prependZeroSym_field_max]
                    omega
                | repB1 k => simp [stepElemDL, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
                | rep2 p => simp [stepElemDL, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
                | rep12 m => simp [stepElemDL, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
            | succ d => simp [stepElemDL, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
    | repB1 k => simp [stepElemDL, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
    | rep2 p => simp [stepElemDL, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
    | rep12 m => simp [stepElemDL, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]

theorem pilot_stepElemCB_run0_field_growth (L R : List SymTok) :
    pilotStateFieldMax (stepElemCB_run0 L R) ≤ pilotStateFieldMax (.CB, L, .item (.run 0) :: R) + 1 := by
  have hL := pilot_bumpSymL_field_growth L
  cases R with
  | nil =>
    simp [stepElemCB_run0, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
    omega
  | cons t R2 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        simp [stepElemCB_run0, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
        omega
      | run d =>
        cases d with
        | zero =>
          simp [stepElemCB_run0, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
          omega
        | succ d =>
          simp [stepElemCB_run0, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax, pilot_prependZeroSym_field_max]
          omega
    | repB1 k => simp [stepElemCB_run0, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
    | rep2 p => simp [stepElemCB_run0, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
    | rep12 m => simp [stepElemCB_run0, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]

theorem pilot_stepElemCB_field_growth (L R : List SymTok) :
    pilotStateFieldMax (stepElemCB L R) ≤ pilotStateFieldMax (.CB, L, R) + 1 := by
  have hL := pilot_bumpSymL_field_growth L
  cases R with
  | nil =>
    simpa [stepElemCB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax] using
      (pilot_max_le_max_plus_one (a := pilotListFieldMax L) (b := 0) (a' := pilotListFieldMax (bumpSymL L)) (b' := 0) hL (by omega))
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        have hR1 := pilot_bumpSymR_field_growth R1
        simpa [stepElemCB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax] using
          (pilot_max_le_max_plus_one hL hR1)
      | run d =>
        cases d with
        | zero => simpa [stepElemCB] using pilot_stepElemCB_run0_field_growth L R1
        | succ d =>
          cases d with
          | zero =>
            have hRbound : pilotListFieldMax R1 ≤ pilotListFieldMax (.item (.run 1) :: R1) + 1 := by
              simp [pilotListFieldMax_cons, pilotTokFieldMax]
              omega
            simpa [stepElemCB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax] using
              (pilot_max_le_max_plus_one hL hRbound)
          | succ d =>
            cases d with
            | zero =>
              have hRbound : pilotListFieldMax (.item (.run 0) :: .item .zero :: R1) ≤
                  pilotListFieldMax (.item (.run 2) :: R1) + 1 := by
                simp [pilotListFieldMax_cons, pilotTokFieldMax]
                omega
              simpa [stepElemCB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax] using
                (pilot_max_le_max_plus_one hL hRbound)
            | succ d =>
              have hRbound : pilotListFieldMax (.item (.run 0) :: .item (.run d) :: R1) ≤
                  pilotListFieldMax (.item (.run (d+3)) :: R1) + 1 := by
                simp [pilotListFieldMax_cons, pilotTokFieldMax]
                omega
              simpa [stepElemCB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax] using
                (pilot_max_le_max_plus_one hL hRbound)
    | repB1 k => simp [stepElemCB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
    | rep2 p => simp [stepElemCB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
    | rep12 m => simp [stepElemCB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]

theorem pilot_stepElemSym_field_growth (mode : SymMode) (L R : List SymTok) :
    pilotStateFieldMax (stepElemSym mode L R) ≤ pilotStateFieldMax (mode, L, R) + 1 := by
  cases mode with
  | BB => exact pilot_stepElemBB_field_growth L R
  | DL => exact pilot_stepElemDL_field_growth L R
  | CB => exact pilot_stepElemCB_field_growth L R
  | HALT => simp [stepElemSym, pilotStateFieldMax]


theorem pilot_stripPrefixSym_suffix (pre xs rest : List SymTok)
    (h : stripPrefixSym pre xs = some rest) :
    pilotListFieldMax rest ≤ pilotListFieldMax xs := by
  have hx := stripPrefixSym_some pre xs rest h
  rw [hx, pilotListFieldMax_append]
  exact Nat.le_max_right _ _


theorem pilot_stepPureBB_field_growth (L R : List SymTok) :
    pilotStateFieldMax (stepPureBB L R) ≤ pilotStateFieldMax (.BB, L, R) + 1 := by
  cases L with
  | nil => exact pilot_stepElemBB_field_growth [] R
  | cons t L1 =>
    cases t with
    | item x => exact pilot_stepElemBB_field_growth (.item x :: L1) R
    | repB1 k =>
      simp [stepPureBB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax] <;> omega
    | rep2 p =>
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := pilot_stripPrefixSym_suffix _ R R2 hs
        simp [stepPureBB, hs, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
        omega
      | none =>
        have hp := pilot_peelPureTok_field_growth (.rep2 p) L1
        have hp' : pilotListFieldMax (peelPureTok (.rep2 p) L1) ≤ pilotListFieldMax (.rep2 p :: L1) := by
          simpa [pilotListFieldMax_cons] using hp
        have hE := pilot_stepElemBB_field_growth (peelPureTok (.rep2 p) L1) R
        have hm := pilotStateFieldMax_left_mono .BB (peelPureTok (.rep2 p) L1) (.rep2 p :: L1) R hp'
        calc
          pilotStateFieldMax (stepPureBB (.rep2 p :: L1) R) ≤ pilotStateFieldMax (.BB, peelPureTok (.rep2 p) L1, R) + 1 := by
            simpa [stepPureBB, hs] using hE
          _ ≤ pilotStateFieldMax (.BB, .rep2 p :: L1, R) + 1 := Nat.add_le_add_right hm 1
    | rep12 m =>
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := pilot_stripPrefixSym_suffix _ R R2 hs
        simp [stepPureBB, hs, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
        omega
      | none =>
        have hp := pilot_peelPureTok_field_growth (.rep12 m) L1
        have hp' : pilotListFieldMax (peelPureTok (.rep12 m) L1) ≤ pilotListFieldMax (.rep12 m :: L1) := by
          simpa [pilotListFieldMax_cons] using hp
        have hE := pilot_stepElemBB_field_growth (peelPureTok (.rep12 m) L1) R
        have hm := pilotStateFieldMax_left_mono .BB (peelPureTok (.rep12 m) L1) (.rep12 m :: L1) R hp'
        calc
          pilotStateFieldMax (stepPureBB (.rep12 m :: L1) R) ≤ pilotStateFieldMax (.BB, peelPureTok (.rep12 m) L1, R) + 1 := by
            simpa [stepPureBB, hs] using hE
          _ ≤ pilotStateFieldMax (.BB, .rep12 m :: L1, R) + 1 := Nat.add_le_add_right hm 1

theorem pilot_stepPureDL_field_growth (L R : List SymTok) :
    pilotStateFieldMax (stepPureDL L R) ≤ pilotStateFieldMax (.DL, L, R) + 1 := by
  cases L with
  | nil => simp [stepPureDL, pilotStateFieldMax]
  | cons t L1 =>
    have hp := pilot_peelPureTok_field_growth t L1
    have hp' : pilotListFieldMax (peelPureTok t L1) ≤ pilotListFieldMax (t :: L1) := by
      simpa [pilotListFieldMax_cons] using hp
    have hE := pilot_stepElemDL_field_growth (peelPureTok t L1) R
    have hm := pilotStateFieldMax_left_mono .DL (peelPureTok t L1) (t :: L1) R hp'
    calc
      pilotStateFieldMax (stepPureDL (t :: L1) R) ≤ pilotStateFieldMax (.DL, peelPureTok t L1, R) + 1 := by
        simpa [stepPureDL] using hE
      _ ≤ pilotStateFieldMax (.DL, t :: L1, R) + 1 := Nat.add_le_add_right hm 1

theorem pilot_stepPureCB_field_growth (L R : List SymTok) :
    pilotStateFieldMax (stepPureCB L R) ≤ pilotStateFieldMax (.CB, L, R) + 1 := by
  have hL := pilot_bumpSymL_field_growth L
  cases R with
  | nil => exact pilot_stepElemCB_field_growth L []
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero => exact pilot_stepElemCB_field_growth L (.item .zero :: R1)
      | run n =>
        cases n with
        | zero => exact pilot_stepElemCB_run0_field_growth L R1
        | succ n =>
          cases n with
          | zero => exact pilot_stepElemCB_field_growth L (.item (.run 1) :: R1)
          | succ n =>
            cases n with
            | zero => exact pilot_stepElemCB_field_growth L (.item (.run 2) :: R1)
            | succ n =>
              have hR : pilotListFieldMax (.item (.run 0) :: .item (.run n) :: R1) ≤
                  pilotListFieldMax (.item (.run (n+3)) :: R1) + 1 := by
                simp [pilotListFieldMax_cons, pilotTokFieldMax]
                omega
              simpa [stepPureCB, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax] using
                (pilot_max_le_max_plus_one hL hR)
    | repB1 k =>
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1)] L with
      | some L2 =>
        have hL2 := pilot_stripPrefixSym_suffix _ L L2 hs
        have hR1 : pilotListFieldMax R1 ≤ pilotListFieldMax (.repB1 k :: R1) := by
          simpa using (pilotListFieldMax_suffix [.repB1 k] R1)
        simp [stepPureCB, hs, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
        omega
      | none =>
        cases hs2 : stripPrefixSym [.item (.run 0)] L with
        | some L1 =>
          have hL1 := pilot_stripPrefixSym_suffix _ L L1 hs2
          have hR1 : pilotListFieldMax R1 ≤ pilotListFieldMax (.repB1 k :: R1) := by
            simpa using (pilotListFieldMax_suffix [.repB1 k] R1)
          simp [stepPureCB, hs, hs2, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
          omega
        | none => simp [stepPureCB, hs, hs2, pilotStateFieldMax]
    | rep2 p =>
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] L with
      | some L2 =>
        have hL2 := pilot_stripPrefixSym_suffix _ L L2 hs
        have hR1 : pilotListFieldMax R1 ≤ pilotListFieldMax (.rep2 p :: R1) := by
          simpa using (pilotListFieldMax_suffix [.rep2 p] R1)
        simp [stepPureCB, hs, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
        omega
      | none =>
        cases hs2 : stripPrefixSym [.item (.run 0)] L with
        | some L1 =>
          have hL1 := pilot_stripPrefixSym_suffix _ L L1 hs2
          have hR1 : pilotListFieldMax R1 ≤ pilotListFieldMax (.rep2 p :: R1) := by
            simpa using (pilotListFieldMax_suffix [.rep2 p] R1)
          simp [stepPureCB, hs, hs2, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
          omega
        | none => simp [stepPureCB, hs, hs2, pilotStateFieldMax]
    | rep12 m =>
      cases hs : stripPrefixSym [.item (.run 0)] L with
      | some L1 =>
        have hL1 := pilot_stripPrefixSym_suffix _ L L1 hs
        have hR1 : pilotListFieldMax R1 ≤ pilotListFieldMax (.rep12 m :: R1) := by
          simpa using (pilotListFieldMax_suffix [.rep12 m] R1)
        simp [stepPureCB, hs, pilotStateFieldMax, pilotListFieldMax_cons, pilotTokFieldMax]
        omega
      | none => simp [stepPureCB, hs, pilotStateFieldMax]

theorem pilot_stepPure_field_growth (s : SymMode × List SymTok × List SymTok) :
    pilotStateFieldMax (stepPure s) ≤ pilotStateFieldMax s + 1 := by
  cases s with
  | mk mode rest =>
    cases rest with
    | mk L R =>
      cases mode with
      | BB => exact pilot_stepPureBB_field_growth L R
      | DL => exact pilot_stepPureDL_field_growth L R
      | CB => exact pilot_stepPureCB_field_growth L R
      | HALT => simp [stepPure, pilotStateFieldMax]

theorem iterStep_stepPure_within (n : Nat)
    (s : SymMode × List SymTok × List SymTok) :
    ReachesWithin
      (50 * n * (pilotStateFieldMax s + n + 1))
      ((evalSym target_tm) s)
      ((evalSym target_tm) (iterStep stepPure n s)) := by
  induction n generalizing s with
  | zero =>
    unfold ReachesWithin
    refine ⟨0, by omega, ?_⟩
    simpa [iterStep] using pilot_reachesIn_refl ((evalSym target_tm) s)
  | succ n ih =>
    have h1 := stepPure_within s
    have h2 := ih (stepPure s)
    have hM := pilot_stepPure_field_growth s
    have h1Budget :
        50 * (pilotStateFieldMax s + 1) ≤
          50 * (pilotStateFieldMax s + n + 2) := by
      apply Nat.mul_le_mul_left 50
      omega
    have h2Factor :
        pilotStateFieldMax (stepPure s) + n + 1 ≤
          pilotStateFieldMax s + n + 2 := by
      omega
    have h2Budget :
        50 * n * (pilotStateFieldMax (stepPure s) + n + 1) ≤
          50 * n * (pilotStateFieldMax s + n + 2) :=
      Nat.mul_le_mul_left (50 * n) h2Factor
    have hcomp := reachesWithin_trans
      (reachesWithin_mono h1Budget h1)
      (reachesWithin_mono h2Budget h2)
    have htotal :
        50 * (pilotStateFieldMax s + n + 2) +
          50 * n * (pilotStateFieldMax s + n + 2) ≤
            50 * (n + 1) * (pilotStateFieldMax s + n + 2) := by
      have heq :
          50 * (pilotStateFieldMax s + n + 2) +
            50 * n * (pilotStateFieldMax s + n + 2) =
              50 * (n + 1) * (pilotStateFieldMax s + n + 2) := by ring
      omega
    have hfinal := reachesWithin_mono htotal hcomp
    simpa [iterStep] using hfinal

#print axioms pilot_stepPure_field_growth
#print axioms iterStep_stepPure_within


end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution
