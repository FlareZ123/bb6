/-
Scratch pilot: turn the upstream execute tactic into an exact ReachesIn proof.
Pinned source: google-deepmind/cryptids @ 3647718b5df22e1a61462dec0376bd204526285a.
-/
import BusyBeaver.BB6.Halt.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH

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
    have h1 := step_CB_run0_run_pos_exact 0 (.run 0 :: L)
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




/-! Additional fixed-cost F424 rule witnesses needed by the
    constructor-complete stepPure cost theorem. -/

/-- BB on a leading zero: one primitive step. -/
theorem step_BB_zero_exact (L1 R : List MItem) :
    ReachesIn target_tm 1
      (cfgBB target_tm (.zero :: L1) R)
      (cfgCB target_tm L1 (bumpM R)) := by
  unfold cfgBB cfgCB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  executeWithin 1

/-- BB on a leading run-2: five primitive steps. -/
theorem step_BB_run2_exact (L1 R : List MItem) :
    ReachesIn target_tm 5
      (cfgBB target_tm (.run 2 :: L1) R)
      (cfgDL target_tm L1 (.run 0 :: .run 0 :: bumpM R)) := by
  unfold cfgBB cfgDL
  dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  executeWithin 5

/-- BB on a leading run-3: nine primitive steps. -/
theorem step_BB_run3_exact (L1 R : List MItem) :
    ReachesIn target_tm 9
      (cfgBB target_tm (.run 3 :: L1) R)
      (cfgBB target_tm (.run 0 :: .zero :: .zero :: L1) (bumpM R)) := by
  unfold cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run, encM_cons_zero]
  rw [← encM_bumpM]
  executeWithin 9

/-- BB on a leading run-(d+4): nine primitive steps, independent of d. -/
theorem step_BB_run_ge4_exact (d : Nat) (L1 R : List MItem) :
    ReachesIn target_tm 9
      (cfgBB target_tm (.run (d + 4) :: L1) R)
      (cfgBB target_tm (.run 0 :: .zero :: .run d :: L1) (bumpM R)) := by
  unfold cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run, encM_cons_zero]
  rw [← encM_bumpM]
  executeWithin 9

/-- DL on a leading run-0: one primitive step. -/
theorem step_DL_run0_exact (L1 R : List MItem) :
    ReachesIn target_tm 1
      (cfgDL target_tm (.run 0 :: L1) R)
      (cfgBB target_tm L1 (bumpM R)) := by
  unfold cfgDL cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  executeWithin 1

/-- DL on a leading run-1: three primitive steps. -/
theorem step_DL_run1_exact (L1 R : List MItem) :
    ReachesIn target_tm 3
      (cfgDL target_tm (.run 1 :: L1) R)
      (cfgDL target_tm L1 (.run 0 :: bumpM R)) := by
  unfold cfgDL
  dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  executeWithin 3

/-- CB on an empty right stack: two primitive steps. -/
theorem step_CB_nil_exact (L : List MItem) :
    ReachesIn target_tm 2
      (cfgCB target_tm L [])
      (cfgDL target_tm (bumpM L) [.run 0]) := by
  unfold cfgCB cfgDL
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  executeWithin 2

/-- CB on a leading zero: two primitive steps. -/
theorem step_CB_zero_exact (L R1 : List MItem) :
    ReachesIn target_tm 2
      (cfgCB target_tm L (.zero :: R1))
      (cfgDL target_tm (bumpM L) (bumpM R1)) := by
  unfold cfgCB cfgDL
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM L, ← encM_bumpM R1]
  executeWithin 2

/-- CB on two leading run-zeros: six primitive steps. -/
theorem step_CB_run0_run0_exact (L R2 : List MItem) :
    ReachesIn target_tm 6
      (cfgCB target_tm L (.run 0 :: .run 0 :: R2))
      (cfgBB target_tm (.run 0 :: .zero :: bumpM L) R2) := by
  unfold cfgCB cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run, encM_cons_zero]
  rw [← encM_bumpM]
  executeWithin 6

/-- CB on a leading run-2: five primitive steps. -/
theorem step_CB_run2_exact (L R1 : List MItem) :
    ReachesIn target_tm 5
      (cfgCB target_tm L (.run 2 :: R1))
      (cfgBB target_tm (bumpM L) (.run 0 :: .zero :: R1)) := by
  unfold cfgCB cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  executeWithin 5

/-- CB on a leading run-(d+3): five primitive steps, independent of d. -/
theorem step_CB_run_ge3_exact (d : Nat) (L R1 : List MItem) :
    ReachesIn target_tm 5
      (cfgCB target_tm L (.run (d + 3) :: R1))
      (cfgBB target_tm (bumpM L) (.run 0 :: .run d :: R1)) := by
  unfold cfgCB cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  executeWithin 5

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
                    simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax]
                    omega
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
              simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax]
              omega
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
        · simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax]
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
        · simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax]
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
        · simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax]
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
          · simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax]
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
        · simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax]
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
          · simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax]
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
        · simp [pilotStateFieldMax, pilotListFieldMax, pilotTokFieldMax]
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


end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution
