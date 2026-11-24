/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in upstream LICENSE.
Derived from google-deepmind/cryptids at 3647718b5df22e1a61462dec0376bd204526285a:
BusyBeaver/Calculi/HaltShared.lean and the two exact F289 Halt modules.
The source primitive proof rewrites are retained; existential reachability
is replaced by exact indexed reachability. This file requires exact-source
Lean compilation before it may be used as a certificate.
-/
import BusyBeaver.Calculi.HaltShared
import BusyBeaver.BB6.Halt.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH
import BusyBeaver.BB6.Halt.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH

open Mathlib Relation Nat Turing BusyBeaver BusyBeaver.RleStackEngine
namespace BB6.Agent17.RleCounted

local notation:50 a " [" m "]⊢ᶜ[" n "] " b => ReachesIn m n a b

class CountedRules (target_tm : Machine (Fin 2) (Fin 6)) : Prop where
  rule_B_nil (L : List ℕ) :
    (cfg_B target_tm L []) [target_tm]⊢ᶜ[1] (cfg_C target_tm (bumpHead L) [])
  rule_B_zero (L R : List ℕ) :
    (cfg_B target_tm L (0 :: R)) [target_tm]⊢ᶜ[4] (cfg_B target_tm (0 :: L) R)
  rule_B_succ (d : ℕ) (L R : List ℕ) :
    (cfg_B target_tm L ((d + 1) :: R)) [target_tm]⊢ᶜ[2] (cfg_BR target_tm L (0 :: d :: R))
  rule_BR_nil (L : List ℕ) :
    (cfg_BR target_tm L []) [target_tm]⊢ᶜ[1] (cfg_C target_tm (bumpHead L) [])
  rule_BR_zero (L R : List ℕ) :
    (cfg_BR target_tm L (0 :: R)) [target_tm]⊢ᶜ[2] (cfg_BR target_tm (0 :: L) R)
  rule_BR_one (L R : List ℕ) :
    (cfg_BR target_tm L (1 :: R)) [target_tm]⊢ᶜ[4] (cfg_DR0 target_tm L (bumpHead R))
  rule_BR_add_two (d : ℕ) (L R : List ℕ) :
    (cfg_BR target_tm L ((d + 2) :: R)) [target_tm]⊢ᶜ[5] (cfg_B target_tm (bumpHead L) (d :: R))
  rule_DR0_nil (R : List ℕ) :
    (cfg_DR0 target_tm [] R) [target_tm]⊢ᶜ[3] (cfg_C target_tm [1] R)
  rule_DR0_zero (L R : List ℕ) :
    (cfg_DR0 target_tm (0 :: L) R) [target_tm]⊢ᶜ[4] (cfg_DR0 target_tm L (0 :: R))
  rule_DR0_succ (a : ℕ) (L R : List ℕ) :
    (cfg_DR0 target_tm ((a + 1) :: L) R) [target_tm]⊢ᶜ[3] (cfg_C target_tm (a :: L) (0 :: R))
  rule_C_nil (R : List ℕ) :
    (cfg_C target_tm [] R) [target_tm]⊢ᶜ[1] (cfg_DR0 target_tm [] R)
  rule_C_zero_nil (R : List ℕ) :
    (cfg_C target_tm [0] R) [target_tm]⊢ᶜ[3] (cfg_C target_tm [] (1 :: R))
  rule_C_zero_zero (L R : List ℕ) :
    (cfg_C target_tm (0 :: 0 :: L) R) [target_tm]⊢ᶜ[5] (cfg_C target_tm (bumpHead L) (1 :: R))
  rule_C_zero_one (L R : List ℕ) :
    (cfg_C target_tm (0 :: 1 :: L) R) [target_tm]⊢ᶜ[17]
      (cfg_C target_tm (bumpHead (bumpHead L)) (0 :: bumpHead R))
  rule_C_zero_add_two (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (0 :: (a + 2) :: L) R) [target_tm]⊢ᶜ[4]
      (cfg_BR target_tm (a :: L) (0 :: 1 :: R))
  rule_C_one_nil (R : List ℕ) :
    (cfg_C target_tm [1] R) [target_tm]⊢ᶜ[5] (cfg_B target_tm [0] (1 :: R))
  rule_C_one_zero (L R : List ℕ) :
    (cfg_C target_tm (1 :: 0 :: L) R) [target_tm]⊢ᶜ[7] (cfg_DR0 target_tm L (2 :: R))
  rule_C_one_succ (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (1 :: (a + 1) :: L) R) [target_tm]⊢ᶜ[6] (cfg_C target_tm (a :: L) (2 :: R))
  rule_C_add_two_halt (a : ℕ) (L R : List ℕ) :
    ∃ cfg', ((cfg_C target_tm ((a + 2) :: L) R) [target_tm]⊢ᶜ[3] cfg') ∧
      (step target_tm cfg').isNone



macro "countStep" : tactic => `(tactic| (
  try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, BusyBeaver.RleStackEngine.listblank_append_cons,
    BusyBeaver.RleStackEngine.listblank_append_nil, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, BusyBeaver.RleStackEngine.default_head]
  apply ReachesIn.step_left (by rfl)
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,
    BusyBeaver.RleStackEngine.listblank_append_cons, BusyBeaver.RleStackEngine.listblank_append_nil, Turing.ListBlank.head_cons,
    Turing.ListBlank.tail_cons, Tape.write, BusyBeaver.RleStackEngine.zero_cons_default, BusyBeaver.RleStackEngine.default_head, BusyBeaver.RleStackEngine.default_tail]))

macro "countFinish" : tactic => `(tactic| (
  change multiStep _ _ 0 = some _
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, BusyBeaver.RleStackEngine.listblank_append_cons,
    BusyBeaver.RleStackEngine.listblank_append_nil, BusyBeaver.RleStackEngine.zero_cons_default, encLeft_nil, encRight_nil, encLeft_cons_one,
    encRight_cons_one, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, BusyBeaver.RleStackEngine.multiStep_zero]
  try rfl))

macro "countExecute" n:num : tactic => `(tactic| (
  iterate $n countStep
  countFinish))

namespace First

abbrev target_tm : Machine (Fin 2) (Fin 6) := BusyBeaver.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH.target
@[simp] theorem isFlipped_tm : isFlipped target_tm = false := rfl

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def F : Fin 6 := 5

@[simp] theorem init_nil : (init ([] : List (Fin 2))) = ⟨some A, ⟨0, default, default⟩⟩ := rfl

def cfg_Halt (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some F, ⟨1, l, r⟩⟩

theorem init_reaches_stack : (init []) [target_tm]⊢ᶜ[1] (cfg_B target_tm [0] []) := by
  rw [init_nil]; unfold cfg_B; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_zero, encLeft_nil, encRight_nil]; countExecute 1

theorem rule_B_nil (L : List ℕ) :
    (cfg_B target_tm L []) [target_tm]⊢ᶜ[1] (cfg_C target_tm (bumpHead L) []) := by
  unfold cfg_B cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_nil]; countExecute 1

theorem rule_B_zero (L R : List ℕ) :
    (cfg_B target_tm L (0 :: R)) [target_tm]⊢ᶜ[4] (cfg_B target_tm (0 :: L) R) := by
  unfold cfg_B; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_zero R, encLeft_zero L];
      countExecute 4

theorem rule_B_succ (d : ℕ) (L R : List ℕ) :
    (cfg_B target_tm L ((d + 1) :: R)) [target_tm]⊢ᶜ[2] (cfg_BR target_tm L (0 :: d :: R)) := by
  unfold cfg_B cfg_BR; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_succ d R, encRight_zero (d :: R), encRight_expose d R]; countExecute 2

theorem rule_BR_nil (L : List ℕ) :
    (cfg_BR target_tm L []) [target_tm]⊢ᶜ[1] (cfg_C target_tm (bumpHead L) []) :=
  rule_B_nil L

theorem rule_BR_zero (L R : List ℕ) :
    (cfg_BR target_tm L (0 :: R)) [target_tm]⊢ᶜ[2] (cfg_BR target_tm (0 :: L) R) := by
  unfold cfg_BR; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_zero R, encLeft_zero L];
      countExecute 2

theorem rule_BR_one (L R : List ℕ) :
    (cfg_BR target_tm L (1 :: R)) [target_tm]⊢ᶜ[4] (cfg_DR0 target_tm L (bumpHead R)) := by
  unfold cfg_BR cfg_DR0; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_succ 0 R,
      encRight_zero R]; countExecute 4

theorem rule_BR_add_two (d : ℕ) (L R : List ℕ) :
    (cfg_BR target_tm L ((d + 2) :: R)) [target_tm]⊢ᶜ[5] (cfg_B target_tm (bumpHead L) (d :: R)) :=
        by
  unfold cfg_BR cfg_B; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_succ (d + 1) R, encRight_succ d R, encRight_expose d R]; countExecute 5

theorem rule_DR0_nil (R : List ℕ) :
    (cfg_DR0 target_tm [] R) [target_tm]⊢ᶜ[3] (cfg_C target_tm [1] R) := by
  unfold cfg_DR0 cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_nil, encLeft_succ 0 [], encLeft_zero [], encLeft_nil]; countExecute 3

theorem rule_DR0_zero (L R : List ℕ) :
    (cfg_DR0 target_tm (0 :: L) R) [target_tm]⊢ᶜ[4] (cfg_DR0 target_tm L (0 :: R)) := by
  unfold cfg_DR0; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_zero L, encRight_zero R];
      countExecute 4

theorem rule_DR0_succ (a : ℕ) (L R : List ℕ) :
    (cfg_DR0 target_tm ((a + 1) :: L) R) [target_tm]⊢ᶜ[3] (cfg_C target_tm (a :: L) (0 :: R)) := by
  unfold cfg_DR0 cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_succ a L,
      encRight_zero R]; countExecute 3

theorem rule_C_nil (R : List ℕ) :
    (cfg_C target_tm [] R) [target_tm]⊢ᶜ[1] (cfg_DR0 target_tm [] R) := by
  unfold cfg_C cfg_DR0; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_nil]; countExecute 1

theorem rule_C_zero_nil (R : List ℕ) :
    (cfg_C target_tm [0] R) [target_tm]⊢ᶜ[3] (cfg_C target_tm [] (1 :: R)) := by
  unfold cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_zero [], encLeft_nil, encRight_succ 0 R, encRight_zero R]; countExecute 3

theorem rule_C_zero_zero (L R : List ℕ) :
    (cfg_C target_tm (0 :: 0 :: L) R) [target_tm]⊢ᶜ[5] (cfg_C target_tm (bumpHead L) (1 :: R)) := by
  unfold cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_zero (0 :: L), encLeft_zero L, encRight_succ 0 R, encRight_zero R]; countExecute 5

theorem rule_C_zero_one (L R : List ℕ) :
    (cfg_C target_tm (0 :: 1 :: L) R) [target_tm]⊢ᶜ[17]
    (cfg_C target_tm (bumpHead (bumpHead L)) (0 :: bumpHead R)) := by
  unfold cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_zero (1 :: L), encLeft_succ 0 L, encLeft_zero L, encRight_zero (bumpHead R)]
  countExecute 17

theorem rule_C_zero_add_two (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (0 :: (a + 2) :: L) R) [target_tm]⊢ᶜ[4] (cfg_BR target_tm (a :: L) (0 :: 1 ::
        R)) := by
  unfold cfg_C cfg_BR; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_zero ((a + 2) :: L), encLeft_succ (a + 1) L, encLeft_succ a L,
    encRight_zero (1 :: R), encRight_succ 0 R, encRight_zero R]; countExecute 4

theorem rule_C_one_nil (R : List ℕ) :
    (cfg_C target_tm [1] R) [target_tm]⊢ᶜ[5] (cfg_B target_tm [0] (1 :: R)) := by
  unfold cfg_C cfg_B; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_succ 0 [], encLeft_zero [], encLeft_nil, encRight_succ 0 R, encRight_zero R]
  countExecute 5

theorem rule_C_one_zero (L R : List ℕ) :
    (cfg_C target_tm (1 :: 0 :: L) R) [target_tm]⊢ᶜ[7] (cfg_DR0 target_tm L (2 :: R)) := by
  unfold cfg_C cfg_DR0; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_succ 0 (0 :: L), encLeft_zero (0 :: L), encLeft_zero L,
    encRight_succ 1 R, encRight_succ 0 R, encRight_zero R]; countExecute 7

theorem rule_C_one_succ (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (1 :: (a + 1) :: L) R) [target_tm]⊢ᶜ[6] (cfg_C target_tm (a :: L) (2 :: R)) :=
        by
  unfold cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_succ 0 ((a + 1) :: L), encLeft_zero ((a + 1) :: L), encLeft_succ a L,
    encRight_succ 1 R, encRight_succ 0 R, encRight_zero R]; countExecute 6

theorem rule_C_add_two_step (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm ((a + 2) :: L) R) [target_tm]⊢ᶜ[3]
    (cfg_Halt ((([1] : List (Fin 2)) ^ a) +> ((encLeft1 L).cons 0))
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encRight1 R)) := by
  unfold cfg_C cfg_Halt; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_succ (a + 1) L, encLeft_succ a L, encLeft_expose a L]; countExecute 3

theorem rule_C_add_two_halt (a : ℕ) (L R : List ℕ) :
    ∃ cfg', ((cfg_C target_tm ((a + 2) :: L) R) [target_tm]⊢ᶜ[3] cfg') ∧
      (step target_tm cfg').isNone :=
  ⟨cfg_Halt ((([1] : List (Fin 2)) ^ a) +> ((encLeft1 L).cons 0))
    ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encRight1 R),
   rule_C_add_two_step a L R, rfl⟩



instance countedRules : CountedRules target_tm where
  rule_B_nil := rule_B_nil
  rule_B_zero := rule_B_zero
  rule_B_succ := rule_B_succ
  rule_BR_nil := rule_BR_nil
  rule_BR_zero := rule_BR_zero
  rule_BR_one := rule_BR_one
  rule_BR_add_two := rule_BR_add_two
  rule_DR0_nil := rule_DR0_nil
  rule_DR0_zero := rule_DR0_zero
  rule_DR0_succ := rule_DR0_succ
  rule_C_nil := rule_C_nil
  rule_C_zero_nil := rule_C_zero_nil
  rule_C_zero_zero := rule_C_zero_zero
  rule_C_zero_one := rule_C_zero_one
  rule_C_zero_add_two := rule_C_zero_add_two
  rule_C_one_nil := rule_C_one_nil
  rule_C_one_zero := rule_C_one_zero
  rule_C_one_succ := rule_C_one_succ
  rule_C_add_two_halt := rule_C_add_two_halt

end First

namespace Second

abbrev target_tm : Machine (Fin 2) (Fin 6) := BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.target
@[simp] theorem isFlipped_tm : isFlipped target_tm = true := rfl

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def E : Fin 6 := 4
def F : Fin 6 := 5

@[simp] theorem init_nil : (init ([] : List (Fin 2))) = ⟨some A, ⟨0, default, default⟩⟩ := rfl

def cfg_Halt (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some F, ⟨1, r, l⟩⟩

theorem init_reaches_stack : (init []) [target_tm]⊢ᶜ[1] (cfg_C target_tm [] [0]) := by
  rw [init_nil]; unfold cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_zero, encLeft_nil, encRight_nil]; countExecute 1

theorem rule_B_nil (L : List ℕ) :
    (cfg_B target_tm L []) [target_tm]⊢ᶜ[1] (cfg_C target_tm (bumpHead L) []) := by
  unfold cfg_B cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_nil]; countExecute 1

theorem rule_B_zero (L R : List ℕ) :
    (cfg_B target_tm L (0 :: R)) [target_tm]⊢ᶜ[4] (cfg_B target_tm (0 :: L) R) := by
  unfold cfg_B; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_zero R, encRight_zero L];
      countExecute 4

theorem rule_B_succ (d : ℕ) (L R : List ℕ) :
    (cfg_B target_tm L ((d + 1) :: R)) [target_tm]⊢ᶜ[2] (cfg_BR target_tm L (0 :: d :: R)) := by
  unfold cfg_B cfg_BR; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_succ d R, encLeft_zero (d :: R), encLeft_expose d R]; countExecute 2

theorem rule_BR_nil (L : List ℕ) :
    (cfg_BR target_tm L []) [target_tm]⊢ᶜ[1] (cfg_C target_tm (bumpHead L) []) :=
  rule_B_nil L

theorem rule_BR_zero (L R : List ℕ) :
    (cfg_BR target_tm L (0 :: R)) [target_tm]⊢ᶜ[2] (cfg_BR target_tm (0 :: L) R) := by
  unfold cfg_BR; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_zero R, encRight_zero L];
      countExecute 2

theorem rule_BR_one (L R : List ℕ) :
    (cfg_BR target_tm L (1 :: R)) [target_tm]⊢ᶜ[4] (cfg_DR0 target_tm L (bumpHead R)) := by
  unfold cfg_BR cfg_DR0; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_succ 0 R,
      encLeft_zero R]; countExecute 4

theorem rule_BR_add_two (d : ℕ) (L R : List ℕ) :
    (cfg_BR target_tm L ((d + 2) :: R)) [target_tm]⊢ᶜ[5] (cfg_B target_tm (bumpHead L) (d :: R)) :=
        by
  unfold cfg_BR cfg_B; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encLeft_succ (d + 1) R, encLeft_succ d R, encLeft_expose d R]; countExecute 5

theorem rule_DR0_nil (R : List ℕ) :
    (cfg_DR0 target_tm [] R) [target_tm]⊢ᶜ[3] (cfg_C target_tm [1] R) := by
  unfold cfg_DR0 cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_nil, encRight_succ 0 [], encRight_zero [], encRight_nil]; countExecute 3

theorem rule_DR0_zero (L R : List ℕ) :
    (cfg_DR0 target_tm (0 :: L) R) [target_tm]⊢ᶜ[4] (cfg_DR0 target_tm L (0 :: R)) := by
  unfold cfg_DR0; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_zero L, encLeft_zero R];
      countExecute 4

theorem rule_DR0_succ (a : ℕ) (L R : List ℕ) :
    (cfg_DR0 target_tm ((a + 1) :: L) R) [target_tm]⊢ᶜ[3] (cfg_C target_tm (a :: L) (0 :: R)) := by
  unfold cfg_DR0 cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_succ a L,
      encLeft_zero R]; countExecute 3

theorem rule_C_nil (R : List ℕ) :
    (cfg_C target_tm [] R) [target_tm]⊢ᶜ[1] (cfg_DR0 target_tm [] R) := by
  unfold cfg_C cfg_DR0; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_nil]; countExecute 1

theorem rule_C_zero_nil (R : List ℕ) :
    (cfg_C target_tm [0] R) [target_tm]⊢ᶜ[3] (cfg_C target_tm [] (1 :: R)) := by
  unfold cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_zero [], encRight_nil, encLeft_succ 0 R, encLeft_zero R]; countExecute 3

theorem rule_C_zero_zero (L R : List ℕ) :
    (cfg_C target_tm (0 :: 0 :: L) R) [target_tm]⊢ᶜ[5] (cfg_C target_tm (bumpHead L) (1 :: R)) := by
  unfold cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_zero (0 :: L), encRight_zero L, encLeft_succ 0 R, encLeft_zero R]; countExecute 5

theorem rule_C_zero_one (L R : List ℕ) :
    (cfg_C target_tm (0 :: 1 :: L) R) [target_tm]⊢ᶜ[17]
    (cfg_C target_tm (bumpHead (bumpHead L)) (0 :: bumpHead R)) := by
  unfold cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_zero (1 :: L), encRight_succ 0 L, encRight_zero L, encLeft_zero (bumpHead R)]
  countExecute 17

theorem rule_C_zero_add_two (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (0 :: (a + 2) :: L) R) [target_tm]⊢ᶜ[4] (cfg_BR target_tm (a :: L) (0 :: 1 ::
        R)) := by
  unfold cfg_C cfg_BR; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_zero ((a + 2) :: L), encRight_succ (a + 1) L, encRight_succ a L,
    encLeft_zero (1 :: R), encLeft_succ 0 R, encLeft_zero R]; countExecute 4

theorem rule_C_one_nil (R : List ℕ) :
    (cfg_C target_tm [1] R) [target_tm]⊢ᶜ[5] (cfg_B target_tm [0] (1 :: R)) := by
  unfold cfg_C cfg_B; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_succ 0 [], encRight_zero [], encRight_nil, encLeft_succ 0 R, encLeft_zero R]
  countExecute 5

theorem rule_C_one_zero (L R : List ℕ) :
    (cfg_C target_tm (1 :: 0 :: L) R) [target_tm]⊢ᶜ[7] (cfg_DR0 target_tm L (2 :: R)) := by
  unfold cfg_C cfg_DR0; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_succ 0 (0 :: L), encRight_zero (0 :: L), encRight_zero L,
    encLeft_succ 1 R, encLeft_succ 0 R, encLeft_zero R]; countExecute 7

theorem rule_C_one_succ (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (1 :: (a + 1) :: L) R) [target_tm]⊢ᶜ[6] (cfg_C target_tm (a :: L) (2 :: R)) :=
        by
  unfold cfg_C; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_succ 0 ((a + 1) :: L), encRight_zero ((a + 1) :: L), encRight_succ a L,
    encLeft_succ 1 R, encLeft_succ 0 R, encLeft_zero R]; countExecute 6

theorem rule_C_add_two_step (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm ((a + 2) :: L) R) [target_tm]⊢ᶜ[3]
    (cfg_Halt (((encRight1 L).cons 0) <+ (([1] : List (Fin 2)) ^ a))
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encLeft1 R)) := by
  unfold cfg_C cfg_Halt; simp only [isFlipped_tm, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [encRight_succ (a + 1) L, encRight_succ a L, encRight_expose a L]; countExecute 3

theorem rule_C_add_two_halt (a : ℕ) (L R : List ℕ) :
    ∃ cfg', ((cfg_C target_tm ((a + 2) :: L) R) [target_tm]⊢ᶜ[3] cfg') ∧
      (step target_tm cfg').isNone :=
  ⟨cfg_Halt (((encRight1 L).cons 0) <+ (([1] : List (Fin 2)) ^ a))
    ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encLeft1 R),
   rule_C_add_two_step a L R, rfl⟩



instance countedRules : CountedRules target_tm where
  rule_B_nil := rule_B_nil
  rule_B_zero := rule_B_zero
  rule_B_succ := rule_B_succ
  rule_BR_nil := rule_BR_nil
  rule_BR_zero := rule_BR_zero
  rule_BR_one := rule_BR_one
  rule_BR_add_two := rule_BR_add_two
  rule_DR0_nil := rule_DR0_nil
  rule_DR0_zero := rule_DR0_zero
  rule_DR0_succ := rule_DR0_succ
  rule_C_nil := rule_C_nil
  rule_C_zero_nil := rule_C_zero_nil
  rule_C_zero_zero := rule_C_zero_zero
  rule_C_zero_one := rule_C_zero_one
  rule_C_zero_add_two := rule_C_zero_add_two
  rule_C_one_nil := rule_C_one_nil
  rule_C_one_zero := rule_C_one_zero
  rule_C_one_succ := rule_C_one_succ
  rule_C_add_two_halt := rule_C_add_two_halt

end Second

end BB6.Agent17.RleCounted

#print axioms BB6.Agent17.RleCounted.First.countedRules
#print axioms BB6.Agent17.RleCounted.Second.countedRules
#print axioms BB6.Agent17.RleCounted.First.init_reaches_stack
#print axioms BB6.Agent17.RleCounted.Second.init_reaches_stack
