/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import TowerCost


open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.F067Counted


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RC_1RC0LD_1LD1RA_1LF0LE_HHH0RD_1LB0LA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

abbrev target_tm : Machine (Fin 2) (Fin 6) := target
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

@[simp] theorem multiStep_zero (M : Machine Γ Λ) (c : Cfg Γ Λ) : multiStep M c 0 = some c := rfl
@[simp] theorem multiStep_one (M : Machine Γ Λ) (c : Cfg Γ Λ) : multiStep M c 1 = step M c := rfl

theorem multiStep_succ (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep M c (n + 1) = (multiStep M c n).bind (step M) := by
  simp only [multiStep, Function.iterate_succ_apply']

theorem multiStep_add (M : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : ℕ) :
    multiStep M c₁ (n + m) = (multiStep M c₁ n).bind (fun c₂ => multiStep M c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    simp_rw [multiStep_succ]

theorem multiStep_trans (M : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : ℕ)
    (h₁ : c₁ [M]⊢^{n} c₂) (h₂ : c₂ [M]⊢^{m} c₃) :
    c₁ [M]⊢^{n+m} c₃ := by
  rw [multiStep_add, h₁]; simp [h₂]


-- Counted composition retains the exact number of live primitive transitions.
theorem countedCast {M : Machine Γ Λ} {s t : Cfg Γ Λ} {n m : ℕ}
    (h : ReachesIn M n s t) (he : n = m) : ReachesIn M m s t :=
  he ▸ h

theorem countedPrepend {M : Machine Γ Λ} {s t u : Cfg Γ Λ} {n total : ℕ}
    (h : ReachesIn M n s t) (hle : n ≤ total)
    (hrest : ReachesIn M (total - n) t u) : ReachesIn M total s u := by
  exact countedCast (ReachesIn.trans h hrest) (by omega)

macro "exact_counted" h:term : tactic =>
  `(tactic| first | exact $h | (refine countedCast $h ?_; omega))

@[simp] theorem pow_zero_list (u : List (Fin 2)) : u ^ (0 : Nat) = [] := rfl
@[simp] theorem pow_succ_list (u : List (Fin 2)) (n : Nat) : u ^ (n + 1) = u ++ u ^ n := rfl
@[simp] theorem nil_append_list (l : List (Fin 2)) : ([] : List (Fin 2)) ++ l = l := rfl
@[simp] theorem cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
@[simp] theorem append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] theorem listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] theorem listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) :
    (x :: xs) +> b = x >> (xs +> b) := rfl
@[simp] theorem zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] theorem default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] theorem default_tail : (default : ListBlank (Fin 2)).tail = default := rfl
@[simp] theorem init_nil : (init ([] : List (Fin 2))) = ⟨some A, ⟨0, default, default⟩⟩ := rfl

omit [Inhabited Γ] in
@[simp]
theorem listblank_append_pow_add (s : ListBlank (Fin 2)) (n m : ℕ) :
    (s <+ (([1] : List (Fin 2)) ^ n)) <+ (([1] : List (Fin 2)) ^ m) =
    s <+ (([1] : List (Fin 2)) ^ (n + m)) := by
  rw [listblank_append_append, list_pow_add_comm, ← list_pow_add]

theorem listblank_right_pow_add (s : ListBlank (Fin 2)) (n m : ℕ) :
    (([1] : List (Fin 2)) ^ n) +> ((([1] : List (Fin 2)) ^ m) +> s) =
    (([1] : List (Fin 2)) ^ (n + m)) +> s := by
  rw [← listblank_append_right_assoc, ← list_pow_add]

-- ============================================================================
-- Section 1: 2nd-Order Digit-Stack Encodings & 16 Local Separator Rules
-- ============================================================================

def encLeft1 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: L => ((encLeft1 L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1))

def encRight1 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | d :: R => (([1] : List (Fin 2)) ^ (d + 1)) +> ((encRight1 R).cons 0)

@[simp] theorem encLeft_nil : encLeft1 [] = default := rfl
@[simp] theorem encLeft_cons (a : ℕ) (L : List ℕ) :
    encLeft1 (a :: L) = ((encLeft1 L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1)) := rfl
@[simp] theorem encRight_nil : encRight1 [] = default := rfl
@[simp] theorem encRight_cons (d : ℕ) (R : List ℕ) :
    encRight1 (d :: R) = (([1] : List (Fin 2)) ^ (d + 1)) +> ((encRight1 R).cons 0) := rfl

def bumpHead : List ℕ → List ℕ
  | [] => [0]
  | b :: L => (b + 1) :: L

@[simp] theorem encLeft_cons_one (L : List ℕ) :
    (1 : Fin 2) >> encLeft1 L = encLeft1 (bumpHead L) := by
  cases L with
  | nil => simp [bumpHead, encLeft1]
  | cons b L' => rfl

@[simp] theorem encRight_cons_one (R : List ℕ) :
    (1 : Fin 2) >> encRight1 R = encRight1 (bumpHead R) := by
  cases R with
  | nil => simp [bumpHead, encRight1]
  | cons d R' => rfl

macro "finish" : tactic => `(tactic| (simp only [ReachesIn, BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, zero_cons_default, encLeft_nil, encRight_nil, encLeft_cons_one, encRight_cons_one, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head, default_tail, multiStep_zero]; try rfl))
macro "step" : tactic => `(tactic| (
  try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons, default_head]
  apply ReachesIn.step_left (by rfl)
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    zero_cons_default, default_head, default_tail]))
macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

def cfg_F (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some F, ⟨0, encLeft1 L, encRight1 R⟩⟩

def cfg_AR (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  (encLeft1 L) {{A}}> (encRight1 R)

inductive StackMode
  | F
  | AR
  deriving DecidableEq, Repr

def evalStackCfg : StackMode → List ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .F, L, R => cfg_F L R
  | .AR, L, R => cfg_AR L R

@[simp] theorem evalStackCfg_F (L R : List ℕ) : evalStackCfg .F L R = cfg_F L R := rfl
@[simp] theorem evalStackCfg_AR (L R : List ℕ) : evalStackCfg .AR L R = cfg_AR L R := rfl

-- Mode F Rules (8 Rules)

theorem rule_F_nil (R : List ℕ) :
    (cfg_F [] R) [target_tm]⊢^{3} (cfg_AR [1] R) := by
  unfold cfg_F cfg_AR
  rw [encLeft_nil, encLeft_cons 1 [], encLeft_nil]
  dsimp [HPow.hPow]
  execute 3

theorem rule_F_zero_nil (R : List ℕ) :
    (cfg_F [0] R) [target_tm]⊢^{3} (cfg_F [] (0 :: bumpHead R)) := by
  unfold cfg_F
  rw [encLeft_cons 0 [], encLeft_nil, encRight_cons 0 (bumpHead R)]
  dsimp [HPow.hPow]
  execute 3

theorem rule_F_zero_zero (L R : List ℕ) :
    (cfg_F (0 :: 0 :: L) R) [target_tm]⊢^{12} (cfg_F (bumpHead (bumpHead L)) (0 :: R)) := by
  unfold cfg_F
  rw [encLeft_cons 0 (0 :: L), encLeft_cons 0 L, encRight_cons 0 R]
  dsimp [HPow.hPow]
  execute 12

theorem rule_F_zero_one (L R : List ℕ) :
    (cfg_F (0 :: 1 :: L) R) [target_tm]⊢^{7} (cfg_F L (2 :: bumpHead R)) := by
  unfold cfg_F
  rw [encLeft_cons 0 (1 :: L), encLeft_cons 1 L, encRight_cons 2 (bumpHead R)]
  dsimp [HPow.hPow]
  execute 7

theorem rule_F_zero_add_two (L R : List ℕ) (b : ℕ) :
    (cfg_F (0 :: (b + 2) :: L) R) [target_tm]⊢^{4} (cfg_AR (b :: L) (0 :: 0 :: bumpHead R)) := by
  unfold cfg_F cfg_AR
  rw [encLeft_cons 0 ((b + 2) :: L), encLeft_cons (b + 2) L, encLeft_cons b L,
      encRight_cons 0 (0 :: bumpHead R), encRight_cons 0 (bumpHead R)]
  have hb : b + 2 + 1 = (b + 1) + 2 := by omega
  rw [hb, ← listblank_append_pow_add ((encLeft1 L).cons 0) (b + 1) 2]
  dsimp [HPow.hPow]
  execute 4

def cfg_Halt_F (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, encLeft1 L, (0 : Fin 2) >> (0 : Fin 2) >> encRight1 (bumpHead R)⟩⟩

theorem rule_F_one (L R : List ℕ) :
    ((cfg_F (1 :: L) R) [target_tm]⊢^{3} (cfg_Halt_F L R)) ∧
    (step target_tm (cfg_Halt_F L R)).isNone := by
  refine ⟨?_, rfl⟩
  unfold cfg_F cfg_Halt_F
  rw [encLeft_cons 1 L]
  dsimp [HPow.hPow]
  execute 3

theorem rule_F_one_halt (L R : List ℕ) :
    ∃ cfg, ((cfg_F (1 :: L) R) [target_tm]⊢^{3} cfg) ∧ (step target_tm cfg).isNone :=
  ⟨cfg_Halt_F L R, (rule_F_one L R).1, (rule_F_one L R).2⟩

theorem rule_F_two (L R : List ℕ) :
    (cfg_F (2 :: L) R) [target_tm]⊢^{8} (cfg_AR (bumpHead (bumpHead L)) (0 :: bumpHead R)) := by
  unfold cfg_F cfg_AR
  rw [encLeft_cons 2 L, encRight_cons 0 (bumpHead R)]
  dsimp [HPow.hPow]
  execute 8

theorem rule_F_add_three (L R : List ℕ) (a : ℕ) :
    (cfg_F ((a + 3) :: L) R) [target_tm]⊢^{5} (cfg_F (a :: L) (0 :: bumpHead R)) := by
  unfold cfg_F
  rw [encLeft_cons (a + 3) L, encLeft_cons a L, encRight_cons 0 (bumpHead R)]
  have ha : a + 3 + 1 = (a + 1) + 3 := by omega
  rw [ha, ← listblank_append_pow_add ((encLeft1 L).cons 0) (a + 1) 3]
  dsimp [HPow.hPow]
  execute 5

-- Mode AR Rules (8 Rules)

theorem rule_AR_nil (L : List ℕ) :
    (cfg_AR L []) [target_tm]⊢^{6} (cfg_F L [1]) := by
  unfold cfg_AR cfg_F
  rw [encRight_nil, encRight_cons 1 [], encRight_nil]
  dsimp [HPow.hPow]
  execute 6

theorem rule_AR_nil_zero (R : List ℕ) :
    (cfg_AR [] (0 :: R)) [target_tm]⊢^{3} (cfg_F [] (bumpHead (bumpHead R))) := by
  unfold cfg_AR cfg_F
  rw [encLeft_nil, encRight_cons 0 R]
  dsimp [HPow.hPow]
  execute 3

theorem rule_AR_zero_zero (L R : List ℕ) :
    (cfg_AR (0 :: L) (0 :: R)) [target_tm]⊢^{7}
    (cfg_AR (bumpHead (bumpHead (bumpHead L))) (bumpHead R)) := by
  unfold cfg_AR
  rw [encLeft_cons 0 L, encRight_cons 0 R]
  cases R with
  | nil =>
    rw [show bumpHead ([] : List ℕ) = [0] from rfl, encRight_cons 0 [], encRight_nil]
    dsimp [HPow.hPow]
    execute 7
  | cons d R' =>
    rw [show bumpHead (d :: R') = (d + 1) :: R' from rfl,
        encRight_cons (d + 1) R', encRight_cons d R']
    have hd : d + 1 + 1 = 1 + (d + 1) := by omega
    rw [hd, ← listblank_right_pow_add ((encRight1 R').cons 0) 1 (d + 1)]
    dsimp [HPow.hPow]
    execute 7

theorem rule_AR_one_zero (L R : List ℕ) :
    (cfg_AR (1 :: L) (0 :: R)) [target_tm]⊢^{7}
    (cfg_F L (bumpHead (bumpHead (bumpHead (bumpHead R))))) := by
  unfold cfg_AR cfg_F
  rw [encLeft_cons 1 L, encRight_cons 0 R]
  dsimp [HPow.hPow]
  execute 7

theorem rule_AR_add_two_zero (L R : List ℕ) (a : ℕ) :
    (cfg_AR ((a + 2) :: L) (0 :: R)) [target_tm]⊢^{4}
    (cfg_AR (a :: L) (0 :: bumpHead (bumpHead R))) := by
  unfold cfg_AR
  rw [encLeft_cons (a + 2) L, encLeft_cons a L,
      encRight_cons 0 R, encRight_cons 0 (bumpHead (bumpHead R))]
  have ha : a + 2 + 1 = (a + 1) + 2 := by omega
  rw [ha, ← listblank_append_pow_add ((encLeft1 L).cons 0) (a + 1) 2]
  dsimp [HPow.hPow]
  execute 4

theorem rule_AR_one_nil (L : List ℕ) :
    (cfg_AR L [1]) [target_tm]⊢^{2} (cfg_AR (0 :: L) []) := by
  unfold cfg_AR
  rw [encLeft_cons 0 L, encRight_cons 1 [], encRight_nil]
  dsimp [HPow.hPow]
  execute 2

theorem rule_AR_one_cons (L R : List ℕ) (e : ℕ) :
    (cfg_AR L (1 :: e :: R)) [target_tm]⊢^{14} (cfg_AR L (0 :: (e + 1) :: R)) := by
  unfold cfg_AR
  rw [encRight_cons 1 (e :: R), encRight_cons e R,
      encRight_cons 0 ((e + 1) :: R), encRight_cons (e + 1) R]
  have he1 : e + 1 = 1 + e := by omega
  have he2 : e + 1 + 1 = 2 + e := by omega
  rw [he2, ← listblank_right_pow_add ((encRight1 R).cons 0) 2 e]
  rw [he1, ← listblank_right_pow_add ((encRight1 R).cons 0) 1 e]
  dsimp [HPow.hPow]
  execute 14

theorem rule_AR_add_two (L R : List ℕ) (d : ℕ) :
    (cfg_AR L ((d + 2) :: R)) [target_tm]⊢^{2} (cfg_AR (0 :: L) (d :: R)) := by
  unfold cfg_AR
  rw [encLeft_cons 0 L, encRight_cons (d + 2) R, encRight_cons d R]
  have hd : d + 2 + 1 = 3 + d := by omega
  rw [hd, ← listblank_right_pow_add ((encRight1 R).cons 0) 3 d]
  have hd2 : d + 1 = 1 + d := by omega
  rw [hd2, ← listblank_right_pow_add ((encRight1 R).cons 0) 1 d]
  dsimp [HPow.hPow]
  execute 2

-- ============================================================================
-- Section 2: Multi-Step Bulk Contractions on `List ℕ`
-- ============================================================================

theorem bumpHead_iterate_cons (k v : ℕ) (L : List ℕ) :
    bumpHead^[k] (v :: L) = (v + k) :: L := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, bumpHead, ih (v + 1)]
    have h : v + 1 + k = v + (k + 1) := by omega
    rw [h]

theorem bumpHead_iterate_nil (k : ℕ) :
    bumpHead^[k + 1] [] = [k] := by
  rw [Function.iterate_succ_apply, bumpHead, bumpHead_iterate_cons, Nat.zero_add]

theorem bumpHead2_iterate_eq (k : ℕ) (R : List ℕ) :
    (fun R => bumpHead (bumpHead R))^[k] R = bumpHead^[2 * k] R := by
  induction k generalizing R with
  | zero => simp
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [Function.iterate_succ_apply', ih, h2, Function.iterate_add_apply]
    rfl

def stepF3Right : ℕ → List ℕ → List ℕ
  | 0, R => R
  | k + 1, R => stepF3Right k (0 :: bumpHead R)

theorem stepF3Right_succ (k : ℕ) (R : List ℕ) :
    stepF3Right (k + 1) R = 0 :: (List.replicate k 1 ++ bumpHead R) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [stepF3Right, ih (0 :: bumpHead R)]
    have h : List.replicate (k + 1) 1 ++ bumpHead R = List.replicate k 1 ++ (1 :: bumpHead R) := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rw [h]
    rfl

theorem rule_F_step3_all (L R : List ℕ) (a k : ℕ) :
    (cfg_F ((3 * k + a) :: L) R) [target_tm]⊢^{5*k}
    (cfg_F (a :: L) (stepF3Right k R)) := by
  induction k generalizing R with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, stepF3Right]
    try exact_counted ReachesIn.zero _ _
  | succ k ih =>
    have h1 : 3 * (k + 1) + a = (3 * k + a) + 3 := by omega
    rw [h1, stepF3Right]
    exact_counted ReachesIn.trans ((rule_F_add_three L R (3 * k + a))) (ih (0 :: bumpHead R))

theorem rule_AR_step2_all (L R : List ℕ) (d k : ℕ) :
    (cfg_AR L ((2 * k + d) :: R)) [target_tm]⊢^{2*k}
    (cfg_AR (List.replicate k 0 ++ L) (d :: R)) := by
  induction k generalizing L with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, List.replicate, List.nil_append]
    try exact_counted ReachesIn.zero _ _
  | succ k ih =>
    have h1 : 2 * (k + 1) + d = (2 * k + d) + 2 := by omega
    have h2 : List.replicate (k + 1) 0 ++ L = List.replicate k 0 ++ (0 :: L) := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rw [h1, h2]
    exact_counted ReachesIn.trans ((rule_AR_add_two L R (2 * k + d))) (ih (0 :: L))

theorem rule_AR_add_two_zero_all (L R : List ℕ) (a k : ℕ) :
    (cfg_AR ((2 * k + a) :: L) (0 :: R)) [target_tm]⊢^{4*k}
    (cfg_AR (a :: L) (0 :: (fun R => bumpHead (bumpHead R))^[k] R)) := by
  induction k generalizing R with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Function.iterate_zero, id_eq]
    try exact_counted ReachesIn.zero _ _
  | succ k ih =>
    have h_eq : 2 * (k + 1) + a = 2 * k + a + 2 := by omega
    rw [h_eq, Function.iterate_succ_apply]
    exact_counted ReachesIn.trans ((rule_AR_add_two_zero L R (2 * k + a)))
      (ih (bumpHead (bumpHead R)))

theorem rule_F_zero4_one (L : List ℕ) (d : ℕ) (R : List ℕ) :
    (cfg_F (0 :: 0 :: 0 :: 0 :: 0 :: L) (0 :: d :: R)) [target_tm]⊢^{72}
    (cfg_F (0 :: L) (0 :: (d + 8) :: R)) := by
  refine countedPrepend ((rule_F_zero_zero (0 :: 0 :: 0 :: L) (0 :: d :: R))) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_F_two (0 :: 0 :: L) (0 :: 0 :: d :: R))) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two_zero (0 :: L) (1 :: 0 :: d :: R) 0)) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_zero_zero (0 :: L) (3 :: 0 :: d :: R))) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two (3 :: L) (0 :: d :: R) 2)) (by omega) ?_
  refine countedPrepend ((rule_AR_add_two (0 :: 3 :: L) (0 :: d :: R) 0)) (by omega) ?_
  refine countedPrepend ((rule_AR_zero_zero (0 :: 3 :: L) (0 :: d :: R))) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_one_cons (3 :: 3 :: L) R d)) (by omega) ?_
  refine countedPrepend ((rule_AR_add_two_zero (3 :: L) ((d + 1) :: R) 1)) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_one_zero (3 :: L) ((d + 1 + 1 + 1) :: R))) (by omega) ?_
  dsimp [bumpHead]
  have hd : d + 1 + 1 + 1 + 1 + 1 + 1 + 1 = d + 7 := by omega
  rw [hd]
  refine countedPrepend ((rule_F_add_three L ((d + 7) :: R) 0)) (by omega) ?_
  dsimp [bumpHead]
  try exact_counted ReachesIn.zero _ _

theorem rule_F_zero4_all (k r : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ) :
    (cfg_F (List.replicate (4 * k + r + 1) 0 ++ L) (0 :: d :: R)) [target_tm]⊢^{72*k}
    (cfg_F (List.replicate (r + 1) 0 ++ L) (0 :: (d + 8 * k) :: R)) := by
  induction k generalizing d with
  | zero =>
    simp
    try exact_counted ReachesIn.zero _ _
  | succ k ih =>
    have h_rep : List.replicate (4 * (k + 1) + r + 1) 0 ++ L =
        0 :: 0 :: 0 :: 0 :: 0 :: (List.replicate (4 * k + r) 0 ++ L) := by
      have h_eq : 4 * (k + 1) + r + 1 = 5 + (4 * k + r) := by omega
      rw [h_eq, List.replicate_add]
      rfl
    rw [h_rep]
    refine countedPrepend (rule_F_zero4_one (List.replicate (4 * k + r) 0 ++ L) d R) (by omega) ?_
    have h_rep2 : 0 :: (List.replicate (4 * k + r) 0 ++ L) = List.replicate (4 * k + r + 1) 0 ++ L := by
      rw [← List.cons_append, ← List.replicate_succ]
    rw [h_rep2]
    have hd : d + 8 * (k + 1) = (d + 8) + 8 * k := by omega
    rw [hd]
    exact_counted ih (d + 8)

theorem rule_AR_zero_ones_all (m b : ℕ) (L R : List ℕ) :
    (cfg_AR (0 :: b :: L) (0 :: (List.replicate m 1 ++ R))) [target_tm]⊢^{9*m}
    (cfg_AR (0 :: (b + 3 * m) :: L) (0 :: R)) := by
  induction m generalizing b with
  | zero =>
    simp
    try exact_counted ReachesIn.zero _ _
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    refine countedPrepend ((rule_AR_zero_zero (b :: L) (1 :: (List.replicate m 1 ++ R)))) (by omega) ?_
    dsimp [bumpHead]
    refine countedPrepend ((rule_AR_add_two ((b + 3) :: L) (List.replicate m 1 ++ R) 0)) (by omega) ?_
    have hb : b + 3 * (m + 1) = (b + 3) + 3 * m := by omega
    rw [hb]
    exact_counted ih (b + 3)

theorem rule_AR_ones_all (m b : ℕ) (L R : List ℕ) :
    (cfg_AR (0 :: b :: L) (List.replicate (m + 1) 1 ++ R)) [target_tm]⊢^{23*m}
    (cfg_AR (0 :: (b + 3 * m) :: L) (1 :: R)) := by
  induction m generalizing b with
  | zero =>
    simp
    try exact_counted ReachesIn.zero _ _
  | succ m ih =>
    have h_rep : List.replicate (m + 2) 1 ++ R = 1 :: 1 :: (List.replicate m 1 ++ R) := rfl
    rw [h_rep]
    refine countedPrepend ((rule_AR_one_cons (0 :: b :: L) (List.replicate m 1 ++ R) 1)) (by omega) ?_
    refine countedPrepend ((rule_AR_zero_zero (b :: L) (2 :: (List.replicate m 1 ++ R)))) (by omega) ?_
    dsimp [bumpHead]
    refine countedPrepend ((rule_AR_add_two ((b + 3) :: L) (List.replicate m 1 ++ R) 1)) (by omega) ?_
    have h_rep2 : 1 :: (List.replicate m 1 ++ R) = List.replicate (m + 1) 1 ++ R := rfl
    rw [h_rep2]
    have hb : b + 3 * (m + 1) = (b + 3) + 3 * m := by omega
    rw [hb]
    exact_counted ih (b + 3)

-- ============================================================================
-- Section 3: 6-Rule Inductive Tower Algebra
-- ============================================================================

def A3 (k : ℕ) (tail : List ℕ) : List ℕ :=
  6 :: 0 :: 0 :: 0 :: (3 * k + 3) :: 3 :: 0 :: tail

def A0 (k : ℕ) (tail : List ℕ) : List ℕ :=
  6 :: 0 :: 0 :: 0 :: (3 * k + 3) :: 0 :: 0 :: 0 :: tail

def B3 (k : ℕ) (tail : List ℕ) : List ℕ :=
  0 :: 3 :: 3 :: 0 :: 0 :: (3 * k + 3) :: 3 :: 0 :: tail

def B0 (k : ℕ) (tail : List ℕ) : List ℕ :=
  0 :: 3 :: 3 :: 0 :: 0 :: (3 * k + 3) :: 0 :: 0 :: 0 :: tail

def SubStep (c : ℕ) (S S' : List ℕ) : Prop :=
  ∀ R_bot : List ℕ,
    (cfg_F (0 :: S) (9 :: R_bot)) [target_tm]⊢^{c}
    (cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: S') (0 :: R_bot))

def TopStep (c : ℕ) (S S' : List ℕ) : Prop :=
  (cfg_F (0 :: S) [5]) [target_tm]⊢^{c} (cfg_F (0 :: S') [5])

def SubHalt (c : ℕ) (S : List ℕ) : Prop :=
  ∀ R_bot : List ℕ,
    ∃ cfg, ((cfg_F (0 :: S) (9 :: R_bot)) [target_tm]⊢^{c} cfg) ∧ (step target_tm cfg).isNone

theorem exit_sub (W : List ℕ) (R_bot : List ℕ) :
    (cfg_AR W (10 :: R_bot)) [target_tm]⊢^{10} (cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: W) (0 :: R_bot)) := by
  simpa using rule_AR_step2_all W R_bot 0 5

theorem exit_top (W : List ℕ) :
    (cfg_AR W [6]) [target_tm]⊢^{24} (cfg_F (0 :: W) [5]) := by
  refine countedPrepend (rule_AR_step2_all W [] 0 3) (by omega) ?_
  dsimp [List.replicate]
  refine countedPrepend ((rule_AR_zero_zero (0 :: 0 :: W) [])) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two_zero (0 :: W) [] 1)) (by omega) ?_
  dsimp [bumpHead]
  exact_counted (rule_AR_one_zero (0 :: W) [1])

theorem subStep_A_any (U : List ℕ) :
    SubStep 56 (6 :: 0 :: 0 :: 0 :: U) (0 :: 3 :: 3 :: 0 :: 0 :: U) := by
  intro R_bot
  refine countedPrepend ((rule_F_zero_add_two (0 :: 0 :: 0 :: U) (9 :: R_bot) 4)) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two_zero (0 :: 0 :: 0 :: U) (0 :: 10 :: R_bot) 2)) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two_zero (0 :: 0 :: 0 :: U) (2 :: 10 :: R_bot) 0)) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_zero_zero (0 :: 0 :: 0 :: U) (4 :: 10 :: R_bot))) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two (3 :: 0 :: 0 :: U) (10 :: R_bot) 3)) (by omega) ?_
  refine countedPrepend ((rule_AR_add_two (0 :: 3 :: 0 :: 0 :: U) (10 :: R_bot) 1)) (by omega) ?_
  refine countedPrepend ((rule_AR_one_cons (0 :: 0 :: 3 :: 0 :: 0 :: U) R_bot 10)) (by omega) ?_
  refine countedPrepend ((rule_AR_zero_zero (0 :: 3 :: 0 :: 0 :: U) (11 :: R_bot))) (by omega) ?_
  dsimp [bumpHead]
  simpa using rule_AR_step2_all (3 :: 3 :: 0 :: 0 :: U) R_bot 0 6

theorem subStep_A3 (k : ℕ) (tail : List ℕ) : SubStep 56 (A3 k tail) (B3 k tail) :=
  subStep_A_any ((3 * k + 3) :: 3 :: 0 :: tail)

theorem subStep_A0 (k : ℕ) (tail : List ℕ) : SubStep 56 (A0 k tail) (B0 k tail) :=
  subStep_A_any ((3 * k + 3) :: 0 :: 0 :: 0 :: tail)

theorem top_A_to_B (U : List ℕ) :
    (cfg_F (0 :: 6 :: 0 :: 0 :: 0 :: U) [5]) [target_tm]⊢^{70}
    (cfg_F (0 :: 0 :: 3 :: 3 :: 0 :: 0 :: U) [5]) := by
  refine countedPrepend ((rule_F_zero_add_two (0 :: 0 :: 0 :: U) [5] 4)) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two_zero (0 :: 0 :: 0 :: U) [0, 6] 2)) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two_zero (0 :: 0 :: 0 :: U) [2, 6] 0)) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_zero_zero (0 :: 0 :: 0 :: U) [4, 6])) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two (3 :: 0 :: 0 :: U) [6] 3)) (by omega) ?_
  refine countedPrepend ((rule_AR_add_two (0 :: 3 :: 0 :: 0 :: U) [6] 1)) (by omega) ?_
  refine countedPrepend ((rule_AR_one_cons (0 :: 0 :: 3 :: 0 :: 0 :: U) [] 6)) (by omega) ?_
  refine countedPrepend ((rule_AR_zero_zero (0 :: 3 :: 0 :: 0 :: U) [7])) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend (rule_AR_step2_all (3 :: 3 :: 0 :: 0 :: U) [] 0 4) (by omega) ?_
  dsimp [List.replicate]
  refine countedPrepend ((rule_AR_zero_zero (0 :: 0 :: 0 :: 3 :: 3 :: 0 :: 0 :: U) [])) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two_zero (0 :: 0 :: 3 :: 3 :: 0 :: 0 :: U) [] 1)) (by omega) ?_
  dsimp [bumpHead]
  exact_counted (rule_AR_one_zero (0 :: 0 :: 3 :: 3 :: 0 :: 0 :: U) [1])

theorem step_B_prefix (V : List ℕ) (d₀ : ℕ) (R_rest : List ℕ) :
    (cfg_F (0 :: 0 :: 3 :: 3 :: 0 :: 0 :: V) (d₀ :: R_rest)) [target_tm]⊢^{40}
    (cfg_F (0 :: 0 :: V) (9 :: 1 :: d₀ :: R_rest)) := by
  refine countedPrepend ((rule_F_zero_zero (3 :: 3 :: 0 :: 0 :: V) (d₀ :: R_rest))) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_F_add_three (3 :: 0 :: 0 :: V) (0 :: d₀ :: R_rest) 2)) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_F_two (3 :: 0 :: 0 :: V) (0 :: 1 :: d₀ :: R_rest))) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two_zero (0 :: 0 :: V) (1 :: 1 :: d₀ :: R_rest) 3)) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two_zero (0 :: 0 :: V) (3 :: 1 :: d₀ :: R_rest) 1)) (by omega) ?_
  dsimp [bumpHead]
  exact_counted (rule_AR_one_zero (0 :: 0 :: V) (5 :: 1 :: d₀ :: R_rest))

theorem step_B0_core (k : ℕ) (tail : List ℕ) (d₀ : ℕ) (R_rest : List ℕ) :
    (cfg_F (0 :: B0 k tail) (d₀ :: R_rest)) [target_tm]⊢^{14*k+122}
    (cfg_AR (A3 (k + 1) tail) ((d₀ + 1) :: R_rest)) := by
  unfold B0
  refine countedPrepend (step_B_prefix ((3 * k + 3) :: 0 :: 0 :: 0 :: tail) d₀ R_rest) (by omega) ?_
  refine countedPrepend ((rule_F_zero_zero ((3 * k + 3) :: 0 :: 0 :: 0 :: tail) (9 :: 1 :: d₀ :: R_rest))) (by omega) ?_
  dsimp [bumpHead]
  have hk1 : 3 * k + 3 + 1 + 1 = 3 * (k + 1) + 2 := by omega
  rw [hk1]
  refine countedPrepend (rule_F_step3_all (0 :: 0 :: 0 :: tail) (0 :: 9 :: 1 :: d₀ :: R_rest) 2 (k + 1)) (by omega) ?_
  rw [stepF3Right_succ k (0 :: 9 :: 1 :: d₀ :: R_rest)]
  dsimp [bumpHead]
  refine countedPrepend ((rule_F_two (0 :: 0 :: 0 :: tail)
    (0 :: (List.replicate k 1 ++ (1 :: 9 :: 1 :: d₀ :: R_rest))))) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two_zero (0 :: 0 :: tail)
    (1 :: (List.replicate k 1 ++ (1 :: 9 :: 1 :: d₀ :: R_rest))) 0)) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_zero_zero (0 :: 0 :: tail)
    (3 :: (List.replicate k 1 ++ (1 :: 9 :: 1 :: d₀ :: R_rest))))) (by omega) ?_
  dsimp [bumpHead]
  have h_rep : List.replicate k 1 ++ (1 :: 9 :: 1 :: d₀ :: R_rest) =
      List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest) := by
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]
  rw [h_rep]
  refine countedPrepend (rule_AR_step2_all (3 :: 0 :: tail)
    (List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest)) 0 2) (by omega) ?_
  dsimp [List.replicate]
  refine countedPrepend (rule_AR_zero_ones_all (k + 1) 0 (3 :: 0 :: tail) (9 :: 1 :: d₀ :: R_rest)) (by omega) ?_
  rw [Nat.zero_add]
  refine countedPrepend ((rule_AR_zero_zero ((3 * (k + 1)) :: 3 :: 0 :: tail) (9 :: 1 :: d₀ :: R_rest))) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend (rule_AR_step2_all ((3 * (k + 1) + 3) :: 3 :: 0 :: tail) (1 :: d₀ :: R_rest) 0 5) (by omega) ?_
  dsimp [List.replicate]
  refine countedPrepend (rule_AR_zero_ones_all 1 0 (0 :: 0 :: 0 :: (3 * (k + 1) + 3) :: 3 :: 0 :: tail) (d₀ :: R_rest)) (by omega) ?_
  dsimp
  refine countedPrepend ((rule_AR_zero_zero
    (3 :: 0 :: 0 :: 0 :: (3 * (k + 1) + 3) :: 3 :: 0 :: tail) (d₀ :: R_rest))) (by omega) ?_
  dsimp [bumpHead, A3]
  try exact_counted ReachesIn.zero _ _

theorem step_B3_pre (k : ℕ) (tail : List ℕ) (d₀ : ℕ) (R_rest : List ℕ) :
    (cfg_F (0 :: B3 k tail) (d₀ :: R_rest)) [target_tm]⊢^{5*k+80}
    (cfg_F (0 :: tail) (9 :: (List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest)))) := by
  unfold B3
  refine countedPrepend (step_B_prefix ((3 * k + 3) :: 3 :: 0 :: tail) d₀ R_rest) (by omega) ?_
  refine countedPrepend ((rule_F_zero_zero ((3 * k + 3) :: 3 :: 0 :: tail) (9 :: 1 :: d₀ :: R_rest))) (by omega) ?_
  dsimp [bumpHead]
  have hk1 : 3 * k + 3 + 1 + 1 = 3 * (k + 1) + 2 := by omega
  rw [hk1]
  refine countedPrepend (rule_F_step3_all (3 :: 0 :: tail) (0 :: 9 :: 1 :: d₀ :: R_rest) 2 (k + 1)) (by omega) ?_
  rw [stepF3Right_succ k (0 :: 9 :: 1 :: d₀ :: R_rest)]
  dsimp [bumpHead]
  have h_rep : List.replicate k 1 ++ (1 :: 9 :: 1 :: d₀ :: R_rest) =
      List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest) := by
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]
  rw [h_rep]
  refine countedPrepend ((rule_F_two (3 :: 0 :: tail)
    (0 :: (List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest))))) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two_zero (0 :: tail)
    (1 :: (List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest))) 3)) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend ((rule_AR_add_two_zero (0 :: tail)
    (3 :: (List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest))) 1)) (by omega) ?_
  dsimp [bumpHead]
  exact_counted (rule_AR_one_zero (0 :: tail)
    (5 :: (List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest))))

theorem step_B3_post (k : ℕ) (tail' : List ℕ) (d₀ : ℕ) (R_rest : List ℕ) :
    (cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: tail') (0 :: (List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest))))
      [target_tm]⊢^{9*k+42}
    (cfg_AR (A0 (k + 1) tail') ((d₀ + 1) :: R_rest)) := by
  refine countedPrepend (rule_AR_zero_ones_all (k + 1) 0 (0 :: 0 :: 0 :: tail') (9 :: 1 :: d₀ :: R_rest)) (by omega) ?_
  rw [Nat.zero_add]
  refine countedPrepend ((rule_AR_zero_zero ((3 * (k + 1)) :: 0 :: 0 :: 0 :: tail') (9 :: 1 :: d₀ :: R_rest))) (by omega) ?_
  dsimp [bumpHead]
  refine countedPrepend (rule_AR_step2_all ((3 * (k + 1) + 3) :: 0 :: 0 :: 0 :: tail') (1 :: d₀ :: R_rest) 0 5) (by omega) ?_
  dsimp [List.replicate]
  refine countedPrepend (rule_AR_zero_ones_all 1 0 (0 :: 0 :: 0 :: (3 * (k + 1) + 3) :: 0 :: 0 :: 0 :: tail') (d₀ :: R_rest)) (by omega) ?_
  dsimp
  refine countedPrepend ((rule_AR_zero_zero
    (3 :: 0 :: 0 :: 0 :: (3 * (k + 1) + 3) :: 0 :: 0 :: 0 :: tail') (d₀ :: R_rest))) (by omega) ?_
  dsimp [bumpHead, A0]
  try exact_counted ReachesIn.zero _ _

theorem subStep_B0 (k : ℕ) (tail : List ℕ) : SubStep (14*k+132) (B0 k tail) (A3 (k + 1) tail) := by
  intro R_bot
  exact_counted ReachesIn.trans (step_B0_core k tail 9 R_bot) (exit_sub (A3 (k + 1) tail) R_bot)

theorem topStep_A0 (k : ℕ) (tail : List ℕ) : TopStep (14*k+216) (A0 k tail) (A3 (k + 1) tail) := by
  refine countedPrepend (top_A_to_B ((3 * k + 3) :: 0 :: 0 :: 0 :: tail)) (by omega) ?_
  exact_counted ReachesIn.trans (step_B0_core k tail 5 []) (exit_top (A3 (k + 1) tail))

theorem subStep_B3 (k : ℕ) {tail tail' : List ℕ} {c : ℕ} (h : SubStep c tail tail') :
    SubStep (c+14*k+132) (B3 k tail) (A0 (k + 1) tail') := by
  intro R_bot
  refine countedPrepend (step_B3_pre k tail 9 R_bot) (by omega) ?_
  refine countedPrepend (h (List.replicate (k + 1) 1 ++ (9 :: 1 :: 9 :: R_bot))) (by omega) ?_
  exact_counted ReachesIn.trans (step_B3_post k tail' 9 R_bot) (exit_sub (A0 (k + 1) tail') R_bot)

theorem topStep_A3 (k : ℕ) {tail tail' : List ℕ} {c : ℕ} (h : SubStep c tail tail') :
    TopStep (c+14*k+216) (A3 k tail) (A0 (k + 1) tail') := by
  refine countedPrepend (top_A_to_B ((3 * k + 3) :: 3 :: 0 :: tail)) (by omega) ?_
  refine countedPrepend (step_B3_pre k tail 5 []) (by omega) ?_
  refine countedPrepend (h (List.replicate (k + 1) 1 ++ [9, 1, 5])) (by omega) ?_
  exact_counted ReachesIn.trans (step_B3_post k tail' 5 []) (exit_top (A0 (k + 1) tail'))

theorem subHalt_B3 (k : ℕ) {tail : List ℕ} {c : ℕ} (h : SubHalt c tail) :
    SubHalt (c+5*k+80) (B3 k tail) := by
  intro R_bot
  obtain ⟨cfg, h_steps, h_none⟩ := h (List.replicate (k + 1) 1 ++ (9 :: 1 :: 9 :: R_bot))
  exact ⟨cfg, countedCast (ReachesIn.trans (step_B3_pre k tail 9 R_bot) h_steps) (by omega), h_none⟩

theorem topHalt_A3 (k : ℕ) {tail : List ℕ} {c : ℕ} (h : SubHalt c tail) :
    ∃ cfg, ((cfg_F (0 :: A3 k tail) [5]) [target_tm]⊢^{c+5*k+150} cfg) ∧ (step target_tm cfg).isNone := by
  obtain ⟨cfg, h_steps, h_none⟩ := h (List.replicate (k + 1) 1 ++ [9, 1, 5])
  refine ⟨cfg, ?_, h_none⟩
  refine countedPrepend (top_A_to_B ((3 * k + 3) :: 3 :: 0 :: tail)) (by omega) ?_
  exact_counted ReachesIn.trans (step_B3_pre k tail 5 []) h_steps

def countedAlgebra : F067Cost.Algebra (List ℕ) where
  A3 := A3
  A0 := A0
  B3 := B3
  B0 := B0
  Sub := SubStep
  Top := TopStep
  SubHalt := SubHalt
  TopHalt := fun c s => ∃ cfg, ((cfg_F (0 :: s) [5]) [target_tm]⊢^{c} cfg) ∧ (step target_tm cfg).isNone
  top_trans := by
    intro a b s t u h1 h2
    exact ReachesIn.trans h1 h2
  top_halt_trans := by
    intro a b s t h1 h2
    obtain ⟨cfg, hsteps, hnone⟩ := h2
    exact ⟨cfg, ReachesIn.trans h1 hsteps, hnone⟩
  subA3 := subStep_A3
  subA0 := subStep_A0
  subB0 := subStep_B0
  subB3 := subStep_B3
  topA0 := topStep_A0
  topA3 := topStep_A3
  sub_haltB3 := subHalt_B3
  top_haltA3 := topHalt_A3

#print axioms countedAlgebra
end
end BusyBeaver.F067Counted
