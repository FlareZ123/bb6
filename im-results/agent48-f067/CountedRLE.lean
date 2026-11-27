/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Exact-cost adaptation of the pinned source module by Agent 48.
-/
module
public import CountedAtoms

open Mathlib Relation Nat Turing BusyBeaver SixState
namespace BusyBeaver.F067Counted
@[expose] public section
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

def TowerA3 : List ℕ → List ℕ → List ℕ
  | [], S => S
  | k :: ks, S => TowerA3 ks (A3 k S)

def TowerA0Out : List ℕ → List ℕ → List ℕ
  | [], S => S
  | k :: ks, S => A0 k (TowerA0Out ks S)

def forceNat {α : Type} (e : ℕ) (f : ℕ → α) : α :=
  Nat.rec (f 0) (fun v _ => f v) (Nat.add e 1)

@[simp]
theorem forceNat_eq {α : Type} (e : ℕ) (f : ℕ → α) : forceNat e f = f e := rfl

def stepTowerAt (c : ℕ) : List ℕ → List ℕ
  | [] => []
  | k :: ks => forceNat (k + c) (fun kc => forceNat (4 * c) (fun c4 => kc :: stepTowerAt c4 ks))

theorem stepTowerAt_ne_nil (c : ℕ) {ks : List ℕ} (hks : ks ≠ []) :
    stepTowerAt c ks ≠ [] := by
  cases ks with
  | nil => contradiction
  | cons _ _ => simp [stepTowerAt]

theorem stepTowerAt_length (c : ℕ) (ks : List ℕ) :
    (stepTowerAt c ks).length = ks.length := by
  induction ks generalizing c with
  | nil => rfl
  | cons k ks ih => simp [stepTowerAt, ih (4 * c)]

theorem stepTowerAt_four (ks : List ℕ) (c : ℕ) :
    (stepTowerAt c)^[4] ks = stepTowerAt (4 * c) ks := by
  induction ks generalizing c with
  | nil => rfl
  | cons k ks ih =>
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, stepTowerAt, forceNat_eq]
    have hk : k + c + c + c + c = k + 4 * c := by omega
    rw [hk]
    congr 1
    exact ih (4 * c)



theorem tower_eq (ks : List ℕ) (S : List ℕ) :
    TowerA3 ks S = F067Cost.tower countedAlgebra ks S := by
  induction ks generalizing S with
  | nil => rfl
  | cons k ks ih => exact ih (A3 k S)

theorem shift_eq (c : ℕ) (ks : List ℕ) : stepTowerAt c ks = F067Cost.shift c ks := by
  induction ks generalizing c with
  | nil => rfl
  | cons k ks ih => simp only [stepTowerAt, forceNat_eq, F067Cost.shift, ih]

theorem towerStep {S S' : List ℕ} {c : ℕ} (ks : List ℕ) (hne : ks ≠ [])
    (hs : SubStep c S S') :
    TopStep (c+F067Cost.g ks) (TowerA3 ks S) (TowerA3 (stepTowerAt 2 ks) S') := by
  rw [tower_eq, tower_eq, shift_eq]
  exact F067Cost.tower_step countedAlgebra ks hne hs

theorem towerHalt {S : List ℕ} {c : ℕ} (ks : List ℕ) (hne : ks ≠ [])
    (hs : SubHalt c S) :
    ∃ cfg, ((cfg_F (0 :: TowerA3 ks S) [5]) [target_tm]⊢^{c+F067Cost.h ks} cfg) ∧
      (step target_tm cfg).isNone := by
  rw [tower_eq]
  exact F067Cost.tower_halt countedAlgebra ks hne hs

theorem TowerA3_append : ∀ (ks₁ ks₂ : List ℕ) (S : List ℕ),
    TowerA3 (ks₁ ++ ks₂) S = TowerA3 ks₂ (TowerA3 ks₁ S)
  | [], _, _ => rfl
  | k :: ks₁, ks₂, S => by
    simp only [List.cons_append, TowerA3]
    exact TowerA3_append ks₁ ks₂ (A3 k S)

-- ============================================================================
-- Section 4: Computable RLE Stack Simulator (`stepGenRLE` & `runSubSim`)
-- ============================================================================

abbrev RLEStack := List (ℕ × ℕ)

def evalRLE : RLEStack → List ℕ
  | [] => []
  | (v, c) :: s => List.replicate c v ++ evalRLE s

def tailFor (isOpen : Bool) (bot : List ℕ) : List ℕ :=
  if isOpen then bot else []

def evalRLEWith (isOpen : Bool) (s : RLEStack) (bot : List ℕ) : List ℕ :=
  evalRLE s ++ tailFor isOpen bot

@[simp]
theorem evalRLEWith_false (s : RLEStack) (bot : List ℕ) :
    evalRLEWith false s bot = evalRLE s := by
  simp [evalRLEWith, tailFor]

@[simp]
theorem evalRLEWith_true (s : RLEStack) (bot : List ℕ) :
    evalRLEWith true s bot = evalRLE s ++ bot := by
  simp [evalRLEWith, tailFor]

def pushRun (v c : ℕ) (s : RLEStack) : RLEStack :=
  if c = 0 then s
  else match s with
    | [] => forceNat v (fun v0 => forceNat c (fun c0 => [(v0, c0)]))
    | (v', c') :: rest =>
      if v = v' then forceNat (c + c') (fun cc => (v', cc) :: rest)
      else forceNat v (fun v0 => forceNat c (fun c0 => (v0, c0) :: (v', c') :: rest))

theorem evalRLE_pushRun (v c : ℕ) (s : RLEStack) :
    evalRLE (pushRun v c s) = List.replicate c v ++ evalRLE s := by
  unfold pushRun
  split_ifs with hc
  · subst hc; rfl
  · cases s with
    | nil => simp [evalRLE]
    | cons hd rest =>
      rcases hd with ⟨v', c'⟩
      dsimp
      split_ifs with hv
      · subst hv
        rw [evalRLE, evalRLE, List.replicate_add, List.append_assoc]
      · simp [evalRLE]

theorem evalRLEWith_pushRun (isOpen : Bool) (v c : ℕ) (s : RLEStack) (bot : List ℕ) :
    evalRLEWith isOpen (pushRun v c s) bot = List.replicate c v ++ evalRLEWith isOpen s bot := by
  simp [evalRLEWith, evalRLE_pushRun, List.append_assoc]

theorem evalRLEWith_pushOne (isOpen : Bool) (v : ℕ) (s : RLEStack) (bot : List ℕ) :
    evalRLEWith isOpen (pushRun v 1 s) bot = v :: evalRLEWith isOpen s bot := by
  simpa using evalRLEWith_pushRun isOpen v 1 s bot

def popOne : RLEStack → Option (ℕ × RLEStack)
  | [] => none
  | (_, 0) :: s => popOne s
  | (v, c + 1) :: s => some (v, if c = 0 then s else (v, c) :: s)

theorem evalRLE_popOne_some : ∀ {s s' : RLEStack} {v : ℕ},
    popOne s = some (v, s') → evalRLE s = v :: evalRLE s'
  | [], _, _, h => by simp [popOne] at h
  | (_, 0) :: s, s', v, h => by
    simp only [popOne, evalRLE, List.replicate_zero, List.nil_append] at h ⊢
    exact evalRLE_popOne_some h
  | (w, c + 1) :: s, s', v, h => by
    simp only [popOne, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    split_ifs with hc
    · subst hc; simp [evalRLE]
    · simp [evalRLE, List.replicate_succ]

theorem evalRLE_popOne_none : ∀ {s : RLEStack},
    popOne s = none → evalRLE s = []
  | [], _ => rfl
  | (_, 0) :: s, h => by
    simp only [popOne, evalRLE, List.replicate_zero, List.nil_append] at h ⊢
    exact evalRLE_popOne_none h
  | (_, _ + 1) :: _, h => by simp [popOne] at h

theorem evalRLEWith_popOne_some {isOpen : Bool} {s s' : RLEStack} {v : ℕ} (bot : List ℕ)
    (h : popOne s = some (v, s')) :
    evalRLEWith isOpen s bot = v :: evalRLEWith isOpen s' bot := by
  simp [evalRLEWith, evalRLE_popOne_some h]

theorem evalRLEWith_popOne_none_closed {s : RLEStack} (bot : List ℕ)
    (h : popOne s = none) :
    evalRLEWith false s bot = [] := by
  simp [evalRLEWith, tailFor, evalRLE_popOne_none h]

def bumpTopOpt (isOpen : Bool) (k : ℕ) (s : RLEStack) : Option RLEStack :=
  match k with
  | 0 => some s
  | m + 1 =>
    match popOne s with
    | some (v, s') => some (pushRun (v + (m + 1)) 1 s')
    | none => if isOpen then none else some (pushRun m 1 [])

theorem evalRLEWith_bumpTopOpt {isOpen : Bool} {k : ℕ} {s s' : RLEStack} (bot : List ℕ)
    (h : bumpTopOpt isOpen k s = some s') :
    evalRLEWith isOpen s' bot = bumpHead^[k] (evalRLEWith isOpen s bot) := by
  cases k with
  | zero =>
    simp only [bumpTopOpt, Option.some.injEq] at h
    subst h
    rfl
  | succ m =>
    simp only [bumpTopOpt] at h
    cases hpop : popOne s with
    | some vp =>
      rcases vp with ⟨v, s₁⟩
      rw [hpop] at h
      simp only [Option.some.injEq] at h
      subst h
      rw [evalRLEWith_pushOne, evalRLEWith_popOne_some bot hpop, bumpHead_iterate_cons]
    | none =>
      rw [hpop] at h
      cases isOpen with
      | true => simp at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        rw [evalRLEWith_pushOne, evalRLEWith_popOne_none_closed bot hpop,
            evalRLEWith, tailFor, evalRLE, bumpHead_iterate_nil]
        rfl

inductive GenStepResult where
  | stepped (cost : ℕ) (mode : StackMode) (L R : RLEStack)
  | halted
  | abort
  deriving DecidableEq, Repr

def tryFastF (L R : RLEStack) : Option (ℕ × RLEStack × RLEStack) :=
  match L with
  | [] => none
  | (v, c) :: L_rest =>
    match v with
    | 0 =>
      if 5 ≤ c then
        match popOne R with
        | none => none
        | some (r0, R₁) =>
          match r0 with
          | 0 =>
            match popOne R₁ with
            | none => none
            | some (d, R₂) =>
              let k := (c - 1) / 4
              let rem := (c - 1) % 4
              forceNat (rem + 1) (fun r1 =>
                some (72*k, (0, r1) :: L_rest, pushRun 0 1 (pushRun (d + 8 * k) 1 R₂)))
          | _ + 1 => none
      else none
    | _ + 1 => none

theorem tryFastF_sound {openL openR : Bool} {L R L' R' : RLEStack} (L_bot R_bot : List ℕ)
    (h : tryFastF L R = some (cost, L', R')) :
    (cfg_F (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢^{cost}
    (cfg_F (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot)) := by
  unfold tryFastF at h
  rcases L with _ | ⟨⟨_ | v, c⟩, L_rest⟩
  · simp at h
  · dsimp at h
    split_ifs at h with hc
    cases hR1 : popOne R with
    | none => rw [hR1] at h; simp at h
    | some vp1 =>
      rcases vp1 with ⟨r0, R₁⟩
      rw [hR1] at h
      cases r0 with
      | succ _ => simp at h
      | zero =>
        dsimp at h
        cases hR2 : popOne R₁ with
        | none => rw [hR2] at h; simp at h
        | some vp2 =>
          rcases vp2 with ⟨d, R₂⟩
          rw [hR2] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          have hL : evalRLEWith openL ((0, c) :: L_rest) L_bot =
              List.replicate (4 * ((c - 1) / 4) + ((c - 1) % 4) + 1) 0 ++
              evalRLEWith openL L_rest L_bot := by
            have h_eq : c = 4 * ((c - 1) / 4) + ((c - 1) % 4) + 1 := by omega
            simp [evalRLEWith, evalRLE, List.append_assoc, ← h_eq]
          have hL' : evalRLEWith openL ((0, (c - 1) % 4 + 1) :: L_rest) L_bot =
              List.replicate ((c - 1) % 4 + 1) 0 ++ evalRLEWith openL L_rest L_bot := by
            simp [evalRLEWith, evalRLE, List.append_assoc]
          have hR : evalRLEWith openR R R_bot = 0 :: d :: evalRLEWith openR R₂ R_bot := by
            rw [evalRLEWith_popOne_some R_bot hR1, evalRLEWith_popOne_some R_bot hR2]
          have hR' : evalRLEWith openR (pushRun 0 1 (pushRun (d + 8 * ((c - 1) / 4)) 1 R₂)) R_bot =
              0 :: (d + 8 * ((c - 1) / 4)) :: evalRLEWith openR R₂ R_bot := by
            rw [evalRLEWith_pushOne, evalRLEWith_pushOne]
          rw [hL, hL', hR, hR']
          exact rule_F_zero4_all ((c - 1) / 4) ((c - 1) % 4) (evalRLEWith openL L_rest L_bot)
            d (evalRLEWith openR R₂ R_bot)
  · simp at h

def tryFastAR_ones (fast1 : Bool) (L R : RLEStack) : Option (ℕ × RLEStack × RLEStack) :=
  if !fast1 then none
  else match R with
    | [] => none
    | (v, c) :: R_rest =>
      match v with
      | 0 => none
      | 1 =>
        if 2 ≤ c then
          match popOne L with
          | none => none
          | some (l0, L₁) =>
            match l0 with
            | 0 =>
              match popOne L₁ with
              | none => none
              | some (b, L₂) =>
                let m := c - 1
                some (23*m, pushRun 0 1 (pushRun (b + 3 * m) 1 L₂), (1, 1) :: R_rest)
            | _ + 1 => none
        else none
      | _ + 2 => none

theorem tryFastAR_ones_sound {openL openR fast1 : Bool} {L R L' R' : RLEStack}
    {cost : ℕ} (L_bot R_bot : List ℕ) (h : tryFastAR_ones fast1 L R = some (cost, L', R')) :
    (cfg_AR (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢^{cost}
    (cfg_AR (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot)) := by
  unfold tryFastAR_ones at h
  cases fast1
  · simp at h
  · rcases R with _ | ⟨⟨_ | _ | v, c⟩, R_rest⟩
    · simp at h
    · simp at h
    · dsimp at h
      split_ifs at h with hc
      cases hL1 : popOne L with
      | none => rw [hL1] at h; simp at h
      | some vp1 =>
        rcases vp1 with ⟨l0, L₁⟩
        rw [hL1] at h
        cases l0 with
        | succ _ => simp at h
        | zero =>
          dsimp at h
          cases hL2 : popOne L₁ with
          | none => rw [hL2] at h; simp at h
          | some vp2 =>
            rcases vp2 with ⟨b, L₂⟩
            rw [hL2] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl, rfl⟩
            have hL : evalRLEWith openL L L_bot = 0 :: b :: evalRLEWith openL L₂ L_bot := by
              rw [evalRLEWith_popOne_some L_bot hL1, evalRLEWith_popOne_some L_bot hL2]
            have hL' : evalRLEWith openL (pushRun 0 1 (pushRun (b + 3 * (c - 1)) 1 L₂)) L_bot =
                0 :: (b + 3 * (c - 1)) :: evalRLEWith openL L₂ L_bot := by
              rw [evalRLEWith_pushOne, evalRLEWith_pushOne]
            have hR : evalRLEWith openR ((1, c) :: R_rest) R_bot =
                List.replicate ((c - 1) + 1) 1 ++ evalRLEWith openR R_rest R_bot := by
              have hc_eq : c = (c - 1) + 1 := by omega
              simp [evalRLEWith, evalRLE, List.append_assoc, ← hc_eq]
            have hR' : evalRLEWith openR ((1, 1) :: R_rest) R_bot =
                1 :: evalRLEWith openR R_rest R_bot := by
              simp [evalRLEWith, evalRLE]
            rw [hL, hL', hR, hR']
            exact rule_AR_ones_all (c - 1) b (evalRLEWith openL L₂ L_bot)
              (evalRLEWith openR R_rest R_bot)
    · simp at h

def tryFastAR_zeroOnes (L R : RLEStack) : Option (ℕ × RLEStack × RLEStack) :=
  match R with
  | [] => none
  | (v1, c1) :: R_tail =>
    match R_tail with
    | [] => none
    | (v2, m) :: R_rest =>
      if v1 == 0 && c1 == 1 && v2 == 1 && 1 ≤ m then
        match popOne L with
        | none => none
        | some (l0, L₁) =>
          match l0 with
          | 0 =>
            match popOne L₁ with
            | none => none
            | some (b, L₂) =>
              some (9*m, pushRun 0 1 (pushRun (b + 3 * m) 1 L₂), pushRun 0 1 R_rest)
          | _ + 1 => none
      else none

theorem tryFastAR_zeroOnes_sound {openL openR : Bool} {L R L' R' : RLEStack}
    {cost : ℕ} (L_bot R_bot : List ℕ) (h : tryFastAR_zeroOnes L R = some (cost, L', R')) :
    (cfg_AR (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢^{cost}
    (cfg_AR (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot)) := by
  unfold tryFastAR_zeroOnes at h
  rcases R with _ | ⟨⟨v1, c1⟩, _ | ⟨⟨v2, m⟩, R_rest⟩⟩
  · simp at h
  · simp at h
  · dsimp at h
    split_ifs at h with hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    rcases hcond with ⟨⟨⟨rfl, rfl⟩, rfl⟩, hm⟩
    cases hL1 : popOne L with
    | none => rw [hL1] at h; simp at h
    | some vp1 =>
      rcases vp1 with ⟨l0, L₁⟩
      rw [hL1] at h
      cases l0 with
      | succ _ => simp at h
      | zero =>
        dsimp at h
        cases hL2 : popOne L₁ with
        | none => rw [hL2] at h; simp at h
        | some vp2 =>
          rcases vp2 with ⟨b, L₂⟩
          rw [hL2] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          have hL : evalRLEWith openL L L_bot = 0 :: b :: evalRLEWith openL L₂ L_bot := by
            rw [evalRLEWith_popOne_some L_bot hL1, evalRLEWith_popOne_some L_bot hL2]
          have hL' : evalRLEWith openL (pushRun 0 1 (pushRun (b + 3 * m) 1 L₂)) L_bot =
              0 :: (b + 3 * m) :: evalRLEWith openL L₂ L_bot := by
            rw [evalRLEWith_pushOne, evalRLEWith_pushOne]
          have hR : evalRLEWith openR ((0, 1) :: (1, m) :: R_rest) R_bot =
              0 :: (List.replicate m 1 ++ evalRLEWith openR R_rest R_bot) := by
            simp [evalRLEWith, evalRLE, List.append_assoc]
          have hR' : evalRLEWith openR (pushRun 0 1 R_rest) R_bot =
              0 :: evalRLEWith openR R_rest R_bot := by
            rw [evalRLEWith_pushOne]
          rw [hL, hL', hR, hR']
          exact rule_AR_zero_ones_all m b (evalRLEWith openL L₂ L_bot)
            (evalRLEWith openR R_rest R_bot)

def stepGenF_slow (openL openR : Bool) (L R : RLEStack) : GenStepResult :=
  match popOne L with
  | none =>
    if openL then .abort
    else .stepped 3 .AR (pushRun 1 1 []) R
  | some (a, L₁) =>
    match a with
    | 0 =>
      match popOne L₁ with
      | none =>
        if openL then .abort
        else match bumpTopOpt openR 1 R with
          | none => .abort
          | some R₁ => .stepped 3 .F [] (pushRun 0 1 R₁)
      | some (b, L₂) =>
        match b with
        | 0 =>
          match bumpTopOpt openL 2 L₂ with
          | none => .abort
          | some L₃ => .stepped 12 .F L₃ (pushRun 0 1 R)
        | 1 =>
          match bumpTopOpt openR 1 R with
          | none => .abort
          | some R₁ => .stepped 7 .F L₂ (pushRun 2 1 R₁)
        | b' + 2 =>
          match bumpTopOpt openR 1 R with
          | none => .abort
          | some R₁ => .stepped 4 .AR (pushRun b' 1 L₂) (pushRun 0 2 R₁)
    | 1 => .halted
    | 2 =>
      match bumpTopOpt openL 2 L₁ with
      | none => .abort
      | some L₂ =>
        match bumpTopOpt openR 1 R with
        | none => .abort
        | some R₁ => .stepped 8 .AR L₂ (pushRun 0 1 R₁)
    | a' + 3 =>
      match bumpTopOpt openR 1 R with
      | none => .abort
      | some R₁ =>
        .stepped (5 * (a' / 3 + 1)) .F (pushRun (a' % 3) 1 L₁)
          (pushRun 0 1 (pushRun 1 (a' / 3) R₁))

theorem stepGenF_slow_sound_step {openL openR : Bool} {L R L' R' : RLEStack} {mode' : StackMode}
    {cost : ℕ} (L_bot R_bot : List ℕ) (h : stepGenF_slow openL openR L R = .stepped cost mode' L' R') :
    (cfg_F (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢^{cost}
    (evalStackCfg mode' (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot)) := by
  unfold stepGenF_slow at h
  cases hpopL : popOne L with
  | none =>
    rw [hpopL] at h
    cases openL with
    | true => simp at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, GenStepResult.stepped.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      rw [evalStackCfg_AR, evalRLEWith_popOne_none_closed L_bot hpopL]
      have h1 : evalRLEWith false (pushRun 1 1 []) L_bot = [1] := by
        simp [evalRLEWith, tailFor, pushRun, evalRLE]
      rw [h1]
      exact (rule_F_nil (evalRLEWith openR R R_bot))
  | some vp =>
    rcases vp with ⟨a, L₁⟩
    rw [hpopL] at h
    have hL : evalRLEWith openL L L_bot = a :: evalRLEWith openL L₁ L_bot :=
      evalRLEWith_popOne_some L_bot hpopL
    rcases a with _ | _ | _ | a'
    · dsimp at h
      cases hpopL1 : popOne L₁ with
      | none =>
        rw [hpopL1] at h
        cases openL with
        | true => simp at h
        | false =>
          dsimp at h
          cases hR1 : bumpTopOpt openR 1 R with
          | none => rw [hR1] at h; simp at h
          | some R₁ =>
            rw [hR1] at h
            simp only [GenStepResult.stepped.injEq] at h
            rcases h with ⟨rfl, rfl, rfl, rfl⟩
            rw [evalStackCfg_F, hL, evalRLEWith_popOne_none_closed L_bot hpopL1,
                evalRLEWith_pushOne, evalRLEWith_bumpTopOpt R_bot hR1]
            simpa [evalRLEWith, tailFor, evalRLE] using
              (rule_F_zero_nil (evalRLEWith openR R R_bot))
      | some vp2 =>
        rcases vp2 with ⟨b, L₂⟩
        rw [hpopL1] at h
        have hL1 : evalRLEWith openL L₁ L_bot = b :: evalRLEWith openL L₂ L_bot :=
          evalRLEWith_popOne_some L_bot hpopL1
        rcases b with _ | _ | b'
        · dsimp at h
          cases hL2 : bumpTopOpt openL 2 L₂ with
          | none => rw [hL2] at h; simp at h
          | some L₃ =>
            rw [hL2] at h
            simp only [GenStepResult.stepped.injEq] at h
            rcases h with ⟨rfl, rfl, rfl, rfl⟩
            rw [evalStackCfg_F, hL, hL1, evalRLEWith_bumpTopOpt L_bot hL2, evalRLEWith_pushOne]
            exact (rule_F_zero_zero (evalRLEWith openL L₂ L_bot)
              (evalRLEWith openR R R_bot))
        · dsimp at h
          cases hR1 : bumpTopOpt openR 1 R with
          | none => rw [hR1] at h; simp at h
          | some R₁ =>
            rw [hR1] at h
            simp only [GenStepResult.stepped.injEq] at h
            rcases h with ⟨rfl, rfl, rfl, rfl⟩
            rw [evalStackCfg_F, hL, hL1, evalRLEWith_pushOne, evalRLEWith_bumpTopOpt R_bot hR1]
            exact (rule_F_zero_one (evalRLEWith openL L₂ L_bot)
              (evalRLEWith openR R R_bot))
        · dsimp at h
          cases hR1 : bumpTopOpt openR 1 R with
          | none => rw [hR1] at h; simp at h
          | some R₁ =>
            rw [hR1] at h
            simp only [GenStepResult.stepped.injEq] at h
            rcases h with ⟨rfl, rfl, rfl, rfl⟩
            rw [evalStackCfg_AR, hL, hL1, evalRLEWith_pushOne, evalRLEWith_pushRun,
                evalRLEWith_bumpTopOpt R_bot hR1]
            exact (rule_F_zero_add_two (evalRLEWith openL L₂ L_bot)
              (evalRLEWith openR R R_bot) b')
    · simp at h
    · dsimp at h
      cases hL2 : bumpTopOpt openL 2 L₁ with
      | none => rw [hL2] at h; simp at h
      | some L₂ =>
        rw [hL2] at h
        dsimp at h
        cases hR1 : bumpTopOpt openR 1 R with
        | none => rw [hR1] at h; simp at h
        | some R₁ =>
          rw [hR1] at h
          simp only [GenStepResult.stepped.injEq] at h
          rcases h with ⟨rfl, rfl, rfl, rfl⟩
          rw [evalStackCfg_AR, hL, evalRLEWith_bumpTopOpt L_bot hL2, evalRLEWith_pushOne,
              evalRLEWith_bumpTopOpt R_bot hR1]
          exact (rule_F_two (evalRLEWith openL L₁ L_bot)
            (evalRLEWith openR R R_bot))
    · dsimp at h
      cases hR1 : bumpTopOpt openR 1 R with
      | none => rw [hR1] at h; simp at h
      | some R₁ =>
        rw [hR1] at h
        simp only [GenStepResult.stepped.injEq] at h
        rcases h with ⟨rfl, rfl, rfl, rfl⟩
        have hL_eq : evalRLEWith openL L L_bot =
            (3 * (a' / 3 + 1) + (a' % 3)) :: evalRLEWith openL L₁ L_bot := by
          rw [hL]; congr 1; omega
        rw [evalStackCfg_F, hL_eq, evalRLEWith_pushOne, evalRLEWith_pushOne,
            evalRLEWith_pushRun, evalRLEWith_bumpTopOpt R_bot hR1]
        have h_step := rule_F_step3_all (evalRLEWith openL L₁ L_bot) (evalRLEWith openR R R_bot)
          (a' % 3) (a' / 3 + 1)
        rw [stepF3Right_succ] at h_step
        exact h_step

theorem stepGenF_slow_sound_halt {openL openR : Bool} {L R : RLEStack}
    (L_bot R_bot : List ℕ) (h : stepGenF_slow openL openR L R = .halted) :
    ∃ cfg, ((cfg_F (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢^{3} cfg) ∧
      (step target_tm cfg).isNone := by
  unfold stepGenF_slow at h
  cases hpopL : popOne L with
  | none =>
    rw [hpopL] at h
    cases openL <;> simp at h
  | some vp =>
    rcases vp with ⟨a, L₁⟩
    rw [hpopL] at h
    rcases a with _ | _ | _ | a'
    · dsimp at h
      cases hpopL1 : popOne L₁ with
      | none =>
        rw [hpopL1] at h
        cases openL with
        | true => simp at h
        | false =>
          dsimp at h
          cases hR1 : bumpTopOpt openR 1 R <;> simp [hR1] at h
      | some vp2 =>
        rcases vp2 with ⟨b, L₂⟩
        rw [hpopL1] at h
        rcases b with _ | _ | b'
        · dsimp at h; cases hL2 : bumpTopOpt openL 2 L₂ <;> simp [hL2] at h
        · dsimp at h; cases hR1 : bumpTopOpt openR 1 R <;> simp [hR1] at h
        · dsimp at h; cases hR1 : bumpTopOpt openR 1 R <;> simp [hR1] at h
    · rw [evalRLEWith_popOne_some L_bot hpopL]
      exact rule_F_one_halt (evalRLEWith openL L₁ L_bot) (evalRLEWith openR R R_bot)
    · dsimp at h
      cases hL2 : bumpTopOpt openL 2 L₁ with
      | none => rw [hL2] at h; simp at h
      | some L₂ =>
        rw [hL2] at h
        dsimp at h
        cases hR1 : bumpTopOpt openR 1 R <;> simp [hR1] at h
    · dsimp at h
      cases hR1 : bumpTopOpt openR 1 R <;> simp [hR1] at h

def stepGenAR_slow (openL openR : Bool) (L R : RLEStack) : GenStepResult :=
  match popOne R with
  | none =>
    if openR then .abort
    else .stepped 6 .F L (pushRun 1 1 [])
  | some (d, R₁) =>
    match d with
    | 0 =>
      match popOne L with
      | none =>
        if openL then .abort
        else match bumpTopOpt openR 2 R₁ with
          | none => .abort
          | some R₂ => .stepped 3 .F [] R₂
      | some (a, L₁) =>
        match a with
        | 0 =>
          match bumpTopOpt openL 3 L₁ with
          | none => .abort
          | some L₂ =>
            match bumpTopOpt openR 1 R₁ with
            | none => .abort
            | some R₂ => .stepped 7 .AR L₂ R₂
        | 1 =>
          match bumpTopOpt openR 4 R₁ with
          | none => .abort
          | some R₂ => .stepped 7 .F L₁ R₂
        | a' + 2 =>
          let k := (a' + 2) / 2
          match bumpTopOpt openR (2 * k) R₁ with
          | none => .abort
          | some R₂ => .stepped (4*k) .AR (pushRun ((a' + 2) % 2) 1 L₁) (pushRun 0 1 R₂)
    | 1 =>
      match popOne R₁ with
      | none =>
        if openR then .abort
        else .stepped 2 .AR (pushRun 0 1 L) []
      | some (e, R₂) =>
        .stepped 14 .AR L (pushRun 0 1 (pushRun (e + 1) 1 R₂))
    | d' + 2 =>
      let k := (d' + 2) / 2
      .stepped (2*k) .AR (pushRun 0 k L) (pushRun ((d' + 2) % 2) 1 R₁)

theorem stepGenAR_slow_sound_step {openL openR : Bool} {L R L' R' : RLEStack} {mode' : StackMode}
    {cost : ℕ} (L_bot R_bot : List ℕ) (h : stepGenAR_slow openL openR L R = .stepped cost mode' L' R') :
    (cfg_AR (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢^{cost}
    (evalStackCfg mode' (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot)) := by
  unfold stepGenAR_slow at h
  cases hpopR : popOne R with
  | none =>
    rw [hpopR] at h
    cases openR with
    | true => simp at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, GenStepResult.stepped.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      rw [evalStackCfg_F, evalRLEWith_popOne_none_closed R_bot hpopR]
      have h1 : evalRLEWith false (pushRun 1 1 []) R_bot = [1] := by
        simp [evalRLEWith, tailFor, pushRun, evalRLE]
      rw [h1]
      exact (rule_AR_nil (evalRLEWith openL L L_bot))
  | some vp =>
    rcases vp with ⟨d, R₁⟩
    rw [hpopR] at h
    have hR : evalRLEWith openR R R_bot = d :: evalRLEWith openR R₁ R_bot :=
      evalRLEWith_popOne_some R_bot hpopR
    rcases d with _ | _ | d'
    · dsimp at h
      cases hpopL : popOne L with
      | none =>
        rw [hpopL] at h
        cases openL with
        | true => simp at h
        | false =>
          dsimp at h
          cases hR2 : bumpTopOpt openR 2 R₁ with
          | none => rw [hR2] at h; simp at h
          | some R₂ =>
            rw [hR2] at h
            simp only [GenStepResult.stepped.injEq] at h
            rcases h with ⟨rfl, rfl, rfl, rfl⟩
            rw [evalStackCfg_F, hR, evalRLEWith_popOne_none_closed L_bot hpopL,
                evalRLEWith_bumpTopOpt R_bot hR2]
            simpa [evalRLEWith, tailFor, evalRLE] using
              (rule_AR_nil_zero (evalRLEWith openR R₁ R_bot))
      | some vpL =>
        rcases vpL with ⟨a, L₁⟩
        rw [hpopL] at h
        have hL : evalRLEWith openL L L_bot = a :: evalRLEWith openL L₁ L_bot :=
          evalRLEWith_popOne_some L_bot hpopL
        rcases a with _ | _ | a'
        · dsimp at h
          cases hL2 : bumpTopOpt openL 3 L₁ with
          | none => rw [hL2] at h; simp at h
          | some L₂ =>
            rw [hL2] at h
            dsimp at h
            cases hR2 : bumpTopOpt openR 1 R₁ with
            | none => rw [hR2] at h; simp at h
            | some R₂ =>
              rw [hR2] at h
              simp only [GenStepResult.stepped.injEq] at h
              rcases h with ⟨rfl, rfl, rfl, rfl⟩
              rw [evalStackCfg_AR, hL, hR, evalRLEWith_bumpTopOpt L_bot hL2,
                  evalRLEWith_bumpTopOpt R_bot hR2]
              exact (rule_AR_zero_zero (evalRLEWith openL L₁ L_bot)
                (evalRLEWith openR R₁ R_bot))
        · dsimp at h
          cases hR2 : bumpTopOpt openR 4 R₁ with
          | none => rw [hR2] at h; simp at h
          | some R₂ =>
            rw [hR2] at h
            simp only [GenStepResult.stepped.injEq] at h
            rcases h with ⟨rfl, rfl, rfl, rfl⟩
            rw [evalStackCfg_F, hL, hR, evalRLEWith_bumpTopOpt R_bot hR2]
            exact (rule_AR_one_zero (evalRLEWith openL L₁ L_bot)
              (evalRLEWith openR R₁ R_bot))
        · dsimp at h
          cases hR2 : bumpTopOpt openR (2 * ((a' + 2) / 2)) R₁ with
          | none => rw [hR2] at h; simp at h
          | some R₂ =>
            rw [hR2] at h
            simp only [GenStepResult.stepped.injEq] at h
            rcases h with ⟨rfl, rfl, rfl, rfl⟩
            have hL_eq : evalRLEWith openL L L_bot =
                (2 * ((a' + 2) / 2) + ((a' + 2) % 2)) :: evalRLEWith openL L₁ L_bot := by
              rw [hL]; congr 1; omega
            rw [evalStackCfg_AR, hL_eq, hR, evalRLEWith_pushOne, evalRLEWith_pushOne,
                evalRLEWith_bumpTopOpt R_bot hR2, ← bumpHead2_iterate_eq]
            exact rule_AR_add_two_zero_all (evalRLEWith openL L₁ L_bot)
              (evalRLEWith openR R₁ R_bot) ((a' + 2) % 2) ((a' + 2) / 2)
    · dsimp at h
      cases hpopR1 : popOne R₁ with
      | none =>
        rw [hpopR1] at h
        cases openR with
        | true => simp at h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, GenStepResult.stepped.injEq] at h
          rcases h with ⟨rfl, rfl, rfl, rfl⟩
          rw [evalStackCfg_AR, hR, evalRLEWith_popOne_none_closed R_bot hpopR1,
              evalRLEWith_pushOne]
          simpa [evalRLEWith, tailFor, evalRLE] using
            (rule_AR_one_nil (evalRLEWith openL L L_bot))
      | some vpR2 =>
        rcases vpR2 with ⟨e, R₂⟩
        rw [hpopR1] at h
        dsimp at h
        simp only [GenStepResult.stepped.injEq] at h
        rcases h with ⟨rfl, rfl, rfl, rfl⟩
        rw [evalStackCfg_AR, hR, evalRLEWith_popOne_some R_bot hpopR1,
            evalRLEWith_pushOne, evalRLEWith_pushOne]
        exact (rule_AR_one_cons (evalRLEWith openL L L_bot)
          (evalRLEWith openR R₂ R_bot) e)
    · dsimp at h
      simp only [GenStepResult.stepped.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      have hR_eq : evalRLEWith openR R R_bot =
          (2 * ((d' + 2) / 2) + ((d' + 2) % 2)) :: evalRLEWith openR R₁ R_bot := by
        rw [hR]; congr 1; omega
      rw [evalStackCfg_AR, hR_eq, evalRLEWith_pushRun, evalRLEWith_pushOne]
      exact rule_AR_step2_all (evalRLEWith openL L L_bot) (evalRLEWith openR R₁ R_bot)
        ((d' + 2) % 2) ((d' + 2) / 2)

theorem stepGenAR_slow_not_halt (openL openR : Bool) (L R : RLEStack) :
    stepGenAR_slow openL openR L R ≠ .halted := by
  unfold stepGenAR_slow
  cases popOne R with
  | none => cases openR <;> simp
  | some vp =>
    rcases vp with ⟨d, R₁⟩
    rcases d with _ | _ | d'
    · dsimp
      cases popOne L with
      | none =>
        cases openL with
        | true => simp
        | false => dsimp; cases bumpTopOpt openR 2 R₁ <;> simp
      | some vpL =>
        rcases vpL with ⟨a, L₁⟩
        rcases a with _ | _ | a'
        · dsimp
          cases bumpTopOpt openL 3 L₁ with
          | none => simp
          | some _ => dsimp; cases bumpTopOpt openR 1 R₁ <;> simp
        · dsimp; cases bumpTopOpt openR 4 R₁ <;> simp
        · dsimp; cases bumpTopOpt openR (2 * ((a' + 2) / 2)) R₁ <;> simp
    · dsimp
      cases popOne R₁ with
      | none => cases openR <;> simp
      | some vp2 => rcases vp2 with ⟨_, _⟩; simp
    · simp

def stepGenRLE (openL openR fast1 : Bool) (mode : StackMode) (L R : RLEStack) : GenStepResult :=
  match mode with
  | .F =>
    match tryFastF L R with
    | some (cost, L', R') => .stepped cost .F L' R'
    | none => stepGenF_slow openL openR L R
  | .AR =>
    match tryFastAR_ones fast1 L R with
    | some (cost, L', R') => .stepped cost .AR L' R'
    | none =>
      match tryFastAR_zeroOnes L R with
      | some (cost, L', R') => .stepped cost .AR L' R'
      | none => stepGenAR_slow openL openR L R

theorem stepGenRLE_sound_step {openL openR fast1 : Bool} {mode mode' : StackMode}
    {L R L' R' : RLEStack} {cost : ℕ} (L_bot R_bot : List ℕ)
    (h : stepGenRLE openL openR fast1 mode L R = .stepped cost mode' L' R') :
    (evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢^{cost}
    (evalStackCfg mode' (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot)) := by
  unfold stepGenRLE at h
  cases mode with
  | F =>
    cases hfast : tryFastF L R with
    | some vp =>
      rcases vp with ⟨cf, Lf, Rf⟩
      rw [hfast] at h
      simp only [GenStepResult.stepped.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      exact tryFastF_sound L_bot R_bot hfast
    | none =>
      rw [hfast] at h
      exact stepGenF_slow_sound_step L_bot R_bot h
  | AR =>
    cases hfast1 : tryFastAR_ones fast1 L R with
    | some vp =>
      rcases vp with ⟨cf, Lf, Rf⟩
      rw [hfast1] at h
      simp only [GenStepResult.stepped.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      exact tryFastAR_ones_sound L_bot R_bot hfast1
    | none =>
      rw [hfast1] at h
      cases hfast2 : tryFastAR_zeroOnes L R with
      | some vp =>
        rcases vp with ⟨cf, Lf, Rf⟩
        rw [hfast2] at h
        simp only [GenStepResult.stepped.injEq] at h
        rcases h with ⟨rfl, rfl, rfl, rfl⟩
        exact tryFastAR_zeroOnes_sound L_bot R_bot hfast2
      | none =>
        rw [hfast2] at h
        exact stepGenAR_slow_sound_step L_bot R_bot h

theorem stepGenRLE_sound_halt {openL openR fast1 : Bool} {mode : StackMode} {L R : RLEStack}
    (L_bot R_bot : List ℕ) (h : stepGenRLE openL openR fast1 mode L R = .halted) :
    ∃ cfg, ((evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢^{3} cfg) ∧
      (step target_tm cfg).isNone := by
  unfold stepGenRLE at h
  cases mode with
  | F =>
    cases hfast : tryFastF L R with
    | some vp =>
      rcases vp with ⟨_, _, _⟩
      rw [hfast] at h
      simp at h
    | none =>
      rw [hfast] at h
      exact stepGenF_slow_sound_halt L_bot R_bot h
  | AR =>
    cases hfast1 : tryFastAR_ones fast1 L R with
    | some vp =>
      rcases vp with ⟨_, _, _⟩
      rw [hfast1] at h
      simp at h
    | none =>
      rw [hfast1] at h
      cases hfast2 : tryFastAR_zeroOnes L R with
      | some vp =>
        rcases vp with ⟨_, _, _⟩
        rw [hfast2] at h
        simp at h
      | none =>
        rw [hfast2] at h
        exact absurd h (stepGenAR_slow_not_halt openL openR L R)

def addGenCost (c : ℕ) : GenStepResult → GenStepResult
  | .stepped d m l r => .stepped (c+d) m l r
  | .halted => .halted
  | .abort => .abort

def runStepsRLE : ℕ → Bool → Bool → Bool → StackMode → RLEStack → RLEStack → GenStepResult
  | 0, _, _, _, mode, L, R => .stepped 0 mode L R
  | n + 1, openL, openR, fast1, mode, L, R =>
    match stepGenRLE openL openR fast1 mode L R with
    | .stepped cost mode₁ L₁ R₁ => addGenCost cost (runStepsRLE n openL openR fast1 mode₁ L₁ R₁)
    | .halted => .halted
    | .abort => .abort

theorem runStepsRLE_sound_step : ∀ {n : ℕ} {openL openR fast1 : Bool} {mode mode' : StackMode}
    {L R L' R' : RLEStack} {cost : ℕ} (L_bot R_bot : List ℕ),
    runStepsRLE n openL openR fast1 mode L R = .stepped cost mode' L' R' →
    (evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢^{cost}
    (evalStackCfg mode' (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot))
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, h => by
    simp only [runStepsRLE, GenStepResult.stepped.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    exact ReachesIn.zero _ _
  | n + 1, openL, openR, fast1, mode, mode', L, R, L', R', cost, L_bot, R_bot, h => by
    unfold runStepsRLE at h
    cases hstep : stepGenRLE openL openR fast1 mode L R with
    | stepped d mode₁ L₁ R₁ =>
      rw [hstep] at h
      cases hrest : runStepsRLE n openL openR fast1 mode₁ L₁ R₁ with
      | stepped e mode₂ L₂ R₂ =>
        rw [hrest] at h
        simp only [addGenCost, GenStepResult.stepped.injEq] at h
        rcases h with ⟨rfl, rfl, rfl, rfl⟩
        exact ReachesIn.trans (stepGenRLE_sound_step L_bot R_bot hstep)
          (runStepsRLE_sound_step L_bot R_bot hrest)
      | halted => rw [hrest] at h; simp [addGenCost] at h
      | abort => rw [hrest] at h; simp [addGenCost] at h
    | halted => rw [hstep] at h; simp at h
    | abort => rw [hstep] at h; simp at h

def peelZeros : ℕ → RLEStack → Option RLEStack
  | 0, s => some s
  | n + 1, s =>
    match popOne s with
    | none => none
    | some (v, s') =>
      match v with
      | 0 => peelZeros n s'
      | _ + 1 => none

theorem evalRLE_peelZeros : ∀ {n : ℕ} {s s' : RLEStack},
    peelZeros n s = some s' → evalRLE s = List.replicate n 0 ++ evalRLE s'
  | 0, _, _, h => by
    simp only [peelZeros, Option.some.injEq] at h
    subst h
    rfl
  | n + 1, s, s', h => by
    unfold peelZeros at h
    cases hpop : popOne s with
    | none => rw [hpop] at h; simp at h
    | some vp =>
      rcases vp with ⟨v, s₁⟩
      rw [hpop] at h
      cases v with
      | succ _ => simp at h
      | zero =>
        dsimp at h
        rw [evalRLE_popOne_some hpop, evalRLE_peelZeros h]
        rfl

theorem evalRLEWith_peelZeros {isOpen : Bool} {n : ℕ} {s s' : RLEStack} (bot : List ℕ)
    (h : peelZeros n s = some s') :
    evalRLEWith isOpen s bot = List.replicate n 0 ++ evalRLEWith isOpen s' bot := by
  simp [evalRLEWith, evalRLE_peelZeros h, List.append_assoc]

def isSingleVal (v : ℕ) (s : RLEStack) : Bool :=
  match popOne s with
  | some (w, s') => (w == v) && (popOne s').isNone
  | none => false

theorem evalRLEWith_isSingleVal {v : ℕ} {s : RLEStack} (bot : List ℕ)
    (h : isSingleVal v s = true) :
    evalRLEWith true s bot = v :: bot := by
  unfold isSingleVal at h
  cases hpop1 : popOne s with
  | none => rw [hpop1] at h; simp at h
  | some vp =>
    rcases vp with ⟨w, s'⟩
    rw [hpop1] at h
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
    rcases h with ⟨rfl, hpop2⟩
    simp [evalRLEWith, tailFor, evalRLE_popOne_some hpop1, evalRLE_popOne_none hpop2]

theorem evalRLE_isSingleVal {v : ℕ} {s : RLEStack} (h : isSingleVal v s = true) :
    evalRLE s = [v] := by
  have h1 := evalRLEWith_isSingleVal [] h
  simpa [evalRLEWith, tailFor] using h1

inductive SubSimResult where
  | stepped (cost : ℕ) (S' : RLEStack)
  | halted (cost : ℕ)
  | abort
  deriving DecidableEq, Repr

def addSubCost (c : ℕ) : SubSimResult → SubSimResult
  | .stepped d s => .stepped (c+d) s
  | .halted d => .halted (c+d)
  | .abort => .abort

def runSubLoop : ℕ → Bool → Bool → StackMode → RLEStack → RLEStack → SubSimResult
  | 0, _, _, _, _, _ => .abort
  | fuel + 1, openL, fast1, mode, L, R =>
    if mode == .AR && isSingleVal 0 R then
      match peelZeros 5 L with
      | some S' => .stepped 0 S'
      | none => .abort
    else
      match stepGenRLE openL true fast1 mode L R with
      | .stepped d mode' L' R' => addSubCost d (runSubLoop fuel openL fast1 mode' L' R')
      | .halted => .halted 3
      | .abort => .abort

def runSubSim (fuel : ℕ) (openL fast1 : Bool) (S : RLEStack) : SubSimResult :=
  runSubLoop fuel openL fast1 .F (pushRun 0 1 S) [(9, 1)]

theorem runSubLoop_sound_step : ∀ {fuel : ℕ} {openL fast1 : Bool} {mode : StackMode}
    {L R S' : RLEStack} {cost : ℕ} (L_bot R_bot : List ℕ),
    runSubLoop fuel openL fast1 mode L R = .stepped cost S' →
    (evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith true R R_bot)) [target_tm]⊢^{cost}
    (cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: evalRLEWith openL S' L_bot) (0 :: R_bot))
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [runSubLoop] at h
  | fuel + 1, openL, fast1, mode, L, R, S', cost, L_bot, R_bot, h => by
    unfold runSubLoop at h
    split_ifs at h with hexit
    · simp only [Bool.and_eq_true, beq_iff_eq] at hexit
      rcases hexit with ⟨rfl, hR0⟩
      cases hpeel : peelZeros 5 L with
      | none => rw [hpeel] at h; simp at h
      | some S_out =>
        rw [hpeel] at h
        simp only [SubSimResult.stepped.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        rw [evalRLEWith_isSingleVal R_bot hR0, evalRLEWith_peelZeros L_bot hpeel]
        exact ReachesIn.zero _ _
    · cases hstep : stepGenRLE openL true fast1 mode L R with
      | stepped d mode' L' R' =>
        rw [hstep] at h
        cases hrest : runSubLoop fuel openL fast1 mode' L' R' with
        | stepped e S_out =>
          rw [hrest] at h
          simp only [addSubCost, SubSimResult.stepped.injEq] at h
          rcases h with ⟨rfl,rfl⟩
          exact ReachesIn.trans (stepGenRLE_sound_step L_bot R_bot hstep)
            (runSubLoop_sound_step L_bot R_bot hrest)
        | halted => rw [hrest] at h; simp [addSubCost] at h
        | abort => rw [hrest] at h; simp [addSubCost] at h
      | halted => rw [hstep] at h; simp at h
      | abort => rw [hstep] at h; simp at h

theorem runSubLoop_sound_halt : ∀ {fuel : ℕ} {openL fast1 : Bool} {mode : StackMode}
    {L R : RLEStack} {cost : ℕ} (L_bot R_bot : List ℕ),
    runSubLoop fuel openL fast1 mode L R = .halted cost →
    ∃ cfg, ((evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith true R R_bot)) [target_tm]⊢^{cost} cfg) ∧
      (step target_tm cfg).isNone
  | 0, _, _, _, _, _, _, _, _, h => by simp [runSubLoop] at h
  | fuel + 1, openL, fast1, mode, L, R, cost, L_bot, R_bot, h => by
    unfold runSubLoop at h
    split_ifs at h with hexit
    · cases hpeel : peelZeros 5 L <;> simp [hpeel] at h
    · cases hstep : stepGenRLE openL true fast1 mode L R with
      | stepped d mode' L' R' =>
        rw [hstep] at h
        cases hrest : runSubLoop fuel openL fast1 mode' L' R' with
        | stepped => rw [hrest] at h; simp [addSubCost] at h
        | halted e =>
          rw [hrest] at h
          simp only [addSubCost, SubSimResult.halted.injEq] at h
          subst cost
          obtain ⟨cfg, h_rest, h_none⟩ := runSubLoop_sound_halt L_bot R_bot hrest
          exact ⟨cfg, ReachesIn.trans (stepGenRLE_sound_step L_bot R_bot hstep) h_rest, h_none⟩
        | abort => rw [hrest] at h; simp [addSubCost] at h
      | halted =>
        rw [hstep] at h
        simp only [SubSimResult.halted.injEq] at h
        subst cost
        exact stepGenRLE_sound_halt L_bot R_bot hstep
      | abort => rw [hstep] at h; simp at h

theorem runSubSim_sound_closed {fuel : ℕ} {fast1 : Bool} {S S' : RLEStack} {cost : ℕ}
    (h : runSubSim fuel false fast1 S = .stepped cost S') :
    SubStep cost (evalRLE S) (evalRLE S') := by
  intro R_bot
  have h1 := runSubLoop_sound_step [] R_bot h
  simpa [evalRLEWith, tailFor, evalRLE_pushRun, evalRLE] using h1

theorem runSubSim_sound_open {fuel : ℕ} {fast1 : Bool} {S S' : RLEStack} {cost : ℕ} (U : List ℕ)
    (h : runSubSim fuel true fast1 S = .stepped cost S') :
    SubStep cost (evalRLE S ++ U) (evalRLE S' ++ U) := by
  intro R_bot
  have h1 := runSubLoop_sound_step U R_bot h
  simpa [evalRLEWith, tailFor, evalRLE_pushRun, evalRLE] using h1

theorem runSubSim_sound_halt {fuel : ℕ} {fast1 : Bool} {S : RLEStack} {cost : ℕ}
    (h : runSubSim fuel false fast1 S = .halted cost) :
    SubHalt cost (evalRLE S) := by
  intro R_bot
  have h1 := runSubLoop_sound_halt [] R_bot h
  simpa [evalRLEWith, tailFor, evalRLE_pushRun, evalRLE] using h1

def peelOneA3 (s : RLEStack) : Option (ℕ × RLEStack) :=
  match popOne s with
  | none => none
  | some (v6, s₁) =>
    if v6 == 6 then
      match peelZeros 3 s₁ with
      | none => none
      | some s₂ =>
        match popOne s₂ with
        | none => none
        | some (x, s₃) =>
          if 3 ≤ x && x % 3 == 0 then
            match popOne s₃ with
            | none => none
            | some (v3, s₄) =>
              if v3 == 3 then
                match popOne s₄ with
                | none => none
                | some (v0, s₅) =>
                  if v0 == 0 then forceNat (x / 3 - 1) (fun k' => some (k', s₅))
                  else none
              else none
          else none
    else none

theorem evalRLE_peelOneA3 {s s' : RLEStack} {k : ℕ} (h : peelOneA3 s = some (k, s')) :
    evalRLE s = A3 k (evalRLE s') := by
  unfold peelOneA3 at h
  cases hp1 : popOne s with
  | none => rw [hp1] at h; simp at h
  | some vp1 =>
    rcases vp1 with ⟨v6, s₁⟩
    rw [hp1] at h
    dsimp at h
    split_ifs at h with hv6
    rw [beq_iff_eq] at hv6
    subst hv6
    cases hpz : peelZeros 3 s₁ with
    | none => rw [hpz] at h; simp at h
    | some s₂ =>
      rw [hpz] at h
      dsimp at h
      cases hp2 : popOne s₂ with
      | none => rw [hp2] at h; simp at h
      | some vp2 =>
        rcases vp2 with ⟨x, s₃⟩
        rw [hp2] at h
        dsimp at h
        split_ifs at h with hx
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx
        cases hp3 : popOne s₃ with
        | none => rw [hp3] at h; simp at h
        | some vp3 =>
          rcases vp3 with ⟨v3, s₄⟩
          rw [hp3] at h
          dsimp at h
          split_ifs at h with hv3
          rw [beq_iff_eq] at hv3
          subst hv3
          cases hp4 : popOne s₄ with
          | none => rw [hp4] at h; simp at h
          | some vp4 =>
            rcases vp4 with ⟨v0, s₅⟩
            rw [hp4] at h
            dsimp at h
            split_ifs at h with hv0
            rw [beq_iff_eq] at hv0
            subst hv0
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            have hx_eq : x = 3 * (x / 3 - 1) + 3 := by omega
            rw [evalRLE_popOne_some hp1, evalRLE_peelZeros hpz, evalRLE_popOne_some hp2,
                evalRLE_popOne_some hp3, evalRLE_popOne_some hp4]
            simp [A3, ← hx_eq]

def peelA3Loop : ℕ → List ℕ → RLEStack → List ℕ × RLEStack
  | 0, acc, s => (acc, s)
  | fuel + 1, acc, s =>
    match peelOneA3 s with
    | some (k, s') => peelA3Loop fuel (k :: acc) s'
    | none => (acc, s)

theorem evalRLE_peelA3Loop : ∀ (fuel : ℕ) (acc : List ℕ) (s : RLEStack),
    TowerA3 (peelA3Loop fuel acc s).1 (evalRLE (peelA3Loop fuel acc s).2) =
    TowerA3 acc (evalRLE s)
  | 0, _, _ => rfl
  | fuel + 1, acc, s => by
    unfold peelA3Loop
    cases h : peelOneA3 s with
    | none => rfl
    | some vp =>
      rcases vp with ⟨k, s'⟩
      rw [evalRLE_peelA3Loop fuel (k :: acc) s', TowerA3, evalRLE_peelOneA3 h]

def wrapOneA3RLE (k : ℕ) (s : RLEStack) : RLEStack :=
  pushRun 6 1 (pushRun 0 3 (pushRun (3 * k + 3) 1 (pushRun 3 1 (pushRun 0 1 s))))

def wrapTowerA3RLE : List ℕ → RLEStack → RLEStack
  | [], s => s
  | k :: ks, s => wrapTowerA3RLE ks (wrapOneA3RLE k s)

theorem evalRLE_wrapOneA3RLE (k : ℕ) (s : RLEStack) :
    evalRLE (wrapOneA3RLE k s) = A3 k (evalRLE s) := by
  simp [wrapOneA3RLE, evalRLE_pushRun, A3]

theorem evalRLE_wrapTowerA3RLE : ∀ (ks : List ℕ) (s : RLEStack),
    evalRLE (wrapTowerA3RLE ks s) = TowerA3 ks (evalRLE s)
  | [], _ => rfl
  | k :: ks, s => by
    simp only [wrapTowerA3RLE, TowerA3, evalRLE_wrapTowerA3RLE ks, evalRLE_wrapOneA3RLE]

def wrapOneA0RLE (k : ℕ) (s : RLEStack) : RLEStack :=
  pushRun 6 1 (pushRun 0 3 (pushRun (3 * k + 3) 1 (pushRun 0 3 s)))

def wrapTowerA0OutRLE : List ℕ → RLEStack → RLEStack
  | [], s => s
  | k :: ks, s => wrapOneA0RLE k (wrapTowerA0OutRLE ks s)

theorem evalRLE_wrapOneA0RLE (k : ℕ) (s : RLEStack) :
    evalRLE (wrapOneA0RLE k s) = A0 k (evalRLE s) := by
  simp [wrapOneA0RLE, evalRLE_pushRun, A0]

theorem evalRLE_wrapTowerA0OutRLE : ∀ (ks : List ℕ) (s : RLEStack),
    evalRLE (wrapTowerA0OutRLE ks s) = TowerA0Out ks (evalRLE s)
  | [], _ => rfl
  | k :: ks, s => by
    simp only [wrapTowerA0OutRLE, TowerA0Out, evalRLE_wrapOneA0RLE, evalRLE_wrapTowerA0OutRLE ks]

-- ============================================================================
-- Section 5: Three-Phase Halting Trajectory (`init [] -> HALT`)
-- ============================================================================

theorem evalRLE_append : ∀ (s₁ s₂ : RLEStack),
    evalRLE (s₁ ++ s₂) = evalRLE s₁ ++ evalRLE s₂
  | [], _ => rfl
  | (v, c) :: s₁, s₂ => by simp [evalRLE, evalRLE_append s₁ s₂, List.append_assoc]


#print axioms runSubSim_sound_closed
#print axioms runSubSim_sound_open
#print axioms runSubSim_sound_halt
end
end BusyBeaver.F067Counted
