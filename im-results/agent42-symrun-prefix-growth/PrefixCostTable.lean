import PrefixGrowth

def stepElemMCost (bbRun0 exitRA : Nat) :
    SymMode × List MItem × List MItem → Nat
  | (.BB, [], _) => 1
  | (.BB, .zero :: _, _) => 1
  | (.BB, .run 0 :: _, _) => bbRun0
  | (.BB, .run 1 :: _, _) => 3
  | (.BB, .run 2 :: _, _) => 5
  | (.BB, .run 3 :: _, _) => 9
  | (.BB, .run (_d + 4) :: _, _) => 9
  | (.DL, .zero :: _, _) => 0
  | (.DL, .run 0 :: _, _) => 1
  | (.DL, .run 1 :: _, _) => 3
  | (.DL, .run 2 :: _, .run d0 :: _) => 3 * d0 + 9 + exitRA
  | (.CB, _, []) => 2
  | (.CB, _, .zero :: _) => 2
  | (.CB, _, .run 0 :: []) => 3
  | (.CB, _, .run 0 :: .zero :: _) => 3
  | (.CB, _, .run 0 :: .run 0 :: _) => 6
  | (.CB, _, .run 0 :: .run (d2 + 1) :: _) => 3 * d2 + 8 + exitRA
  | (.CB, _, .run 1 :: _) => 3
  | (.CB, _, .run 2 :: _) => 5
  | (.CB, _, .run (_d + 3) :: _) => 5
  | _ => 0

theorem maxRunState_runHead_left (mode : SymMode) (d : Nat) (L R : List MItem) :
    d ≤ maxRunState (mode, .run d :: L, R) := by
  unfold maxRunState
  exact Nat.le_trans (Nat.le_max_left d (maxRunList L))
    (Nat.le_max_left (maxRunList (.run d :: L)) (maxRunList R))

theorem maxRunState_runHead_right (mode : SymMode) (L : List MItem) (d : Nat) (R : List MItem) :
    d ≤ maxRunState (mode, L, .run d :: R) := by
  unfold maxRunState
  exact Nat.le_trans (Nat.le_max_left d (maxRunList R))
    (Nat.le_max_right (maxRunList L) (maxRunList (.run d :: R)))

theorem stepElemMCost_le (bbRun0 exitRA : Nat) (hbb : bbRun0 ≤ 8) (hexit : exitRA ≤ 13) :
    ∀ s, stepElemMCost bbRun0 exitRA s ≤ 3 * maxRunState s + 22 := by
  intro s
  rcases s with ⟨mode, L, R⟩
  cases mode with
  | BB =>
    cases L with
    | nil => simp [stepElemMCost, maxRunState, maxRunList]
    | cons t L1 =>
      cases t with
      | zero => simp [stepElemMCost, maxRunState, maxRunList]
      | run d =>
        cases d with
        | zero => simp [stepElemMCost, maxRunState, maxRunList]; omega
        | succ d =>
          cases d with
          | zero => simp [stepElemMCost, maxRunState, maxRunList]
          | succ d =>
            cases d with
            | zero => simp [stepElemMCost, maxRunState, maxRunList]
            | succ d =>
              cases d with
              | zero => simp [stepElemMCost, maxRunState, maxRunList]
              | succ d => simp [stepElemMCost, maxRunState, maxRunList]
  | DL =>
    cases L with
    | nil => simp [stepElemMCost, maxRunState, maxRunList]
    | cons t L1 =>
      cases t with
      | zero => simp [stepElemMCost, maxRunState, maxRunList]
      | run d =>
        cases d with
        | zero => simp [stepElemMCost, maxRunState, maxRunList]
        | succ d =>
          cases d with
          | zero => simp [stepElemMCost, maxRunState, maxRunList]
          | succ d =>
            cases d with
            | zero =>
              cases R with
              | nil => simp [stepElemMCost, maxRunState, maxRunList]
              | cons t R1 =>
                cases t with
                | zero => simp [stepElemMCost, maxRunState, maxRunList]
                | run d0 =>
                  simp only [stepElemMCost]
                  have hr := maxRunState_runHead_right SymMode.DL (.run 2 :: L1) d0 R1
                  simp only [Nat.reduceAdd] at hr ⊢
                  omega
            | succ d => simp [stepElemMCost, maxRunState, maxRunList]
  | CB =>
    cases R with
    | nil => simp [stepElemMCost, maxRunState, maxRunList]
    | cons t R1 =>
      cases t with
      | zero => simp [stepElemMCost, maxRunState, maxRunList]
      | run d =>
        cases d with
        | zero =>
          cases R1 with
          | nil => simp [stepElemMCost, maxRunState, maxRunList]
          | cons t2 R2 =>
            cases t2 with
            | zero => simp [stepElemMCost, maxRunState, maxRunList]
            | run d2 =>
              cases d2 with
              | zero => simp [stepElemMCost, maxRunState, maxRunList]
              | succ d2 =>
                simp only [stepElemMCost]
                have hr0 := maxRunState_runHead_right SymMode.CB L d2.succ R2
                have hr : d2.succ ≤ maxRunState (SymMode.CB, L, .run 0 :: .run d2.succ :: R2) := by
                  simpa [maxRunState, maxRunList] using hr0
                simp only [Nat.add_one] at hr ⊢
                omega
        | succ d =>
          cases d with
          | zero => simp [stepElemMCost, maxRunState, maxRunList]
          | succ d =>
            cases d with
            | zero => simp [stepElemMCost, maxRunState, maxRunList]
            | succ d => simp [stepElemMCost, maxRunState, maxRunList]
  | HALT => simp [stepElemMCost, maxRunState]

def iterStepCost
    (cost : (SymMode × List MItem × List MItem) → Nat)
    (f : (SymMode × List MItem × List MItem) → (SymMode × List MItem × List MItem)) :
    Nat → (SymMode × List MItem × List MItem) → Nat
  | 0, _ => 0
  | n + 1, s => cost s + iterStepCost cost f n (f s)

theorem iterStepCost_le
    (cost : (SymMode × List MItem × List MItem) → Nat)
    (f : (SymMode × List MItem × List MItem) → (SymMode × List MItem × List MItem))
    (hstep : ∀ s, maxRunState (f s) ≤ maxRunState s + 1)
    (hcost : ∀ s, cost s ≤ 3 * maxRunState s + 22) :
    ∀ n s, iterStepCost cost f n s ≤ n * (3 * (maxRunState s + n) + 22) := by
  intro n
  induction n with
  | zero => intro s; simp [iterStepCost]
  | succ n ih =>
    intro s
    simp only [iterStepCost]
    let C := 3 * (maxRunState s + (n + 1)) + 22
    have hcosts := hcost s
    have hsteps := hstep s
    have hfirst : cost s ≤ C := by dsimp [C]; omega
    have hmul : n * (3 * (maxRunState (f s) + n) + 22) ≤ n * C := by
      apply Nat.mul_le_mul_left
      dsimp [C]
      omega
    have htail : iterStepCost cost f n (f s) ≤ n * C := Nat.le_trans (ih (f s)) hmul
    calc
      cost s + iterStepCost cost f n (f s) ≤ C + n * C := Nat.add_le_add hfirst htail
      _ = n * C + C := by omega
      _ = (n + 1) * C := by rw [Nat.succ_mul]

theorem f424_prefix_cost_table_lt :
    iterStepCost (stepElemMCost 8 13) stepElemM 19217 f424PrefixStart + 19 < 2^31 := by
  have hcost : ∀ s, stepElemMCost 8 13 s ≤ 3 * maxRunState s + 22 :=
    stepElemMCost_le 8 13 (by omega) (by omega)
  have h := iterStepCost_le (stepElemMCost 8 13) stepElemM maxRunState_stepElemM hcost 19217 f424PrefixStart
  have hstart : maxRunState f424PrefixStart = 1 := by simp [f424PrefixStart, maxRunState, maxRunList]
  calc
    iterStepCost (stepElemMCost 8 13) stepElemM 19217 f424PrefixStart + 19
      ≤ 19217 * (3 * (1 + 19217) + 22) + 19 := by rw [hstart] at h; omega
    _ < 2^31 := by decide

theorem f412_prefix_cost_table_lt :
    iterStepCost (stepElemMCost 6 11) stepElemM 19255 f412PrefixStart + 2 < 2^31 := by
  have hcost : ∀ s, stepElemMCost 6 11 s ≤ 3 * maxRunState s + 22 :=
    stepElemMCost_le 6 11 (by omega) (by omega)
  have h := iterStepCost_le (stepElemMCost 6 11) stepElemM maxRunState_stepElemM hcost 19255 f412PrefixStart
  have hstart : maxRunState f412PrefixStart = 0 := by simp [f412PrefixStart, maxRunState, maxRunList]
  calc
    iterStepCost (stepElemMCost 6 11) stepElemM 19255 f412PrefixStart + 2
      ≤ 19255 * (3 * (0 + 19255) + 22) + 2 := by rw [hstart] at h; omega
    _ < 2^31 := by decide
