import Lean

inductive MItem where
  | zero : MItem
  | run (d : Nat) : MItem
  deriving DecidableEq, Repr

inductive SymMode where
  | BB | DL | CB | HALT
  deriving DecidableEq, Repr

def strictNat {α : Type} (n : Nat) (f : Nat → α) : α :=
  @Nat.rec (fun _ => α) (f 0) (fun k _ => f k) (Nat.add n 1)

@[simp] theorem strictNat_eq {α : Type} (n : Nat) (f : Nat → α) : strictNat n f = f n := rfl

def strictMList {α : Type} (xs : List MItem) (f : List MItem → α) : α :=
  match xs with
  | [] => f []
  | h :: t => f (h :: t)

@[simp] theorem strictMList_eq {α : Type} (xs : List MItem) (f : List MItem → α) : strictMList xs f = f xs := by
  cases xs <;> rfl

def bumpM : List MItem → List MItem
  | [] => [.run 0]
  | .zero :: M => .run 0 :: M
  | .run d :: M => strictNat (d + 1) (fun d' => .run d' :: M)

def prependZeroM : Nat → List MItem → List MItem
  | 0, acc => acc
  | n + 1, acc => prependZeroM n (.zero :: acc)

def stepElemM : SymMode × List MItem × List MItem → SymMode × List MItem × List MItem
  | (.BB, [], R) => strictMList (bumpM R) (fun R' => (.CB, [], R'))
  | (.BB, .zero :: L1, R) => strictMList (bumpM R) (fun R' => (.CB, L1, R'))
  | (.BB, .run 0 :: L1, R) => (.BB, L1, .run 0 :: R)
  | (.BB, .run 1 :: L1, R) => strictMList (bumpM R) (fun R' => (.BB, L1, .run 0 :: R'))
  | (.BB, .run 2 :: L1, R) => strictMList (bumpM R) (fun R' => (.DL, L1, .run 0 :: .run 0 :: R'))
  | (.BB, .run 3 :: L1, R) => strictMList (bumpM R) (fun R' => (.BB, .run 0 :: .zero :: .zero :: L1, R'))
  | (.BB, .run (d + 4) :: L1, R) =>
      strictNat d (fun d' => strictMList (bumpM R) (fun R' => (.BB, .run 0 :: .zero :: .run d' :: L1, R')))
  | (.DL, .zero :: L1, R) => (.HALT, .zero :: L1, R)
  | (.DL, .run 0 :: L1, R) => strictMList (bumpM R) (fun R' => (.BB, L1, R'))
  | (.DL, .run 1 :: L1, R) => strictMList (bumpM R) (fun R' => (.DL, L1, .run 0 :: R'))
  | (.DL, .run 2 :: L1, .run d0 :: R1) =>
      strictMList (prependZeroM (d0 + 1) L1) (fun L' => (.CB, .run 0 :: .run 0 :: L', R1))
  | (.CB, L, []) => strictMList (bumpM L) (fun L' => (.DL, L', [.run 0]))
  | (.CB, L, .zero :: R1) => strictMList (bumpM L) (fun L' => strictMList (bumpM R1) (fun R' => (.DL, L', R')))
  | (.CB, L, .run 0 :: []) => strictMList (bumpM L) (fun L' => (.BB, .run 0 :: L', []))
  | (.CB, L, .run 0 :: .zero :: R2) => strictMList (bumpM L) (fun L' => (.BB, .run 0 :: L', R2))
  | (.CB, L, .run 0 :: .run 0 :: R2) => strictMList (bumpM L) (fun L' => (.BB, .run 0 :: .zero :: L', R2))
  | (.CB, L, .run 0 :: .run (d2 + 1) :: R2) =>
      strictMList (bumpM L) (fun L1 => strictMList (prependZeroM d2 L1) (fun L2 => (.CB, .run 0 :: .run 0 :: L2, R2)))
  | (.CB, L, .run 1 :: R1) => strictMList (bumpM L) (fun L' => (.CB, .run 0 :: L', R1))
  | (.CB, L, .run 2 :: R1) => strictMList (bumpM L) (fun L' => (.BB, L', .run 0 :: .zero :: R1))
  | (.CB, L, .run (d + 3) :: R1) =>
      strictNat d (fun d' => strictMList (bumpM L) (fun L' => (.BB, L', .run 0 :: .run d' :: R1)))
  | s => s

def iterStep {α : Type} (f : α → α) : Nat → α → α
  | 0, s => s
  | n + 1, s => iterStep f n (f s)

theorem iterStep_commute (f : α → α) (n : Nat) :
    ∀ s, iterStep f n (f s) = f (iterStep f n s) := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    simp [iterStep, ih (f s)]

theorem iterStep_add (f : α → α) (m n : Nat) :
    ∀ s, iterStep f (m + n) s = iterStep f n (iterStep f m s) := by
  induction n with
  | zero => intro s; simp [iterStep]
  | succ n ih =>
    intro s
    simp only [iterStep]
    rw [← iterStep_commute f m s]
    exact ih (f s)

def stepElem16 := iterStep stepElemM 16
def stepElem256 := iterStep stepElem16 16
def stepElem4096 := iterStep stepElem256 16

def runElemFast (a b c d : Nat) (s : SymMode × List MItem × List MItem) :
    SymMode × List MItem × List MItem :=
  iterStep stepElemM a (iterStep stepElem16 b (iterStep stepElem256 c (iterStep stepElem4096 d s)))

theorem iterStep_block (f : α → α) (m n : Nat) :
    ∀ s, iterStep (iterStep f m) n s = iterStep f (m * n) s := by
  induction n with
  | zero => intro s; simp [iterStep]
  | succ n ih =>
    intro s
    simp only [iterStep]
    rw [ih (iterStep f m s)]
    calc
      iterStep f (m * n) (iterStep f m s) = iterStep f (m + m * n) s := by
        symm
        exact iterStep_add f m (m * n) s
      _ = iterStep f (m * n + m) s := by rw [Nat.add_comm]
      _ = iterStep f (m * (n + 1)) s := by rw [Nat.mul_succ]

theorem stepElem16_eq (s : SymMode × List MItem × List MItem) :
    stepElem16 s = iterStep stepElemM 16 s := rfl

theorem stepElem256_eq (s : SymMode × List MItem × List MItem) :
    stepElem256 s = iterStep stepElemM 256 s := by
  change iterStep (iterStep stepElemM 16) 16 s = iterStep stepElemM 256 s
  simpa using iterStep_block stepElemM 16 16 s

theorem stepElem4096_eq (s : SymMode × List MItem × List MItem) :
    stepElem4096 s = iterStep stepElemM 4096 s := by
  change iterStep stepElem256 16 s = iterStep stepElemM 4096 s
  have h256 : stepElem256 = iterStep stepElemM 256 := funext stepElem256_eq
  rw [h256]
  exact iterStep_block stepElemM 256 16 s

theorem runElemFast_eq_iterStep (a b c d : Nat) (s : SymMode × List MItem × List MItem) :
    runElemFast a b c d s = iterStep stepElemM (4096 * d + 256 * c + 16 * b + a) s := by
  unfold runElemFast
  have h16 : stepElem16 = iterStep stepElemM 16 := funext stepElem16_eq
  have h256 : stepElem256 = iterStep stepElemM 256 := funext stepElem256_eq
  have h4096 : stepElem4096 = iterStep stepElemM 4096 := funext stepElem4096_eq
  rw [h16, h256, h4096]
  have hb : iterStep (iterStep stepElemM 16) b = iterStep stepElemM (16 * b) := funext (iterStep_block stepElemM 16 b)
  have hc : iterStep (iterStep stepElemM 256) c = iterStep stepElemM (256 * c) := funext (iterStep_block stepElemM 256 c)
  have hd : iterStep (iterStep stepElemM 4096) d = iterStep stepElemM (4096 * d) := funext (iterStep_block stepElemM 4096 d)
  rw [hb, hc, hd]
  rw [← iterStep_add stepElemM (4096 * d) (256 * c)]
  rw [← iterStep_add stepElemM (4096 * d + 256 * c) (16 * b)]
  rw [← iterStep_add stepElemM (4096 * d + 256 * c + 16 * b) a]

def maxRunList : List MItem → Nat
  | [] => 0
  | .zero :: xs => maxRunList xs
  | .run n :: xs => max n (maxRunList xs)

def maxRunState (s : SymMode × List MItem × List MItem) : Nat :=
  max (maxRunList s.2.1) (maxRunList s.2.2)

theorem maxRunList_bumpM (xs : List MItem) : maxRunList (bumpM xs) ≤ maxRunList xs + 1 := by
  cases xs with
  | nil => simp [bumpM, maxRunList]
  | cons x xs =>
    cases x with
    | zero => simp [bumpM, maxRunList]
    | run d => simp [bumpM, maxRunList, strictNat_eq]; omega

theorem maxRunList_prependZeroM (n : Nat) (xs : List MItem) :
    maxRunList (prependZeroM n xs) = maxRunList xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [prependZeroM, maxRunList, ih]

theorem maxRunList_tail_le (x : MItem) (xs : List MItem) :
    maxRunList xs ≤ maxRunList (x :: xs) := by
  cases x with
  | zero => exact Nat.le_refl _
  | run d => exact Nat.le_max_right d (maxRunList xs)

theorem maxRunList_tail_le_succ (x : MItem) (xs : List MItem) :
    maxRunList xs ≤ maxRunList (x :: xs) + 1 := by
  have h := maxRunList_tail_le x xs
  omega

theorem maxRunList_run_mono (d e : Nat) (xs : List MItem) (h : d ≤ e) :
    maxRunList (.run d :: xs) ≤ maxRunList (.run e :: xs) := by
  simp only [maxRunList]
  apply Nat.max_le.mpr
  constructor
  · exact Nat.le_trans h (Nat.le_max_left e (maxRunList xs))
  · exact Nat.le_max_right e (maxRunList xs)

theorem maxRunList_run_mono_succ (d e : Nat) (xs : List MItem) (h : d ≤ e) :
    maxRunList (.run d :: xs) ≤ maxRunList (.run e :: xs) + 1 := by
  have hm := maxRunList_run_mono d e xs h
  omega

theorem max_le_max_succ {a b c d : Nat} (ha : a ≤ c + 1) (hb : b ≤ d + 1) :
    max a b ≤ max c d + 1 := by
  apply Nat.max_le.mpr
  constructor
  · exact Nat.le_trans ha (Nat.add_le_add_right (Nat.le_max_left c d) 1)
  · exact Nat.le_trans hb (Nat.add_le_add_right (Nat.le_max_right c d) 1)

theorem maxRunState_componentwise (mode : SymMode) (L R L' R' : List MItem)
    (hL : maxRunList L' ≤ maxRunList L + 1)
    (hR : maxRunList R' ≤ maxRunList R + 1) :
    maxRunState (mode, L', R') ≤ maxRunState (mode, L, R) + 1 := by
  exact max_le_max_succ hL hR

theorem maxRunState_stepElemM (s : SymMode × List MItem × List MItem) :
    maxRunState (stepElemM s) ≤ maxRunState s + 1 := by
  rcases s with ⟨mode, L, R⟩
  cases mode with
  | BB =>
    cases L with
    | nil =>
      simp only [stepElemM, strictMList_eq]
      apply maxRunState_componentwise
      · simp [maxRunList]
      · exact maxRunList_bumpM R
    | cons t L1 =>
      cases t with
      | zero =>
        simp only [stepElemM, strictMList_eq]
        apply maxRunState_componentwise
        · simp [maxRunList]
        · exact maxRunList_bumpM R
      | run d =>
        cases d with
        | zero =>
          simp only [stepElemM]
          apply maxRunState_componentwise
          · exact maxRunList_tail_le_succ (.run 0) L1
          · simp [maxRunList]
        | succ d =>
          cases d with
          | zero =>
            simp only [stepElemM, strictMList_eq]
            apply maxRunState_componentwise
            · exact maxRunList_tail_le_succ (.run 1) L1
            · simpa [maxRunList] using maxRunList_bumpM R
          | succ d =>
            cases d with
            | zero =>
              simp only [stepElemM, strictMList_eq]
              apply maxRunState_componentwise
              · exact maxRunList_tail_le_succ (.run 2) L1
              · simpa [maxRunList] using maxRunList_bumpM R
            | succ d =>
              cases d with
              | zero =>
                simp only [stepElemM, strictMList_eq]
                apply maxRunState_componentwise
                · simp [maxRunList] <;> omega
                · exact maxRunList_bumpM R
              | succ d =>
                simp only [stepElemM, strictNat_eq, strictMList_eq]
                apply maxRunState_componentwise
                · simpa [maxRunList] using (maxRunList_run_mono_succ d (d + 4) L1 (by omega))
                · exact maxRunList_bumpM R
  | DL =>
    cases L with
    | nil => simp [stepElemM]
    | cons t L1 =>
      cases t with
      | zero => simp [stepElemM, maxRunState, maxRunList] <;> omega
      | run d =>
        cases d with
        | zero =>
          simp only [stepElemM, strictMList_eq]
          apply maxRunState_componentwise
          · exact maxRunList_tail_le_succ (.run 0) L1
          · exact maxRunList_bumpM R
        | succ d =>
          cases d with
          | zero =>
            simp only [stepElemM, strictMList_eq]
            apply maxRunState_componentwise
            · exact maxRunList_tail_le_succ (.run 1) L1
            · simpa [maxRunList] using maxRunList_bumpM R
          | succ d =>
            cases d with
            | zero =>
              cases R with
              | nil => simp [stepElemM]
              | cons rt R1 =>
                cases rt with
                | zero => simp [stepElemM]
                | run d0 =>
                  simp only [stepElemM, strictMList_eq]
                  apply maxRunState_componentwise
                  · simp [maxRunList, maxRunList_prependZeroM] <;> omega
                  · exact maxRunList_tail_le_succ (.run d0) R1
            | succ d => simp [stepElemM]
  | CB =>
    cases R with
    | nil =>
      simp only [stepElemM, strictMList_eq]
      apply maxRunState_componentwise
      · exact maxRunList_bumpM L
      · simp [maxRunList]
    | cons t R1 =>
      cases t with
      | zero =>
        simp only [stepElemM, strictMList_eq]
        apply maxRunState_componentwise
        · exact maxRunList_bumpM L
        · exact maxRunList_bumpM R1
      | run d =>
        cases d with
        | zero =>
          cases R1 with
          | nil =>
            simp only [stepElemM, strictMList_eq]
            apply maxRunState_componentwise
            · simpa [maxRunList] using maxRunList_bumpM L
            · simp [maxRunList]
          | cons t2 R2 =>
            cases t2 with
            | zero =>
              simp only [stepElemM, strictMList_eq]
              apply maxRunState_componentwise
              · simpa [maxRunList] using maxRunList_bumpM L
              · exact maxRunList_tail_le_succ (.zero) R2
            | run d2 =>
              cases d2 with
              | zero =>
                simp only [stepElemM, strictMList_eq]
                apply maxRunState_componentwise
                · simpa [maxRunList] using maxRunList_bumpM L
                · exact maxRunList_tail_le_succ (.run 0) R2
              | succ d2 =>
                simp only [stepElemM, strictMList_eq]
                apply maxRunState_componentwise
                · simp [maxRunList, maxRunList_prependZeroM, maxRunList_bumpM]
                · exact maxRunList_tail_le_succ (.run (d2 + 1)) R2
        | succ d =>
          cases d with
          | zero =>
            simp only [stepElemM, strictMList_eq]
            apply maxRunState_componentwise
            · simpa [maxRunList] using maxRunList_bumpM L
            · exact maxRunList_tail_le_succ (.run 1) R1
          | succ d =>
            cases d with
            | zero =>
              simp only [stepElemM, strictMList_eq]
              apply maxRunState_componentwise
              · exact maxRunList_bumpM L
              · simp [maxRunList] <;> omega
            | succ d =>
              simp only [stepElemM, strictNat_eq, strictMList_eq]
              apply maxRunState_componentwise
              · exact maxRunList_bumpM L
              · simpa [maxRunList] using (maxRunList_run_mono_succ d (d + 3) R1 (by omega))
  | HALT => simp [stepElemM]

theorem maxRunState_iterStep_add
    (f : (SymMode × List MItem × List MItem) → (SymMode × List MItem × List MItem))
    (k : Nat) (hf : ∀ s, maxRunState (f s) ≤ maxRunState s + k) :
    ∀ n s, maxRunState (iterStep f n s) ≤ maxRunState s + k * n := by
  intro n
  induction n with
  | zero => intro s; simp [iterStep]
  | succ n ih =>
    intro s
    simp only [iterStep]
    calc
      maxRunState (iterStep f n (f s)) ≤ maxRunState (f s) + k * n := ih (f s)
      _ ≤ (maxRunState s + k) + k * n := Nat.add_le_add_right (hf s) (k * n)
      _ = maxRunState s + k * n + k := by omega
      _ = maxRunState s + k * (n + 1) := by rw [Nat.mul_succ]; omega

theorem maxRunState_stepElem16 (s : SymMode × List MItem × List MItem) :
    maxRunState (stepElem16 s) ≤ maxRunState s + 16 := by
  simpa [stepElem16] using
    (maxRunState_iterStep_add stepElemM 1 maxRunState_stepElemM 16 s)

theorem maxRunState_stepElem256 (s : SymMode × List MItem × List MItem) :
    maxRunState (stepElem256 s) ≤ maxRunState s + 256 := by
  have h : ∀ s, maxRunState (stepElem16 s) ≤ maxRunState s + 16 := maxRunState_stepElem16
  simpa [stepElem256] using (maxRunState_iterStep_add stepElem16 16 h 16 s)

theorem maxRunState_stepElem4096 (s : SymMode × List MItem × List MItem) :
    maxRunState (stepElem4096 s) ≤ maxRunState s + 4096 := by
  have h : ∀ s, maxRunState (stepElem256 s) ≤ maxRunState s + 256 := maxRunState_stepElem256
  simpa [stepElem4096] using (maxRunState_iterStep_add stepElem256 256 h 16 s)

theorem maxRunState_runElemFast (a b c d : Nat) (s : SymMode × List MItem × List MItem) :
    maxRunState (runElemFast a b c d s) ≤
      maxRunState s + a + 16 * b + 256 * c + 4096 * d := by
  unfold runElemFast
  have ha := maxRunState_iterStep_add stepElemM 1 maxRunState_stepElemM a
    (iterStep stepElem16 b (iterStep stepElem256 c (iterStep stepElem4096 d s)))
  have hb := maxRunState_iterStep_add stepElem16 16 maxRunState_stepElem16 b
    (iterStep stepElem256 c (iterStep stepElem4096 d s))
  have hc := maxRunState_iterStep_add stepElem256 256 maxRunState_stepElem256 c
    (iterStep stepElem4096 d s)
  have hd := maxRunState_iterStep_add stepElem4096 4096 maxRunState_stepElem4096 d s
  omega

def iterStepTraceMax (f : (SymMode × List MItem × List MItem) → (SymMode × List MItem × List MItem)) :
    Nat → (SymMode × List MItem × List MItem) → Nat
  | 0, s => maxRunState s
  | n + 1, s => max (maxRunState s) (iterStepTraceMax f n (f s))

theorem iterStepTraceMax_le
    (f : (SymMode × List MItem × List MItem) → (SymMode × List MItem × List MItem))
    (k : Nat) (hf : ∀ s, maxRunState (f s) ≤ maxRunState s + k) :
    ∀ n s, iterStepTraceMax f n s ≤ maxRunState s + k * n := by
  intro n
  induction n with
  | zero => intro s; simp [iterStepTraceMax]
  | succ n ih =>
    intro s
    simp only [iterStepTraceMax]
    apply Nat.max_le.mpr
    constructor
    · omega
    · calc
        iterStepTraceMax f n (f s) ≤ maxRunState (f s) + k * n := ih (f s)
        _ ≤ (maxRunState s + k) + k * n := Nat.add_le_add_right (hf s) (k * n)
        _ = maxRunState s + k * (n + 1) := by rw [Nat.mul_succ]; omega

def f424PrefixStart : SymMode × List MItem × List MItem :=
  (.CB, [], [.run 1, .run 0])

def f412PrefixStart : SymMode × List MItem × List MItem :=
  (.BB, [.run 0], [])

theorem f424_runElemFast_max_le :
    maxRunState (runElemFast 1 1 11 4 f424PrefixStart) ≤ 19218 := by
  have h := maxRunState_runElemFast 1 1 11 4 f424PrefixStart
  simp [f424PrefixStart, maxRunState, maxRunList] at h ⊢
  omega

theorem f412_runElemFast_max_le :
    maxRunState (runElemFast 7 3 11 4 f412PrefixStart) ≤ 19255 := by
  have h := maxRunState_runElemFast 7 3 11 4 f412PrefixStart
  simp [f412PrefixStart, maxRunState, maxRunList] at h ⊢
  omega

theorem f424_runElemFast_trace_max_le :
    iterStepTraceMax stepElemM 19217 f424PrefixStart ≤ 19218 := by
  have h := iterStepTraceMax_le stepElemM 1 maxRunState_stepElemM 19217 f424PrefixStart
  simp [f424PrefixStart, maxRunState, maxRunList] at h ⊢
  omega

theorem f412_runElemFast_trace_max_le :
    iterStepTraceMax stepElemM 19255 f412PrefixStart ≤ 19255 := by
  have h := iterStepTraceMax_le stepElemM 1 maxRunState_stepElemM 19255 f412PrefixStart
  simp [f412PrefixStart, maxRunState, maxRunList] at h ⊢
  omega

theorem f424_prefix_coarse_cost_lt :
    19217 * (3 * 19218 + 22) + 19 < 2^31 := by decide

theorem f412_prefix_coarse_cost_lt :
    19255 * (3 * 19255 + 22) + 2 < 2^31 := by decide

