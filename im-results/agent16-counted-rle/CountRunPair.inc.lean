
-- Strict forward accumulator: normalize each state and its count once.
def countRunSteps (n : Nat) (s : RleFullState) (a : Nat) : RleFullState × Nat :=
  Nat.rec (fun s a => (s, a))
    (fun _ ih s a =>
      match s with
      | ⟨m, ls, R, true⟩ => (⟨m, ls, R, true⟩, a)
      | ⟨m, ls, R, false⟩ =>
        strictNat (a + costRleStep ⟨m, ls, R, false⟩) (fun a' =>
          strictStateFast (rleStep ⟨m, ls, R, false⟩) (fun s' => ih s' a')))
    n s a

theorem countRunSteps_succ (n : Nat) (s : RleFullState) (a : Nat) :
    countRunSteps (n+1) s a =
      match s with
      | ⟨m, ls, R, true⟩ => (⟨m, ls, R, true⟩, a)
      | ⟨m, ls, R, false⟩ =>
        strictNat (a + costRleStep ⟨m, ls, R, false⟩) (fun a' =>
          strictStateFast (rleStep ⟨m, ls, R, false⟩) (fun s' => countRunSteps n s' a')) := rfl

theorem countRunSteps_eq (n : Nat) (s : RleFullState) (a : Nat) :
    countRunSteps n s a = (runStepsInner n s, a + costStepsInner n s) := by
  induction n generalizing s a with
  | zero => rfl
  | succ n ih =>
    rcases s with ⟨m, ls, R, h⟩
    cases h <;> rw [countRunSteps_succ, runStepsInner_succ, costStepsInner_succ]
    · simp only [strictNat_eq, strictStateFast_eq, ih, Nat.add_assoc]
    · simp only [Nat.add_zero]

def countRunBatches (b : Nat) (s : RleFullState) (a : Nat) : RleFullState × Nat :=
  Nat.rec (fun s a => (s,a))
    (fun _ ih s a =>
      match countRunSteps 25 s a with
      | (s', a') => strictNat a' (fun a'' => strictState s' (fun s'' => ih s'' a'')))
    b s a

theorem countRunBatches_succ (b : Nat) (s : RleFullState) (a : Nat) :
    countRunBatches (b+1) s a =
      match countRunSteps 25 s a with
      | (s', a') => strictNat a' (fun a'' => strictState s' (fun s'' => countRunBatches b s'' a'')) := rfl

theorem countRunBatches_eq (b : Nat) (s : RleFullState) (a : Nat) :
    countRunBatches b s a = (runBatches b s, a + costBatches b s) := by
  induction b generalizing s a with
  | zero => rfl
  | succ b ih =>
    rw [countRunBatches_succ, runBatches_succ, costBatches_succ, countRunSteps_eq]
    simp only [strictNat_eq, strictState_eq, ih, Nat.add_assoc]

theorem countRunBatches_pair {b k : Nat} {s1 s2 : RleFullState}
    (h : countRunBatches b s1 0 = (s2,k)) : runBatches b s1 = s2 ∧ costBatches b s1 = k := by
  rw [countRunBatches_eq, Nat.zero_add] at h
  exact Prod.mk.inj h
