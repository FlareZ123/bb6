import Enumerate62Potential

namespace BB6.Agent11CutPotential

open BB6.Agent48Queue

/--
Exact worst-case number of source queue updates in the complete normalized
expansion subtree of a node with `cut` introduced states and `holes`
undefined rows. Existing-label children retain the cut; the four least-fresh
children increase it by one. The one-hole optimization makes the terminal
cost exactly one.
-/
def cutWeight (cut : Nat) : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 =>
      1 + 4 * cut * cutWeight cut (n + 1) +
        (if cut < 6 then 4 * cutWeight (cut + 1) (n + 1) else 0)

theorem cutWeight_step (cut n : Nat) :
    cutWeight cut (n + 2) =
      1 + 4 * cut * cutWeight cut (n + 1) +
        (if cut < 6 then 4 * cutWeight (cut + 1) (n + 1) else 0) := rfl

theorem cutWeight_pos (cut holes : Nat) : 0 < cutWeight cut holes := by
  cases holes with
  | zero => simp [cutWeight]
  | succ n =>
      cases n with
      | zero => simp [cutWeight]
      | succ n => simp [cutWeight]; omega

theorem cutWeight_expand_eq (cut holes : Nat) (hh : 2 ≤ holes) :
    cutWeight cut holes =
      1 + 4 * cut * cutWeight cut (holes - 1) +
        (if cut < 6 then 4 * cutWeight (cut + 1) (holes - 1) else 0) := by
  have h2 : (holes - 2) + 2 = holes := by omega
  have h1 : (holes - 2) + 1 = holes - 1 := by omega
  calc
    cutWeight cut holes = cutWeight cut ((holes - 2) + 2) :=
      congrArg (cutWeight cut) h2.symm
    _ = 1 + 4 * cut * cutWeight cut ((holes - 2) + 1) +
          (if cut < 6 then 4 * cutWeight (cut + 1) ((holes - 2) + 1) else 0) :=
      cutWeight_step cut (holes - 2)
    _ = 1 + 4 * cut * cutWeight cut (holes - 1) +
          (if cut < 6 then 4 * cutWeight (cut + 1) (holes - 1) else 0) := by
      rw [h1]

def cutNodeWeight (x : Node) : Nat := cutWeight x.cut.val x.holes

theorem cutNodeWeight_pos (x : Node) : 0 < cutNodeWeight x :=
  cutWeight_pos x.cut.val x.holes

def cutMass : List Node → Nat
  | [] => 0
  | x :: xs => cutNodeWeight x + cutMass xs

theorem cutMass_append (xs ys : List Node) :
    cutMass (xs ++ ys) = cutMass xs + cutMass ys := by
  induction xs with
  | nil => simp [cutMass]
  | cons x xs ih => simp [cutMass, ih, Nat.add_assoc]

theorem cutMass_replicate (n : Nat) (x : Node) :
    cutMass (List.replicate n x) = n * cutNodeWeight x := by
  induction n with
  | zero => simp [cutMass]
  | succ n ih =>
      change cutNodeWeight x + cutMass (List.replicate n x) =
        (n + 1) * cutNodeWeight x
      rw [ih, Nat.succ_mul]
      omega

theorem cutMass_zero_iff_nil (xs : List Node) :
    cutMass xs = 0 ↔ xs = [] := by
  cases xs with
  | nil => simp [cutMass]
  | cons x xs =>
      constructor
      · intro h
        have hw := cutNodeWeight_pos x
        simp [cutMass] at h
        omega
      · intro h
        cases h

theorem cutMass_take_le (xs : List Node) (n : Nat) :
    cutMass (xs.take n) ≤ cutMass xs := by
  induction xs generalizing n with
  | nil => simp [cutMass]
  | cons x xs ih =>
      cases n with
      | zero => simp [cutMass]
      | succ n =>
          have h := ih n
          simp [cutMass] at h ⊢
          omega

theorem cutMass_drop_le (xs : List Node) (n : Nat) :
    cutMass (xs.drop n) ≤ cutMass xs := by
  induction xs generalizing n with
  | nil => simp [cutMass]
  | cons x xs ih =>
      cases n with
      | zero => simp [cutMass]
      | succ n =>
          have h := ih n
          simp [cutMass] at h ⊢
          omega

theorem cutMass_chunk_le (xs : List Node) (l sz : Nat) :
    cutMass ((xs.drop l).take sz) ≤ cutMass xs := by
  calc
    cutMass ((xs.drop l).take sz) ≤ cutMass (xs.drop l) :=
      cutMass_take_le (xs.drop l) sz
    _ ≤ cutMass xs := cutMass_drop_le xs l

theorem cutNodeWeight_existing (x : Node) :
    cutNodeWeight (existingChild x) =
      cutWeight x.cut.val (x.holes - 1) := rfl

theorem cutNodeWeight_fresh (x : Node) (hc : x.cut.val < 6) :
    cutNodeWeight (freshChild x) =
      cutWeight (x.cut.val + 1) (x.holes - 1) := by
  unfold cutNodeWeight
  rw [freshChild_cut x hc]
  rfl

/-- Exact weighted mass of all ordinary children in the source expansion. -/
theorem cutMass_expandProjection (x : Node) :
    cutMass (expandProjection x) =
      4 * x.cut.val * cutWeight x.cut.val (x.holes - 1) +
        (if x.cut.val < 6 then
          4 * cutWeight (x.cut.val + 1) (x.holes - 1) else 0) := by
  unfold expandProjection
  rw [cutMass_append, cutMass_replicate]
  by_cases hc : x.cut.val < 6
  · rw [if_pos hc, cutMass_replicate]
    rw [cutNodeWeight_existing, cutNodeWeight_fresh x hc]
    simp [hc]
  · rw [if_neg hc]
    simp [cutMass, cutNodeWeight_existing, hc]

/-- A Halt update consumes the parent and replaces it by strictly less
weighted mass, with the exact state-cut branching recurrence. -/
theorem cutMass_expandProjection_succ (x : Node) (hh : 2 ≤ x.holes) :
    cutMass (expandProjection x) + 1 = cutNodeWeight x := by
  rw [cutMass_expandProjection]
  unfold cutNodeWeight
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (cutWeight_expand_eq x.cut.val x.holes hh).symm

theorem expandProjection'_cutMass_lt (x : Node) (hpos : 1 ≤ x.holes) :
    cutMass (expandProjection' x hpos) < cutNodeWeight x := by
  by_cases h : x.holes = 1
  · simp [expandProjection', h, cutMass, cutNodeWeight, cutWeight]
  · have htwo : 2 ≤ x.holes := by omega
    have heq := cutMass_expandProjection_succ x htwo
    change cutMass (if x.holes = 1 then [] else expandProjection x) <
      cutNodeWeight x
    rw [if_neg h]
    omega

theorem update_cutMass_lt (decide : (x : Node) → Verdict x)
    (q : SearchQueue) (hne : q.active ≠ []) :
    cutMass (update decide q).active < cutMass q.active := by
  cases hq : q.active with
  | nil => exact False.elim (hne hq)
  | cons x xs =>
      cases hd : decide x with
      | halt hpos =>
          simp [update, hq, hd, cutMass_append]
          exact Nat.add_lt_add_right (expandProjection'_cutMass_lt x hpos)
            (cutMass xs)
      | nonhalt =>
          simp [update, hq, hd, cutMass]
          exact Nat.lt_add_of_pos_left (cutNodeWeight_pos x)
      | unknown =>
          simp [update, hq, hd, cutMass]
          exact Nat.lt_add_of_pos_left (cutNodeWeight_pos x)

theorem runUpdates_cutMass_active_empty_of_bound
    (decide : (x : Node) → Verdict x) (fuel : Nat) (q : SearchQueue)
    (hbound : cutMass q.active ≤ fuel) :
    (runUpdates decide fuel q).active = [] := by
  induction fuel generalizing q with
  | zero =>
      have hmass : cutMass q.active = 0 := by omega
      have hnil : q.active = [] := (cutMass_zero_iff_nil q.active).mp hmass
      simp [runUpdates, hnil]
  | succ fuel ih =>
      cases hq : q.active with
      | nil => simp [runUpdates, hq]
      | cons x xs =>
          have hdec := update_cutMass_lt decide q (by simp [hq])
          have hnext : cutMass (update decide q).active ≤ fuel := by omega
          simpa [runUpdates, hq] using ih (update decide q) hnext

theorem cutBfsAux_mass_le (decide : (x : Node) → Verdict x) :
    ∀ xs holdout,
      cutMass (bfsAux decide xs holdout) ≤ cutMass xs + cutMass holdout := by
  intro xs
  induction xs with
  | nil =>
      intro holdout
      simp [bfsAux, cutMass]
  | cons x xs ih =>
      intro holdout
      cases hd : decide x with
      | halt hpos =>
          have hrec := ih (expandProjection' x hpos ++ holdout)
          rw [cutMass_append] at hrec
          have hchild := expandProjection'_cutMass_lt x hpos
          simp only [bfsAux, hd, cutMass]
          omega
      | nonhalt =>
          have hrec := ih holdout
          simp only [bfsAux, hd, cutMass]
          omega
      | unknown =>
          have hrec := ih (x :: holdout)
          simp [cutMass] at hrec
          simp only [bfsAux, hd, cutMass]
          omega

def cutTotalMass (q : SearchQueue) : Nat :=
  cutMass q.active + cutMass q.holdout

theorem cutBfsRound_total_mass_le (decide : (x : Node) → Verdict x)
    (q : SearchQueue) :
    cutTotalMass (bfsRound decide q) ≤ cutTotalMass q := by
  unfold cutTotalMass bfsRound
  change cutMass (bfsAux decide q.active q.holdout) + 0 ≤
    cutMass q.active + cutMass q.holdout
  simpa using cutBfsAux_mass_le decide q.active q.holdout

theorem cutFourBfsPasses_total_mass_le (decide : (x : Node) → Verdict x)
    (q : SearchQueue) :
    cutTotalMass (fourBfsPasses decide q) ≤ cutTotalMass q := by
  unfold fourBfsPasses
  have h1 := cutBfsRound_total_mass_le decide
    (bfsRound decide (bfsRound decide (bfsRound decide q)))
  have h2 := cutBfsRound_total_mass_le decide
    (bfsRound decide (bfsRound decide q))
  have h3 := cutBfsRound_total_mass_le decide (bfsRound decide q)
  have h4 := cutBfsRound_total_mass_le decide q
  exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4))

theorem cutQ0_total_mass_le (decide : (x : Node) → Verdict x) :
    cutTotalMass (q0 decide) ≤ cutWeight 2 11 := by
  have hroot : cutTotalMass rootQueue = cutWeight 2 11 := by
    simp [cutTotalMass, rootQueue, rootNode, cutMass, cutNodeWeight]
  rw [← hroot]
  exact cutFourBfsPasses_total_mass_le decide rootQueue

theorem cutChunkActiveMass_le (q : SearchQueue) (l sz : Nat) :
    cutMass (chunkQueue q l sz).active ≤ cutTotalMass q := by
  change cutMass ((q.active.drop l).take sz) ≤
    cutMass q.active + cutMass q.holdout
  have h := cutMass_chunk_le q.active l sz
  omega

theorem cutWeight_root_value :
    cutWeight 2 11 = 3072847418605 := by decide

theorem cutWeight_root_lt_old_bound :
    cutWeight 2 11 < 25 ^ 11 := by decide

theorem cutWeight_root_le_maxT :
    cutWeight 2 11 ≤ maxT := by decide

theorem cutWeight_0_seven : cutWeight 0 7 = 888933 := by decide
theorem cutWeight_1_seven : cutWeight 1 7 = 3810329 := by decide
theorem cutWeight_2_seven : cutWeight 2 7 = 13980909 := by decide
theorem cutWeight_3_seven : cutWeight 3 7 = 43268961 := by decide
theorem cutWeight_4_seven : cutWeight 4 7 = 108653749 := by decide
theorem cutWeight_5_seven : cutWeight 5 7 = 199411801 := by decide
theorem cutWeight_6_seven : cutWeight 6 7 = 199411801 := by decide

theorem cutWeight_seven_le (c : Fin 7) :
    cutWeight c.val 7 ≤ 199411801 := by
  have hc : c.val < 7 := c.isLt
  have hval : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 ∨ c.val = 3 ∨
      c.val = 4 ∨ c.val = 5 ∨ c.val = 6 := by omega
  rcases hval with h | h | h | h | h | h | h
  · rw [h, cutWeight_0_seven]
    decide
  · rw [h, cutWeight_1_seven]
    decide
  · rw [h, cutWeight_2_seven]
    decide
  · rw [h, cutWeight_3_seven]
    decide
  · rw [h, cutWeight_4_seven]
    decide
  · rw [h, cutWeight_5_seven]
    decide
  · rw [h, cutWeight_6_seven]
    decide

/-- The pinned MAXT bound follows from the sharper state-cut potential.
This is still only a fuel theorem: the independent queue-coverage invariant,
classifier soundness, and actual holdout certificates remain necessary. -/
theorem every_chunk_drains_cut (decide : (x : Node) → Verdict x)
    (l sz : Nat) :
    (runUpdates decide maxT (chunkQueue (q0 decide) l sz)).active = [] := by
  apply runUpdates_cutMass_active_empty_of_bound
  have hchunk := cutChunkActiveMass_le (q0 decide) l sz
  have hq0 := cutQ0_total_mass_le decide
  exact Nat.le_trans (Nat.le_trans hchunk hq0) cutWeight_root_le_maxT

#print axioms cutWeight_expand_eq
#print axioms cutMass_expandProjection
#print axioms cutMass_expandProjection_succ
#print axioms update_cutMass_lt
#print axioms runUpdates_cutMass_active_empty_of_bound
#print axioms cutBfsRound_total_mass_le
#print axioms cutQ0_total_mass_le
#print axioms every_chunk_drains_cut

end BB6.Agent11CutPotential
