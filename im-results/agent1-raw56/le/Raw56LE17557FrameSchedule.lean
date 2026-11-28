import Raw56LE17557DefectStack

namespace BB6.Agent1Raw56.LE17557FrameSchedule
open BB6.Agent1Raw56.LE17557RhoArithmetic
open BB6.Agent1Raw56.LE17557DefectStack

/-- A single finite zero-run frame is hit by B/C actions in this recursively
    generated order.  `true` is B and `false` is carry C. -/
def frame : Nat → List Bool
  | 0 => [true]
  | r + 1 => frame r ++ [false, true] ++ frame r ++ [false]

/-- Prefix-balance machine: B increments, C decrements, and C at zero fails. -/
def walk : Nat → List Bool → Option Nat
  | n, [] => some n
  | n, true :: xs => walk (n+1) xs
  | 0, false :: _ => none
  | n+1, false :: xs => walk n xs

theorem walk_append (n : Nat) (u v : List Bool) :
    walk n (u ++ v) = (walk n u).bind (fun k => walk k v) := by
  induction u generalizing n with
  | nil => rfl
  | cons a u ih =>
      cases a <;> cases n <;> simp [walk, ih]

/-- Every frame word is ballot-safe and has net B-minus-C balance one. -/
theorem walk_frame (r n : Nat) : walk n (frame r) = some (n+1) := by
  induction r generalizing n with
  | zero => simp [frame, walk]
  | succ r ih =>
      simpa [frame, walk_append, ih, walk, List.append_assoc]

def countB (w : List Bool) : Nat := w.count true
def countC (w : List Bool) : Nat := w.count false

@[simp] theorem countB_append (u v : List Bool) :
    countB (u ++ v) = countB u + countB v := by
  simp [countB, List.count_append]

@[simp] theorem countC_append (u v : List Bool) :
    countC (u ++ v) = countC u + countC v := by
  simp [countC, List.count_append]

theorem frame_counts_plus (r : Nat) :
    countB (frame r) + 1 = 2^(r+1) ∧
    countC (frame r) + 2 = 2^(r+1) := by
  induction r with
  | zero => decide
  | succ r ih =>
      rcases ih with ⟨hb,hc⟩
      constructor <;>
        simp [frame, countB, countC, List.count_append, Nat.pow_succ] at * <;>
        omega

theorem frame_counts (r : Nat) :
    countB (frame r) = 2^(r+1) - 1 ∧
    countC (frame r) = 2^(r+1) - 2 := by
  have h := frame_counts_plus r
  omega

theorem frame_length_plus (r : Nat) :
    (frame r).length + 3 = 2^(r+2) := by
  induction r with
  | zero => decide
  | succ r ih =>
      simp [frame, Nat.pow_succ] at *
      omega

theorem frame_length (r : Nat) :
    (frame r).length = 2^(r+2) - 3 := by
  have h := frame_length_plus r
  omega

theorem prefix_walk_some {n m : Nat} {p s : List Bool}
    (h : walk n (p ++ s) = some m) : ∃ k, walk n p = some k := by
  rw [walk_append] at h
  cases hp : walk n p with
  | none => simp [hp] at h
  | some k => exact ⟨k, rfl⟩

theorem walk_count_balance {n m : Nat} {w : List Bool}
    (h : walk n w = some m) :
    m + countC w = n + countB w := by
  induction w generalizing n m with
  | nil =>
      simp [walk] at h
      subst m
      simp [countB, countC]
  | cons a w ih =>
      cases a with
      | false =>
          cases n with
          | zero => simp [walk] at h
          | succ n =>
              simp only [walk] at h
              have hh := ih h
              simp [countB, countC] at hh ⊢
              omega
      | true =>
          simp only [walk] at h
          have hh := ih h
          simp [countB, countC] at hh ⊢
          omega

/-- Every prefix of a frame has at least as many B actions as carries. -/
theorem frame_prefix_ballot (r : Nat) {p s : List Bool}
    (hps : frame r = p ++ s) : countC p ≤ countB p := by
  have hw : walk 0 (frame r) = some 1 := by
    simpa using walk_frame r 0
  rw [hps] at hw
  obtain ⟨k,hk⟩ := prefix_walk_some hw
  have hb := walk_count_balance hk
  simp at hb
  omega

/-- Pure arithmetic normal form for a frame prefix. -/
theorem rho_frame_balance (q d : Nat) :
    rhoZero (8*q + d - 1) =
      16*q + d - 1 + 8*(d/8) := by
  unfold rhoZero
  by_cases h7 : (8*q + d - 1) % 8 = 7
  · simp [h7]
    omega
  · simp [h7]
    omega

/-- Remaining low-side runway after a prefix. -/
def lowRemaining (r : Nat) (p : List Bool) : Nat :=
  8 * (2^(r+1) - 1) - 1 - (7 * countB p + countC p)

/-- Remaining high-side runway after the same prefix. -/
def highRemaining (r : Nat) (p : List Bool) : Nat :=
  16 * (2^(r+1) - 1) - 1 - (15 * countB p + countC p)

theorem frame_prefix_count_bounds (r : Nat) {p s : List Bool}
    (hps : frame r = p ++ s) :
    countB p ≤ 2^(r+1)-1 ∧ countC p ≤ 2^(r+1)-2 := by
  have hc := frame_counts r
  have hbapp : countB (frame r) = countB p + countB s := by
    rw [hps, countB_append]
  have hcapp : countC (frame r) = countC p + countC s := by
    rw [hps, countC_append]
  omega

theorem lowRemaining_balance_form (r : Nat) {p s : List Bool}
    (hps : frame r = p ++ s) :
    lowRemaining r p =
      8 * ((2^(r+1)-1) - countB p) +
        (countB p - countC p) - 1 := by
  have hb := frame_prefix_ballot r hps
  have hc := frame_prefix_count_bounds r hps
  unfold lowRemaining
  omega

theorem highRemaining_balance_form (r : Nat) {p s : List Bool}
    (hps : frame r = p ++ s) :
    highRemaining r p =
      16 * ((2^(r+1)-1) - countB p) +
        (countB p - countC p) - 1 := by
  have hb := frame_prefix_ballot r hps
  have hc := frame_prefix_count_bounds r hps
  unfold highRemaining
  omega

/-- Exact defect formula for every frame prefix. -/
theorem frame_prefix_rho (r : Nat) {p s : List Bool}
    (hps : frame r = p ++ s) :
    rhoZero (lowRemaining r p) =
      highRemaining r p + 8 * ((countB p - countC p) / 8) := by
  rw [lowRemaining_balance_form r hps, highRemaining_balance_form r hps]
  exact rho_frame_balance ((2^(r+1)-1) - countB p)
    (countB p - countC p)

def prefixWeight (p : List Bool) : Nat :=
  (countB p - countC p) / 8

/-- The existing weighted-defect relation is therefore not merely heuristic:
    on an abstract frame schedule its exact weight is floor((B-C)/8). -/
theorem frame_prefix_defect (r : Nat) {p s : List Bool}
    (hps : frame r = p ++ s) :
    weightedZero (lowRemaining r p) (prefixWeight p) =
      highRemaining r p := by
  unfold weightedZero prefixWeight
  have h := frame_prefix_rho r hps
  omega

def lowCost (w : List Bool) : Nat := 7 * countB w + countC w
def highCost (w : List Bool) : Nat := 15 * countB w + countC w

theorem frame_lowCost (r : Nat) :
    lowCost (frame r) = 8*(2^(r+1)-1)-1 := by
  rcases frame_counts r with ⟨hb,hc⟩
  unfold lowCost
  omega

theorem frame_highCost (r : Nat) :
    highCost (frame r) = 16*(2^(r+1)-1)-1 := by
  rcases frame_counts r with ⟨hb,hc⟩
  unfold highCost
  omega

/-- Remaining runway is exactly the cost of the unexecuted suffix. -/
theorem lowRemaining_eq_suffixCost (r : Nat) {p s : List Bool}
    (hps : frame r = p ++ s) :
    lowRemaining r p = lowCost s := by
  have hf := frame_lowCost r
  have hbapp : countB (frame r) = countB p + countB s := by
    rw [hps, countB_append]
  have hcapp : countC (frame r) = countC p + countC s := by
    rw [hps, countC_append]
  unfold lowRemaining lowCost at *
  omega

theorem highRemaining_eq_suffixCost (r : Nat) {p s : List Bool}
    (hps : frame r = p ++ s) :
    highRemaining r p = highCost s := by
  have hf := frame_highCost r
  have hbapp : countB (frame r) = countB p + countB s := by
    rw [hps, countB_append]
  have hcapp : countC (frame r) = countC p + countC s := by
    rw [hps, countC_append]
  unfold highRemaining highCost at *
  omega

/-- The closed-form frame weight updates exactly by the defect-stack B
    transition at every scheduled B hit. -/
theorem next_B_weight_update (r : Nat) {p s : List Bool}
    (hps : frame r = p ++ true :: s) :
    bNextWeight (lowRemaining r p) (prefixWeight p) =
      prefixWeight (p ++ [true]) := by
  have hbal := frame_prefix_ballot r hps
  have hf := lowRemaining_balance_form r hps
  have hsuf := lowRemaining_eq_suffixCost r hps
  have h7 : 7 ≤ lowRemaining r p := by
    rw [hsuf]
    simp [lowCost, countB, countC]
  by_cases hd : countB p = countC p
  · have hn : lowRemaining r p % 8 ≠ 6 := by
      intro h6
      omega
    simp [prefixWeight, bNextWeight, countB, countC,
      List.count_append, hd, hn]
  · have hdpos : 1 ≤ countB p - countC p := by omega
    have hm :
        lowRemaining r p % 8 =
          (countB p - countC p - 1) % 8 := by
      have heq :
          lowRemaining r p =
            8 * ((2^(r+1)-1) - countB p) +
              (countB p - countC p - 1) := by
        omega
      rw [heq, Nat.add_mod]
      simp
    unfold prefixWeight bNextWeight
    rw [hm]
    simp only [countB, countC, List.count_append, List.count_cons,
      List.count_nil, Nat.add_zero]
    split <;> omega

/-- Likewise the closed-form frame weight follows the carry transition exactly.
    Ballot positivity at a scheduled carry supplies the only delicate case. -/
theorem next_C_weight_update (r : Nat) {p s : List Bool}
    (hps : frame r = p ++ false :: s) :
    carryNextWeight (lowRemaining r p) (prefixWeight p) =
      prefixWeight (p ++ [false]) := by
  have hbfull : countC (p ++ [false]) ≤ countB (p ++ [false]) := by
    apply frame_prefix_ballot r (p := p ++ [false]) (s := s)
    simpa [List.append_assoc] using hps
  have hpos : countC p + 1 ≤ countB p := by
    simpa [countB, countC, List.count_append] using hbfull
  have hf := lowRemaining_balance_form r hps
  have hm :
      lowRemaining r p % 8 =
        (countB p - countC p - 1) % 8 := by
    have heq :
        lowRemaining r p =
          8 * ((2^(r+1)-1) - countB p) +
            (countB p - countC p - 1) := by
      omega
    rw [heq, Nat.add_mod]
    simp
  unfold prefixWeight carryNextWeight
  rw [hm]
  simp only [countB, countC, List.count_append, List.count_cons,
    List.count_nil, Nat.add_zero]
  split <;> omega

/-- The B/BBA semantic runway guards follow immediately from suffix cost. -/
theorem next_B_guards (r : Nat) {p s : List Bool}
    (hps : frame r = p ++ true :: s) :
    7 ≤ lowRemaining r p ∧ 15 ≤ highRemaining r p := by
  have hl := lowRemaining_eq_suffixCost r hps
  have hh := highRemaining_eq_suffixCost r hps
  simp [lowCost, highCost, countB, countC] at hl hh ⊢
  omega

/-- The carry semantic runway guards likewise follow from suffix cost. -/
theorem next_C_guards (r : Nat) {p s : List Bool}
    (hps : frame r = p ++ false :: s) :
    1 ≤ lowRemaining r p ∧ 1 ≤ highRemaining r p := by
  have hl := lowRemaining_eq_suffixCost r hps
  have hh := highRemaining_eq_suffixCost r hps
  simp [lowCost, highCost, countB, countC] at hl hh ⊢
  omega

theorem next_C_balance_positive (r : Nat) {p s : List Bool}
    (hps : frame r = p ++ false :: s) :
    1 ≤ countB p - countC p := by
  have hbfull : countC (p ++ [false]) ≤ countB (p ++ [false]) := by
    apply frame_prefix_ballot r (p := p ++ [false]) (s := s)
    simpa [List.append_assoc] using hps
  have hb : countC p + 1 ≤ countB p := by
    simpa [countB, countC, List.count_append] using hbfull
  omega

/-- This is exactly the formerly separate residue-7 positivity guard:
    if a carry sees a residue-7 low runway, the prefix balance is a positive
    multiple of eight, hence its defect weight is positive. -/
theorem next_C_residue7_weight_positive (r : Nat) {p s : List Bool}
    (hps : frame r = p ++ false :: s)
    (hr : lowRemaining r p % 8 = 7) :
    1 ≤ prefixWeight p := by
  have hb := next_C_balance_positive r hps
  have hf := lowRemaining_balance_form r hps
  unfold prefixWeight
  omega

/-- Refinement of an outer-frame hit when the entire macro level is
    lifted once: an outer B becomes B B C, while an outer carry remains a
    carry because the inserted N_0 B pair is a complete nested frame. -/
def refineLetter : Bool → List Bool
  | true => [true, true, false]
  | false => [false]

def refine (w : List Bool) : List Bool := w.flatMap refineLetter

@[simp] theorem refine_nil : refine [] = [] := rfl

@[simp] theorem refine_cons (a : Bool) (w : List Bool) :
    refine (a :: w) = refineLetter a ++ refine w := rfl

@[simp] theorem refine_append (u v : List Bool) :
    refine (u ++ v) = refine u ++ refine v := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      simp [refine, List.append_assoc, ih]

/-- The recursive frame schedule is exactly the outer-hit schedule induced by
    one level of the rank-labelled macro substitution. -/
theorem frame_succ_refine (r : Nat) :
    frame (r+1) = [true, false] ++ refine (frame r) := by
  induction r with
  | zero => decide
  | succ r ih =>
      calc
        frame (r+2) =
            frame (r+1) ++ [false, true] ++ frame (r+1) ++ [false] := rfl
        _ = ([true, false] ++ refine (frame r)) ++ [false, true] ++
              ([true, false] ++ refine (frame r)) ++ [false] := by rw [ih]
        _ = [true, false] ++
              (refine (frame r) ++ [false] ++ [true, true, false] ++
               refine (frame r) ++ [false]) := by
              simp [List.append_assoc]
        _ = [true, false] ++
              refine (frame r ++ [false, true] ++ frame r ++ [false]) := by
              simp [refine_append, refineLetter, List.append_assoc]
        _ = [true, false] ++ refine (frame (r+1)) := rfl

/-- A canonical prefix attaining the largest recursively exposed balance. -/
def peak : Nat → List Bool
  | 0 => [true]
  | r + 1 => frame r ++ [false, true] ++ peak r

theorem peak_prefix (r : Nat) : ∃ s, frame r = peak r ++ s := by
  induction r with
  | zero => exact ⟨[], by simp [frame, peak]⟩
  | succ r ih =>
      obtain ⟨s, hs⟩ := ih
      refine ⟨s ++ [false], ?_⟩
      simp [frame, peak, hs, List.append_assoc]

theorem frame_balance_one (r : Nat) :
    countB (frame r) = countC (frame r) + 1 := by
  rcases frame_counts_plus r with ⟨hb,hc⟩
  omega

theorem peak_balance (r : Nat) :
    countB (peak r) = countC (peak r) + (r+1) := by
  induction r with
  | zero => decide
  | succ r ih =>
      have hf := frame_balance_one r
      simp [peak, countB, countC, List.count_append] at *
      omega

theorem peak_weight (r : Nat) :
    prefixWeight (peak r) = (r+1)/8 := by
  have h := peak_balance r
  unfold prefixWeight
  omega

/-- Defect weights in the exact abstract frame schedule are unbounded.  This
    rules out upgrading the finite maximum-weight-two observations to a global
    bounded-weight invariant. -/
theorem prefixWeight_unbounded (t : Nat) :
    ∃ p s, frame (8*t) = p ++ s ∧ prefixWeight p = t := by
  obtain ⟨s, hs⟩ := peak_prefix (8*t)
  refine ⟨peak (8*t), s, hs, ?_⟩
  rw [peak_weight]
  omega

/-- Second-right-run length carried by a rank-r normal-A action. -/
def normalB (r : Nat) : Nat := 2^(r+4) - 3

theorem pow_ge16 (r : Nat) : 16 ≤ 2^(r+4) := by
  have h : 2^4 ≤ 2^(r+4) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  simpa using h

theorem normalB_ge6 (r : Nat) : 6 ≤ normalB r := by
  unfold normalB
  have hp := pow_ge16 r
  omega

/-- The formerly empirical normal-A residue guard is forced by frame rank. -/
theorem normalB_mod8 (r : Nat) : normalB r % 8 = 5 := by
  unfold normalB
  have hp := pow_ge16 r
  have hpow : 2^(r+4) % 8 = 0 := by
    rw [show r+4 = 3 + (r+1) by omega, Nat.pow_add]
    simp
  omega

/-- A rank-r frame is born from normal A with b = 2^(r+4)-3:
    its low runway is b-6. -/
theorem frame_initial_low (r : Nat) :
    lowRemaining r [] = normalB r - 6 := by
  unfold lowRemaining normalB countB countC
  simp [Nat.pow_succ]
  omega

/-- The corresponding high runway is 2*b-11. -/
theorem frame_initial_high (r : Nat) :
    highRemaining r [] = 2 * normalB r - 11 := by
  unfold highRemaining normalB countB countC
  simp [Nat.pow_succ]
  omega

/-- A whole frame consumes both related runways exactly and closes with zero
    defect weight.  Thus recursive frames can be popped without a residual
    arithmetic side condition once their schedule is established. -/
theorem frame_closes (r : Nat) :
    lowRemaining r (frame r) = 0 ∧
    highRemaining r (frame r) = 0 ∧
    prefixWeight (frame r) = 0 := by
  have hl := lowRemaining_eq_suffixCost r (p := frame r) (s := []) (by simp)
  have hh := highRemaining_eq_suffixCost r (p := frame r) (s := []) (by simp)
  have hb := frame_balance_one r
  constructor
  · simpa [lowCost, countB, countC] using hl
  constructor
  · simpa [highCost, countB, countC] using hh
  · unfold prefixWeight
    omega

#print axioms next_B_weight_update
#print axioms next_C_weight_update
#print axioms normalB_ge6
#print axioms normalB_mod8
#print axioms frame_succ_refine
#print axioms frame_initial_low
#print axioms frame_initial_high
#print axioms frame_closes
#print axioms walk_frame
#print axioms frame_prefix_ballot
#print axioms frame_prefix_defect
#print axioms next_B_guards
#print axioms next_C_guards
#print axioms next_C_residue7_weight_positive
#print axioms prefixWeight_unbounded

end BB6.Agent1Raw56.LE17557FrameSchedule
