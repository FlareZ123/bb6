import SourceExactF424Core

/-!
# F424 exact primitive-cost lift for the initial MItem acceleration

This lifts the already source-checked mode-specific BB/DL/CB primitive
witnesses to the upstream MItem-level stepElemM transition used by
runElemFast. It is a draft until the exact import closure is Lean-compiled.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine

namespace BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution

abbrev MState := SymMode × List MItem × List MItem

/-- F424's exact primitive charge for one source MItem transition. -/
def costElemM424 : MState → Nat
  | (.BB, [], _) => 1
  | (.BB, .zero :: _, _) => 1
  | (.BB, .run 0 :: _, _) => 8
  | (.BB, .run 1 :: _, _) => 3
  | (.BB, .run 2 :: _, _) => 5
  | (.BB, .run 3 :: _, _) => 9
  | (.BB, .run (d + 4) :: _, _) => 9
  | (.DL, .zero :: _, _) => 0
  | (.DL, .run 0 :: _, _) => 1
  | (.DL, .run 1 :: _, _) => 3
  | (.DL, .run 2 :: _, .run d0 :: _) => 3 * d0 + 22
  | (.CB, _, []) => 2
  | (.CB, _, .zero :: _) => 2
  | (.CB, _, .run 0 :: []) => 3
  | (.CB, _, .run 0 :: .zero :: _) => 3
  | (.CB, _, .run 0 :: .run 0 :: _) => 6
  | (.CB, _, .run 0 :: .run (d2 + 1) :: _) => 3 * d2 + 21
  | (.CB, _, .run 1 :: _) => 3
  | (.CB, _, .run 2 :: _) => 5
  | (.CB, _, .run (d + 3) :: _) => 5
  | _ => 0

/-- Every MItem-level stepElemM branch is an exact original-TM run.
    The only zero-cost branches are stutters or the symbolic HALT marker,
    whose evalM image is the already-halting DL configuration. -/
theorem sourceElemM424_exact (s : MState) :
    ReachesIn target_tm (costElemM424 s)
      (evalM target_tm s)
      (evalM target_tm (stepElemM s)) := by
  rcases s with ⟨mode, L, R⟩
  cases mode with
  | BB =>
    cases L with
    | nil =>
      simpa [costElemM424, stepElemM, strictMList_eq, evalM] using
        step_BB_nil_exact R
    | cons t L1 =>
      cases t with
      | zero =>
        simpa [costElemM424, stepElemM, strictMList_eq, evalM] using
          step_BB_zero_exact L1 R
      | run d =>
        rcases d with _ | _ | _ | _ | d
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run0_exact L1 R
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run1_exact L1 R
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run2_exact L1 R
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run3_exact L1 R
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run_ge4_exact d L1 R
  | DL =>
    cases L with
    | nil => rfl
    | cons t L1 =>
      cases t with
      | zero => rfl
      | run d =>
        rcases d with _ | _ | _ | d
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_DL_run0_exact L1 R
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_DL_run1_exact L1 R
        · cases R with
          | nil => rfl
          | cons rt R1 =>
            cases rt with
            | zero => rfl
            | run d0 =>
              simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq,
                prependZeroM_eq, evalM] using
                step_DL_run2_exact d0 L1 R1
        · rfl
  | CB =>
    cases R with
    | nil =>
      simpa [costElemM424, stepElemM, strictMList_eq, evalM] using
        step_CB_nil_exact L
    | cons t R1 =>
      cases t with
      | zero =>
        simpa [costElemM424, stepElemM, strictMList_eq, evalM] using
          step_CB_zero_exact L R1
      | run d =>
        rcases d with _ | _ | _ | d
        · cases R1 with
          | nil =>
            simpa [costElemM424, stepElemM, strictMList_eq, evalM] using
              step_CB_run0_nil_exact L
          | cons t2 R2 =>
            cases t2 with
            | zero =>
              simpa [costElemM424, stepElemM, strictMList_eq, evalM] using
                step_CB_run0_zero_exact L R2
            | run d2 =>
              rcases d2 with _ | d2
              · simpa [costElemM424, stepElemM, strictMList_eq, evalM] using
                  step_CB_run0_run0_exact L R2
              · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq,
                  prependZeroM_eq, evalM] using
                  step_CB_run0_run_pos_exact d2 L R2
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_CB_run1_exact L R1
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_CB_run2_exact L R1
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_CB_run_ge3_exact d L R1
  | HALT => rfl

/-- Exact primitive cost of n successive source stepElemM transitions. -/
def costIterM424 : Nat → MState → Nat
  | 0, _ => 0
  | n + 1, s => costElemM424 s + costIterM424 n (stepElemM s)

theorem costIterM424_exact_reaches (n : Nat) (s : MState) :
    multiStep target_tm (evalM target_tm s) (costIterM424 n s) =
      some (evalM target_tm (iterStep stepElemM n s)) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change multiStep target_tm (evalM target_tm s)
      (costElemM424 s + costIterM424 n (stepElemM s)) =
        some (evalM target_tm (iterStep stepElemM n (stepElemM s)))
    exact multiStep_trans (sourceElemM424_exact s) (ih (stepElemM s))


/-- Iterating a transition in two nested blocks is equivalent to one
    iteration with the sum of the block lengths. -/
theorem iterStep_add {α : Type} (f : α → α) (n m : Nat) (s : α) :
    iterStep f (n + m) s = iterStep f m (iterStep f n s) := by
  induction n generalizing s with
  | zero => simp [iterStep]
  | succ n ih => simp [Nat.succ_add, iterStep, ih]

theorem iterStep_comp {α : Type} (f : α → α) (a b : Nat) (s : α) :
    iterStep f a (iterStep f b s) = iterStep f (a + b) s := by
  simpa [Nat.add_comm] using (iterStep_add f b a s).symm

theorem iterStep_repeat {α : Type} (f : α → α) (n m : Nat) (s : α) :
    iterStep (iterStep f n) m s = iterStep f (n * m) s := by
  induction m generalizing s with
  | zero => simp [iterStep]
  | succ m ih =>
    simp only [iterStep]
    calc
      iterStep (iterStep f n) m (iterStep f n s)
          = iterStep f (n * m) (iterStep f n s) := ih (iterStep f n s)
      _ = iterStep f (n * m + n) s := iterStep_comp f (n * m) n s
      _ = iterStep f (n * (m + 1)) s := by rw [Nat.mul_succ]

/-- The upstream runElemFast nesting is exactly 1+16b+256c+4096d
    elementary MItem transitions. -/
theorem runElemFast_eq_iterStep (a b c d : Nat) (s : MState) :
    runElemFast a b c d s =
      iterStep stepElemM (a + 16 * b + 256 * c + 4096 * d) s := by
  simp [runElemFast, stepElem16, stepElem256, stepElem4096,
    iterStep_repeat, iterStep_comp, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

def startF424M : MState := (.CB, [], [.run 1, .run 0])

theorem runElemFast424_exact_reaches :
    multiStep target_tm (evalM target_tm startF424M)
      (costIterM424 19217 startF424M) =
      some (evalM target_tm (runElemFast 1 1 11 4 startF424M)) := by
  rw [runElemFast_eq_iterStep]
  norm_num
  exact costIterM424_exact_reaches 19217 startF424M


/-- Exact source checkpoint used by the upstream F424 halting certificate. -/
def initSymCyc3_F424 : SymMode × List SymTok × List SymTok :=
  (.CB,
    [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1),
      .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 0), .item .zero, .item (.run 1), .repB1 46, .item (.run 0)],
    [.item (.run 79), .item (.run 0), .item (.run 1), .item .zero,
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1)])

set_option maxRecDepth 200000 in
theorem runElemFast424_eq_initSymCyc3 :
    runElemFast 1 1 11 4 startF424M =
      (initSymCyc3_F424.1, encSymL initSymCyc3_F424.2.1,
        encSymR initSymCyc3_F424.2.2) := by
  decide +kernel

theorem blankToInitSymCyc3_exact_reaches :
    multiStep target_tm (init ([] : List (Fin 2)))
      (18 + costIterM424 19217 startF424M) =
      some (evalSym target_tm initSymCyc3_F424) := by
  rw [blankToRunElemFast424_exact_reaches, runElemFast424_eq_initSymCyc3]
  rfl

#print axioms sourceElemM424_exact
#print axioms costIterM424_exact_reaches

end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution


/-- Maximum run counter on an MItem stack; zero markers do not contribute. -/
def maxRunMList : List MItem → Nat
  | [] => 0
  | .zero :: xs => maxRunMList xs
  | .run d :: xs => max d (maxRunMList xs)

theorem maxRunMList_bumpM_le (xs : List MItem) :
    maxRunMList (bumpM xs) ≤ maxRunMList xs + 1 := by
  cases xs with
  | nil => simp [bumpM, maxRunMList]
  | cons x xs =>
    cases x with
    | zero => simp [bumpM, maxRunMList]
    | run d =>
      simp [bumpM, strictNat_eq, maxRunMList]
      omega

theorem maxRunMList_tail_le (x : MItem) (xs : List MItem) :
    maxRunMList xs ≤ maxRunMList (x :: xs) := by
  cases x <;> simp [maxRunMList] <;> omega

/-- The right-hand run maximum grows by at most one under every source
    MItem transition. Only the DL-run2 and CB-run0/positive-run costs depend
    on a run counter on this side, so this is the needed prefix invariant. -/
theorem maxRunMRight_stepElemM_le (s : MState) :
    maxRunMList (stepElemM s).2.2 ≤ maxRunMList s.2.2 + 1 := by
  rcases s with ⟨mode, L, R⟩
  cases mode with
  | BB =>
    cases L with
    | nil =>
      simpa [stepElemM, strictMList_eq, maxRunMList] using
        maxRunMList_bumpM_le R
    | cons t L1 =>
      cases t with
      | zero =>
        simpa [stepElemM, strictMList_eq, maxRunMList] using
          maxRunMList_bumpM_le R
      | run d =>
        rcases d with _ | _ | _ | _ | d
        · simp [stepElemM, strictMList_eq, maxRunMList]
          omega
        · simpa [stepElemM, strictMList_eq, maxRunMList] using
            maxRunMList_bumpM_le R
        · simpa [stepElemM, strictMList_eq, maxRunMList] using
            maxRunMList_bumpM_le R
        · simpa [stepElemM, strictMList_eq, maxRunMList] using
            maxRunMList_bumpM_le R
        · simpa [stepElemM, strictMList_eq, strictNat_eq, maxRunMList] using
            maxRunMList_bumpM_le R
  | DL =>
    cases L with
    | nil => simp [stepElemM, maxRunMList]
      <;> omega
    | cons t L1 =>
      cases t with
      | zero => simp [stepElemM, maxRunMList]
        <;> omega
      | run d =>
        rcases d with _ | _ | _ | d
        · simpa [stepElemM, strictMList_eq, maxRunMList] using
            maxRunMList_bumpM_le R
        · simpa [stepElemM, strictMList_eq, maxRunMList] using
            maxRunMList_bumpM_le R
        · cases R with
          | nil => simp [stepElemM, maxRunMList]
            <;> omega
          | cons rt R1 =>
            cases rt with
            | zero => simp [stepElemM, maxRunMList]
              <;> omega
            | run d0 =>
              simp [stepElemM, strictMList_eq, strictNat_eq, maxRunMList]
              omega
        · simp [stepElemM, maxRunMList]
          <;> omega
  | CB =>
    cases R with
    | nil =>
      simp [stepElemM, strictMList_eq, maxRunMList]
      omega
    | cons t R1 =>
      cases t with
      | zero =>
        simpa [stepElemM, strictMList_eq, maxRunMList] using
          maxRunMList_bumpM_le R1
      | run d =>
        rcases d with _ | _ | _ | d
        · cases R1 with
          | nil =>
            simp [stepElemM, strictMList_eq, maxRunMList]
            omega
          | cons t2 R2 =>
            cases t2 with
            | zero =>
              simp [stepElemM, strictMList_eq, maxRunMList]
              omega
            | run d2 =>
              rcases d2 with _ | d2
              · simp [stepElemM, strictMList_eq, maxRunMList]
                omega
              · simp [stepElemM, strictMList_eq, strictNat_eq, maxRunMList]
                omega
        · simp [stepElemM, strictMList_eq, maxRunMList]
          omega
        · simp [stepElemM, strictMList_eq, maxRunMList]
          omega
        · simp [stepElemM, strictMList_eq, strictNat_eq, maxRunMList]
          omega
  | HALT => simp [stepElemM, maxRunMList]
    <;> omega

/-- The one-step primitive charge is at most three times the current
    right-side maximum plus 22. The only unbounded branches are DL/run2 and
    CB/run0 followed by a positive run; both consume their parameter from R. -/
theorem costElemM424_le (s : MState) :
    costElemM424 s ≤ 3 * maxRunMList s.2.2 + 22 := by
  rcases s with ⟨mode, L, R⟩
  cases mode with
  | BB =>
    cases L with
    | nil => simp [costElemM424, maxRunMList] <;> omega
    | cons t L1 =>
      cases t with
      | zero => simp [costElemM424, maxRunMList] <;> omega
      | run d =>
        rcases d with _ | _ | _ | _ | d <;>
          simp [costElemM424, maxRunMList] <;> omega
  | DL =>
    cases L with
    | nil => simp [costElemM424, maxRunMList] <;> omega
    | cons t L1 =>
      cases t with
      | zero => simp [costElemM424, maxRunMList] <;> omega
      | run d =>
        rcases d with _ | _ | _ | d
        · simp [costElemM424, maxRunMList] <;> omega
        · simp [costElemM424, maxRunMList] <;> omega
        · cases R with
          | nil => simp [costElemM424, maxRunMList] <;> omega
          | cons rt R1 =>
            cases rt with
            | zero => simp [costElemM424, maxRunMList] <;> omega
            | run d0 => simp [costElemM424, maxRunMList] <;> omega
        · simp [costElemM424, maxRunMList] <;> omega
  | CB =>
    cases R with
    | nil => simp [costElemM424, maxRunMList] <;> omega
    | cons t R1 =>
      cases t with
      | zero => simp [costElemM424, maxRunMList] <;> omega
      | run d =>
        rcases d with _ | _ | _ | d
        · cases R1 with
          | nil => simp [costElemM424, maxRunMList] <;> omega
          | cons t2 R2 =>
            cases t2 with
            | zero => simp [costElemM424, maxRunMList] <;> omega
            | run d2 =>
              rcases d2 with _ | d2
              · simp [costElemM424, maxRunMList] <;> omega
              · simp [costElemM424, maxRunMList] <;> omega
        · simp [costElemM424, maxRunMList] <;> omega
        · simp [costElemM424, maxRunMList] <;> omega
        · simp [costElemM424, maxRunMList] <;> omega
  | HALT => simp [costElemM424, maxRunMList]

theorem maxRunMRight_iterStep_le (n : Nat) (s : MState) :
    maxRunMList (iterStep stepElemM n s).2.2 ≤ maxRunMList s.2.2 + n := by
  induction n generalizing s with
  | zero => simp [iterStep]
  | succ n ih =>
    simp only [iterStep]
    calc
      maxRunMList (iterStep stepElemM n (stepElemM s)).2.2
          ≤ maxRunMList (stepElemM s).2.2 + n := ih (stepElemM s)
      _ ≤ maxRunMList s.2.2 + 1 + n :=
        Nat.add_le_add_right (maxRunMRight_stepElemM_le s) n
      _ = maxRunMList s.2.2 + (n + 1) := by omega

/-- Coarse but fully source-linked bound for any finite initial MItem run. -/
theorem costIterM424_le (n : Nat) (s : MState) :
    costIterM424 n s ≤
      n * (3 * (maxRunMList s.2.2 + n) + 22) := by
  induction n generalizing s with
  | zero => simp [costIterM424]
  | succ n ih =>
    let C := 3 * (maxRunMList s.2.2 + (n + 1)) + 22
    have hcost : costElemM424 s ≤ C := by
      have h := costElemM424_le s
      dsimp [C]
      omega
    have hmax := maxRunMRight_stepElemM_le s
    have harg :
        3 * (maxRunMList (stepElemM s).2.2 + n) + 22 ≤ C := by
      dsimp [C]
      omega
    have hih : costIterM424 n (stepElemM s) ≤ n * C := by
      calc
        costIterM424 n (stepElemM s)
            ≤ n * (3 * (maxRunMList (stepElemM s).2.2 + n) + 22) :=
              ih (stepElemM s)
        _ ≤ n * C := Nat.mul_le_mul_left n harg
    change costElemM424 s + costIterM424 n (stepElemM s) ≤ (n + 1) * C
    calc
      _ ≤ C + n * C := Nat.add_le_add hcost hih
      _ = n * C + C := Nat.add_comm _ _
      _ = (n + 1) * C := by rw [Nat.succ_mul]



/-- The 19,217-step F424 MItem prefix costs less than 2^31 primitive
    transitions, including the exact machine-specific source charges. -/
theorem costIterM424_f424_prefix_lt_two31 :
    costIterM424 19217 startF424M < 2 ^ 31 := by
  apply lt_of_le_of_lt (costIterM424_le 19217 startF424M)
  norm_num [startF424M, maxRunMList]


/-- Exact computed primitive cost of the 19,217-step F424 MItem prefix.
    This agrees with the independent JS replay; the proof is kernel reduction. -/
set_option maxRecDepth 200000 in
theorem costIterM424_f424_prefix_eq_164368 :
    costIterM424 19217 startF424M = 164368 := by
  decide +kernel

theorem blankToInitSymCyc3_cost_eq_164386 :
    18 + costIterM424 19217 startF424M = 164386 := by
  rw [costIterM424_f424_prefix_eq_164368]
  norm_num

theorem blankToInitSymCyc3_exact_164386 :
    multiStep target_tm (init ([] : List (Fin 2))) 164386 =
      some (evalSym target_tm initSymCyc3_F424) := by
  simpa [costIterM424_f424_prefix_eq_164368] using
    blankToInitSymCyc3_exact_reaches

#print axioms costIterM424_f424_prefix_eq_164368
#print axioms blankToInitSymCyc3_exact_164386


/-- The source runElemFast prefix from the F424 CB entry state is reached
    within 2^31 primitive TM transitions. -/
theorem runElemFast424_within_two31 :
    ∃ n : Nat, n < 2 ^ 31 ∧
      multiStep target_tm (evalM target_tm startF424M) n =
        some (evalM target_tm (runElemFast 1 1 11 4 startF424M)) := by
  exact ⟨costIterM424 19217 startF424M,
    costIterM424_f424_prefix_lt_two31,
    runElemFast424_exact_reaches⟩


/-- The blank-tape F424 configuration reaches its CB entry state in 18
    original-machine transitions. The existing stepWithin tactic expands
    and checks this short source-table prefix. -/
theorem initToCB424_exact :
    ReachesIn target_tm 18 (init ([] : List (Fin 2)))
      (evalM target_tm startF424M) := by
  executeWithin 18
  finishWithin

theorem blankToRunElemFast424_exact_reaches :
    multiStep target_tm (init ([] : List (Fin 2)))
      (18 + costIterM424 19217 startF424M) =
      some (evalM target_tm (runElemFast 1 1 11 4 startF424M)) := by
  exact multiStep_trans initToCB424_exact runElemFast424_exact_reaches

theorem blankToRunElemFast424_within_two31 :
    ∃ n : Nat, n < 2 ^ 31 ∧
      multiStep target_tm (init ([] : List (Fin 2))) n =
        some (evalM target_tm (runElemFast 1 1 11 4 startF424M)) := by
  refine ⟨18 + costIterM424 19217 startF424M, ?_, blankToRunElemFast424_exact_reaches⟩
  have h := costIterM424_f424_prefix_lt_two31
  omega

#print axioms runElemFast424_exact_reaches
#print axioms costIterM424_f424_prefix_lt_two31
#print axioms runElemFast424_within_two31
#print axioms maxRunMRight_stepElemM_le
#print axioms costElemM424_le
#print axioms costIterM424_le
#print axioms initToCB424_exact
#print axioms blankToRunElemFast424_exact_reaches
#print axioms blankToRunElemFast424_within_two31
