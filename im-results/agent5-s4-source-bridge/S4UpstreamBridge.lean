import S4Phase
import BusyBeaver.BB6.Accelerations.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF

namespace S4SourceBridge
def sourceRun : Nat → BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.HighLevelState → Option BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.HighLevelState
  | 0, s => some s
  | n + 1, s => (sourceRun n s).bind BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.highLevelNext

def unwrap : BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.HighLevelState → S4.State
  | .C a L => (a,L)

theorem bump_eq (L : List Nat) : BusyBeaver.Stack.bumpHead L = S4.bump L := by
  cases L <;> rfl

theorem bumpBy_eq (k : Nat) (L : List Nat) :
    BusyBeaver.Stack.bumpHeadBy k L = S4.bumpBy k L := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    simp only [BusyBeaver.Stack.bumpHeadBy, S4.bumpBy]
    rw [bump_eq]
    exact ih _

theorem transfer_eq (a : Nat) (L R : List Nat) :
    unwrap (BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.transferHL a L R) = S4.transfer a L R := by
  rfl

theorem epoch_eq (L : List Nat) :
  ∀ (a : Nat) (R : List Nat),
    (BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.stepEpoch a L R).map unwrap = S4.epoch a L R := by
  induction L with
  | nil =>
    intro a
    induction a using Nat.strongRecOn with
    | ind a ih =>
      intro R
      rw [BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.stepEpoch, S4.epoch]
      simp only [↓reduceIte]
      rw [bumpBy_eq]
      by_cases ha : a ≤ 1
      · simp [ha]
      · by_cases he : a % 2 = 0
        · simp [ha, he, transfer_eq, bump_eq]
        · simp only [ha, he, ↓reduceIte]
          exact ih (a/2) (by omega) (0 :: S4.bumpBy (a/2) R)
  | cons b L ih =>
    intro a R
    rw [BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.stepEpoch, S4.epoch]
    simp only [List.cons_ne_nil, ↓reduceIte, List.headD_cons, List.tail_cons]
    rw [bumpBy_eq]
    by_cases he : a % 2 = 0
    · simp [he, transfer_eq, bump_eq]
    · simp only [he, ↓reduceIte]
      exact ih (b+a/2+1) (0::S4.bumpBy (a/2) R)

theorem step_eq (s : BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.HighLevelState) :
  (BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.highLevelNext s).map unwrap = S4.highNext (unwrap s) := by
  cases s with
  | C a L => exact epoch_eq L a [0]

theorem run_eq (n : Nat) (s : BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.HighLevelState) :
  (sourceRun n s).map unwrap = S4.run n (unwrap s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((sourceRun n s).bind BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.highLevelNext).map unwrap =
      (S4.run n (unwrap s)).bind S4.highNext
    rw [← ih]
    cases h : sourceRun n s with
    | none => simp [h]
    | some t => simpa [h] using step_eq t

theorem halts_iff (s : BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.HighLevelState) :
 (∃ n, sourceRun n s = none) ↔ (∃ n, S4.run n (unwrap s) = none) := by
  constructor
  · rintro ⟨n, h⟩
    refine ⟨n, ?_⟩
    rw [← run_eq n s, h]
    rfl
  · rintro ⟨n, h⟩
    refine ⟨n, ?_⟩
    have heq := run_eq n s
    rw [h] at heq
    cases hr : sourceRun n s with
    | none => rfl
    | some t =>
      rw [hr] at heq
      simp at heq

theorem highLevelNext_eq (a : Nat) (L : List Nat) :
  (BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.highLevelNext (.C a L)).map unwrap = S4.epoch a L [0] :=
  epoch_eq L a [0]

theorem sourceRun_eq_iter (n : Nat) (s : BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.HighLevelState) :
    sourceRun n s =
    Function.iterate (Option.bind · BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.highLevelNext) n (some s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sourceRun, Function.iterate_succ_apply']
    rw [← ih]

theorem original_highLevel_halts_iff_model :
    BusyBeaver.CollatzHalts BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.highLevelNext
      BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.highLevelStart ↔
      (∃ n, S4.run n (3,[0]) = none) := by
  unfold BusyBeaver.CollatzHalts
  simp only [← sourceRun_eq_iter, Option.isNone_iff_eq_none]
  simpa [BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.highLevelStart, unwrap] using
    (halts_iff BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.highLevelStart)

theorem original_machine_halts_iff_model :
    BusyBeaver.IsHalt BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.target ↔
    (∃ n, S4.run n (3,[0]) = none) :=
  BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.isHalt_iff_highLevel_acceleration.trans
    original_highLevel_halts_iff_model

#print axioms S4SourceBridge.original_machine_halts_iff_model
#print axioms S4SourceBridge.original_highLevel_halts_iff_model
#print axioms S4SourceBridge.sourceRun_eq_iter
#print axioms S4SourceBridge.halts_iff
#print axioms S4SourceBridge.epoch_eq
#print axioms S4SourceBridge.highLevelNext_eq
end S4SourceBridge
