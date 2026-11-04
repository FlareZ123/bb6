import S4SourceShape
import BusyBeaver.BB6.Accelerations.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF

namespace S4NativeCompact

private abbrev M :=
  BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF

def unwrap : M.HighLevelState → Nat × List Nat
  | .C a L => (a,L)

theorem bumpN_eq (k : Nat) (L : List Nat) :
    BusyBeaver.Stack.bumpHeadBy k L = S4SourceShape.bumpN k L := by
  induction k generalizing L with
  | zero =>
      cases L <;> rfl
  | succ k ih =>
      have hstep : S4SourceShape.bumpN (k+1) L =
          S4SourceShape.bumpN k (BusyBeaver.Stack.bumpHead L) := by
        cases L with
        | nil =>
            cases k <;> simp [S4SourceShape.bumpN, BusyBeaver.Stack.bumpHead] <;> omega
        | cons b S =>
            cases k <;> simp [S4SourceShape.bumpN, BusyBeaver.Stack.bumpHead] <;> omega
      rw [BusyBeaver.Stack.bumpHeadBy, ih]
      exact hstep.symm

theorem bump2_eq (L : List Nat) :
    BusyBeaver.Stack.bumpHead (BusyBeaver.Stack.bumpHead L) =
      S4SourceShape.bumpN 2 L := by
  cases L <;> rfl

theorem transfer_eq (a : Nat) (L R : List Nat) :
    unwrap (M.transferHL a L R) = S4SourceShape.transferHL a L R := by
  rfl

theorem epoch_eq (L : List Nat) :
    ∀ (a : Nat) (R : List Nat),
      (M.stepEpoch a L R).map unwrap =
        S4SourceShape.epoch a L R := by
  induction L with
  | nil =>
      intro a
      induction a using Nat.strongRecOn with
      | ind a ih =>
          intro R
          rw [M.stepEpoch, S4SourceShape.epoch]
          simp only [↓reduceIte]
          rw [bumpN_eq]
          by_cases ha : a ≤ 1
          · simp [ha]
          · by_cases he : a % 2 = 0
            · simp [ha, he, transfer_eq, bump2_eq]
            · simp only [ha, he, ↓reduceIte]
              exact ih (a/2) (by omega) (0 :: S4SourceShape.bumpN (a/2) R)
  | cons b L ih =>
      intro a R
      rw [M.stepEpoch, S4SourceShape.epoch]
      simp only [List.cons_ne_nil, ↓reduceIte, List.headD_cons, List.tail_cons]
      rw [bumpN_eq]
      by_cases he : a % 2 = 0
      · simp [he, transfer_eq, bump2_eq]
      · simp only [he, ↓reduceIte]
        exact ih (b+a/2+1) (0::S4SourceShape.bumpN (a/2) R)

theorem compact_exact_native_epoch (T : List Nat) :
    ((M.stepEpoch 27 (S4SourceShape.bumpN 31 T) [0,6,5,3,1]).map
       (fun s => _root_.bump17 ((unwrap s).2.drop 4))) =
      _root_.compactNext T := by
  rw [show
    (M.stepEpoch 27 (S4SourceShape.bumpN 31 T) [0,6,5,3,1]).map
       (fun s => _root_.bump17 ((unwrap s).2.drop 4)) =
    ((M.stepEpoch 27 (S4SourceShape.bumpN 31 T) [0,6,5,3,1]).map unwrap).map
       (fun p => _root_.bump17 (p.2.drop 4)) by
         simp [Option.map_map, Function.comp_def]]
  rw [epoch_eq]
  exact S4SourceShape.sourceReduced_eq_compactNext T

#print axioms epoch_eq
#print axioms compact_exact_native_epoch
end S4NativeCompact
