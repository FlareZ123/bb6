import HaltingFan
import Lean.Elab.Tactic.Omega

namespace S4Collision

theorem H125_end64 : H 125 [64] = none := by
  simp [H]

theorem danger_block64 (n : Nat) :
    compactNext ([80] ++ List.replicate n 62 ++ [64]) = none := by
  simp only [List.cons_append, List.nil_append, compactNext, Nat.reduceAdd]
  rw [H125_replicate62, H125_end64]
  simp

theorem incoming_block64 (k m : Nat) :
    compactNext ([82,61] ++ List.replicate k 62 ++ [57,2] ++ List.replicate m 62 ++ [64]) =
      some ([80] ++ List.replicate (k+m+3) 62 ++ [64]) := by
  simp only [List.cons_append, List.nil_append, compactNext, Nat.reduceAdd]
  rw [H127_start]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [H125_replicate62, H125_terminal62]
  simp [bumpBy]
  change List.replicate k 62 ++ (List.replicate 3 62 ++ (List.replicate m 62 ++ [64])) =
    List.replicate (k+m+3) 62 ++ [64]
  rw [←List.append_assoc, ←List.append_assoc]
  rw [List.replicate_append_replicate, List.replicate_append_replicate]
  simp only [show k+3+m=k+m+3 by omega]

def positiveTarget (n : Nat) : List Nat :=
  [80] ++ List.replicate (n+3) 62 ++ [64]

def positiveParent (n i : Nat) : List Nat :=
  [82,61] ++ List.replicate i 62 ++ [57,2] ++ List.replicate (n-i) 62 ++ [64]

theorem positive_target_members (n : Nat) :
    ∀ x ∈ positiveTarget n, 0 < x := by
  intro x hx
  simp [positiveTarget, List.mem_append, List.mem_replicate] at hx
  omega

theorem positive_parent_members (n i : Nat) :
    ∀ x ∈ positiveParent n i, 0 < x := by
  intro x hx
  simp [positiveParent, List.mem_append, List.mem_replicate] at hx
  omega

theorem count62_rep64 (k m : Nat) :
  count62 (List.replicate k 62 ++ [57,2] ++ List.replicate m 62 ++ [64]) = k := by
  induction k with
  | zero => simp [count62]
  | succ k ih =>
    simpa [count62, List.replicate_succ, List.cons_append, Nat.add_comm] using congrArg Nat.succ ih

theorem positive_marker (n i : Nat) :
    count62 ((positiveParent n i).drop 2) = i := by
  simpa [positiveParent, List.drop] using count62_rep64 i (n-i)

theorem positive_parent_injective (n i j : Nat)
    (e : positiveParent n i = positiveParent n j) : i = j := by
  have h := congrArg (fun T => count62 (T.drop 2)) e
  simpa only [positive_marker] using h

theorem positive_parent_correct (n i : Nat) (hi : i ≤ n) :
    compactNext (positiveParent n i) = some (positiveTarget n) := by
  have e : i+(n-i)+3 = n+3 := by omega
  simpa [positiveParent, positiveTarget, e] using incoming_block64 i (n-i)

theorem positive_target_halts (n : Nat) : compactNext (positiveTarget n) = none := by
  exact danger_block64 (n+3)

theorem unbounded_positive_halting_indegree (n : Nat) :
    ∃ (P : Nat → List Nat) (y : List Nat),
      (∀ x ∈ y, 0 < x) ∧
      (∀ i, ∀ x ∈ P i, 0 < x) ∧
      compactNext y = none ∧
      (∀ i, i ≤ n → compactNext (P i) = some y) ∧
      (∀ i j, i ≤ n → j ≤ n → P i = P j → i = j) := by
  refine ⟨positiveParent n, positiveTarget n, positive_target_members n,
    (fun i => positive_parent_members n i), positive_target_halts n, ?_, ?_⟩
  · exact fun i hi => positive_parent_correct n i hi
  · exact fun i j _ _ h => positive_parent_injective n i j h

#print axioms unbounded_positive_halting_indegree
end S4Collision
