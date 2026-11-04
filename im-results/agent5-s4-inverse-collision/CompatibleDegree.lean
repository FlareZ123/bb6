import CompatibleCore
import Lean.Elab.Tactic.Omega

namespace S4Collision

def compatibleTarget (n : Nat) : List Nat :=
  [80,150] ++ List.replicate (n+3) 106 ++ [20]

def compatibleParent (n i : Nat) : List Nat :=
  [82,237,62] ++ List.replicate i 106 ++ [101,2] ++ List.replicate (n-i) 106 ++ [20]

def count106 : List Nat → Nat
  | [] => 0
  | 106::S => 1 + count106 S
  | _::_ => 0

theorem count106_rep (k m : Nat) :
  count106 (List.replicate k 106 ++ [101,2] ++ List.replicate m 106 ++ [20]) = k := by
  induction k with
  | zero => simp [count106]
  | succ k ih =>
    simpa [count106, List.replicate_succ, List.cons_append, Nat.add_comm] using congrArg Nat.succ ih

theorem compatible_marker (n i : Nat) :
    count106 ((compatibleParent n i).drop 3) = i := by
  simpa [compatibleParent, List.drop] using count106_rep i (n-i)

theorem compatible_parent_injective (n i j : Nat)
    (e : compatibleParent n i = compatibleParent n j) : i = j := by
  have h := congrArg (fun T => count106 (T.drop 3)) e
  simpa only [compatible_marker] using h

theorem compatible_parent_correct (n i : Nat) (hi : i ≤ n) :
    compactNext (compatibleParent n i) = some (compatibleTarget n) := by
  have e : i+(n-i)+3 = n+3 := by omega
  simpa [compatibleParent, compatibleTarget, e] using compatible_incoming i (n-i)

theorem compatible_target_halts (n : Nat) : compactNext (compatibleTarget n) = none := by
  exact compatible_danger (n+3)

theorem compatible_target_prefix (n : Nat) : (compatibleTarget n).take 2 = [80,150] := by
  simp [compatibleTarget]

theorem compatible_target_positive (n : Nat) :
    ∀ x ∈ compatibleTarget n, 0 < x := by
  intro x hx
  simp [compatibleTarget, List.mem_append, List.mem_replicate] at hx
  omega

theorem compatible_parent_positive (n i : Nat) :
    ∀ x ∈ compatibleParent n i, 0 < x := by
  intro x hx
  simp [compatibleParent, List.mem_append, List.mem_replicate] at hx
  omega

theorem compatible_halting_indegree (n : Nat) :
    ∃ (P : Nat → List Nat) (y : List Nat),
      y.take 2 = [80,150] ∧
      (∀ x ∈ y, 0 < x) ∧
      (∀ i, ∀ x ∈ P i, 0 < x) ∧
      S4SourceShape.sourceReduced y = none ∧
      (∀ i, i ≤ n → S4SourceShape.sourceReduced (P i) = some y) ∧
      (∀ i j, i ≤ n → j ≤ n → P i = P j → i = j) := by
  refine ⟨compatibleParent n, compatibleTarget n, compatible_target_prefix n,
    compatible_target_positive n, (fun i => compatible_parent_positive n i), ?_, ?_, ?_⟩
  · rw [compact_source_equivalence]; exact compatible_target_halts n
  · intro i hi
    rw [compact_source_equivalence]
    exact compatible_parent_correct n i hi
  · exact fun i j _ _ h => compatible_parent_injective n i j h

#print axioms compatible_halting_indegree
end S4Collision
