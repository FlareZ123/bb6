import UnboundedCore
import Lean.Elab.Tactic.Omega

namespace S4Collision

def source1 (m : Nat) : List Nat := [80,133,2] ++ List.replicate m 100

def source2 (k m : Nat) : List Nat :=
  [80,138] ++ List.replicate k 100 ++ [95,2] ++ List.replicate m 100

def count100 : List Nat → Nat
  | [] => 0
  | 100::S => 1 + count100 S
  | _::_ => 0

theorem count100_rep (k m : Nat) :
  count100 (List.replicate k 100 ++ [95,2] ++ List.replicate m 100) = k := by
  induction k with
  | zero => simp [count100]
  | succ k ih =>
    have hi : count100 (List.replicate k 100 ++ 95::2::List.replicate m 100) = k := by
      simpa [List.append_assoc] using ih
    simpa [count100, List.replicate_succ, List.cons_append, Nat.add_comm] using congrArg Nat.succ hi

theorem source2_marker (k m : Nat) : count100 ((source2 k m).drop 2) = k := by
  simpa [source2, List.drop] using count100_rep k m

theorem source2_distinct (k k' m m' : Nat) (hk : k ≠ k') :
    source2 k m ≠ source2 k' m' := by
  intro h
  have e := congrArg (fun T => count100 (T.drop 2)) h
  rw [source2_marker,source2_marker] at e
  exact hk e

theorem source1_vs_source2 (m k m' : Nat) : source1 m ≠ source2 k m' := by
  intro h
  have e := congrArg (fun T : List Nat => (T.drop 1).head?) h
  simp [source1,source2] at e

def target (n : Nat) : List Nat := [79] ++ List.replicate (n+2) 100

def indexed (n i : Nat) : List Nat :=
  if i = 0 then source1 n else source2 (i-1) (n-i)

theorem indexed_correct (n i : Nat) (hi : i ≤ n) :
    compactNext (indexed n i) = some (target n) := by
  by_cases h : i = 0
  · subst i
    simpa [indexed, target, source1] using base_preimage n
  · have e : (i-1)+(n-i)+3 = n+2 := by omega
    simpa [indexed, h, target, source2, e] using loop_preimage (i-1) (n-i)

theorem indexed_injective (n i j : Nat) (_hi : i ≤ n) (_hj : j ≤ n)
    (heq : indexed n i = indexed n j) : i = j := by
  by_cases a : i = 0
  · by_cases b : j = 0
    · omega
    · have e : source1 n = source2 (j-1) (n-j) := by
        simpa [indexed, a, b] using heq
      exact False.elim ((source1_vs_source2 n (j-1) (n-j)) e)
  · by_cases b : j = 0
    · have e : source1 n = source2 (i-1) (n-i) := by
        simpa [indexed, a, b] using heq.symm
      exact False.elim ((source1_vs_source2 n (i-1) (n-i)) e)
    · have e : source2 (i-1) (n-i) = source2 (j-1) (n-j) := by
        simpa [indexed, a, b] using heq
      have d := congrArg (fun T => count100 (T.drop 2)) e
      rw [source2_marker, source2_marker] at d
      omega

theorem arbitrarily_many_distinct_preimages (n : Nat) :
    ∃ (P : Nat → List Nat) (y : List Nat),
      (∀ i, i ≤ n → compactNext (P i) = some y) ∧
      (∀ i j, i ≤ n → j ≤ n → P i = P j → i = j) := by
  refine ⟨indexed n, target n, ?_, ?_⟩
  · exact fun i hi => indexed_correct n i hi
  · exact fun i j hi hj heq => indexed_injective n i j hi hj heq

#print axioms arbitrarily_many_distinct_preimages
end S4Collision
