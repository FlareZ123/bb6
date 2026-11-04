import UnboundedDegree
import Lean.Elab.Tactic.Omega

namespace S4Collision

theorem H125_loop62 (S : List Nat) :
  H 125 (62::S) = (H 125 S).map (62::·) := by
  simpa using odd_cons 62 62 S

theorem H125_replicate62 (k : Nat) (S : List Nat) :
  H 125 (List.replicate k 62 ++ S) =
    (H 125 S).map (fun U => List.replicate k 62 ++ U) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append]
    rw [H125_loop62, ih]
    simp [Option.map_map, Function.comp_def]

theorem H125_end : H 125 [0] = none := by
  simp [H, _root_.H]

theorem H125_terminal62 (S : List Nat) :
  H 125 (57::2::S) = some (62::62::62::S) := by
  simp [H, _root_.H]

theorem H127_start (S : List Nat) :
  H 127 (61::S) = (H 125 S).map (63::·) := by
  simpa using odd_cons 63 61 S

theorem danger_block (n : Nat) :
    compactNext ([80] ++ List.replicate n 62 ++ [0]) = none := by
  simp only [List.cons_append, List.nil_append, compactNext, Nat.reduceAdd]
  rw [H125_replicate62, H125_end]
  simp

theorem incoming_block (k m : Nat) :
    compactNext ([82,61] ++ List.replicate k 62 ++ [57,2] ++ List.replicate m 62 ++ [0]) =
      some ([80] ++ List.replicate (k+m+3) 62 ++ [0]) := by
  simp only [List.cons_append, List.nil_append, compactNext, Nat.reduceAdd]
  rw [H127_start]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [H125_replicate62, H125_terminal62]
  simp [bumpBy]
  change List.replicate k 62 ++ (List.replicate 3 62 ++ (List.replicate m 62 ++ [0])) =
    List.replicate (k+m+3) 62 ++ [0]
  rw [←List.append_assoc, ←List.append_assoc]
  rw [List.replicate_append_replicate, List.replicate_append_replicate]
  simpa only [show k+3+m=k+m+3 by omega]

def terminalTarget (n : Nat) : List Nat :=
  [80] ++ List.replicate (n+3) 62 ++ [0]

def terminalParent (n i : Nat) : List Nat :=
  [82,61] ++ List.replicate i 62 ++ [57,2] ++ List.replicate (n-i) 62 ++ [0]

def count62 : List Nat → Nat
  | [] => 0
  | 62::S => 1 + count62 S
  | _::_ => 0

theorem count62_rep (k m : Nat) :
  count62 (List.replicate k 62 ++ [57,2] ++ List.replicate m 62 ++ [0]) = k := by
  induction k with
  | zero => simp [count62]
  | succ k ih =>
    simpa [count62, List.replicate_succ, List.cons_append, Nat.add_comm] using congrArg Nat.succ ih

theorem parent_marker (n i : Nat) :
    count62 ((terminalParent n i).drop 2) = i := by
  simpa [terminalParent, List.drop] using count62_rep i (n-i)

theorem parent_injective (n i j : Nat)
    (e : terminalParent n i = terminalParent n j) : i = j := by
  have h := congrArg (fun T => count62 (T.drop 2)) e
  simpa only [parent_marker] using h

theorem parent_correct (n i : Nat) (hi : i ≤ n) :
    compactNext (terminalParent n i) = some (terminalTarget n) := by
  have e : i+(n-i)+3 = n+3 := by omega
  simpa [terminalParent, terminalTarget, e] using incoming_block i (n-i)

theorem terminal_halts (n : Nat) : compactNext (terminalTarget n) = none := by
  exact danger_block (n+3)

theorem unbounded_halting_indegree (n : Nat) :
    ∃ (P : Nat → List Nat) (y : List Nat),
      compactNext y = none ∧
      (∀ i, i ≤ n → compactNext (P i) = some y) ∧
      (∀ i j, i ≤ n → j ≤ n → P i = P j → i = j) := by
  refine ⟨terminalParent n, terminalTarget n, terminal_halts n, ?_, ?_⟩
  · exact fun i hi => parent_correct n i hi
  · exact fun i j _ _ h => parent_injective n i j h

#print axioms danger_block
#print axioms incoming_block
#print axioms unbounded_halting_indegree
end S4Collision
