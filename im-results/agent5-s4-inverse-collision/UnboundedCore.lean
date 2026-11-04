import Collision
import Lean.Elab.Tactic.Omega

namespace S4Collision

theorem H201_loop (S : List Nat) :
  H 201 (100::S) = (H 201 S).map (100::·) := by
  simpa using odd_cons 100 100 S

theorem H201_replicate (k : Nat) (S : List Nat) :
  H 201 (List.replicate k 100 ++ S) =
    (H 201 S).map (fun U => List.replicate k 100 ++ U) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append]
    rw [H201_loop, ih]
    simp [Option.map_map, Function.comp_def]

theorem H201_terminal (S : List Nat) :
    H 201 (95::2::S) = some (100::100::100::S) := by
  simp [H, _root_.H]

theorem H125_terminal (S : List Nat) :
    H 125 (133::2::S) = some (62::100::100::S) := by
  simp [H, _root_.H]

theorem H125_many (k : Nat) (S : List Nat) :
    H 125 (138::(List.replicate k 100 ++ (95::2::S))) =
      some (62::(List.replicate (k+3) 100 ++ S)) := by
  have a : H 125 (138::(List.replicate k 100 ++ (95::2::S))) =
      (H 201 (List.replicate k 100 ++ (95::2::S))).map (62::·) := by
    simpa using odd_cons 62 138 (List.replicate k 100 ++ (95::2::S))
  rw [a,H201_replicate,H201_terminal]
  simp only [Option.map_some]
  congr 2
  change List.replicate k 100 ++ (List.replicate 3 100 ++ S) =
    List.replicate (k+3) 100 ++ S
  rw [←List.append_assoc, List.replicate_append_replicate]

theorem base_preimage (m : Nat) :
    compactNext ([80,133,2] ++ List.replicate m 100) =
      some ([79] ++ List.replicate (m+2) 100) := by
  simp only [List.cons_append, List.nil_append, compactNext, Nat.reduceAdd]
  rw [H125_terminal]
  simp [bumpBy, List.replicate_succ]

theorem loop_preimage (k m : Nat) :
    compactNext ([80,138] ++ List.replicate k 100 ++ [95,2] ++ List.replicate m 100) =
      some ([79] ++ List.replicate (k+m+3) 100) := by
  simp only [List.cons_append, List.nil_append, compactNext, Nat.reduceAdd]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [H125_many]
  simp [bumpBy, List.replicate_append_replicate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

#print axioms base_preimage
#print axioms loop_preimage
end S4Collision
