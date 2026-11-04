import SourceTransfer
import Lean.Elab.Tactic.Omega

namespace S4Collision

theorem H213_loop106 (S : List Nat) :
  H 213 (106::S) = (H 213 S).map (106::·) := by
  simpa using odd_cons 106 106 S

theorem H213_replicate106 (k : Nat) (S : List Nat) :
  H 213 (List.replicate k 106 ++ S) =
    (H 213 S).map (fun U => List.replicate k 106 ++ U) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append]
    rw [H213_loop106, ih]
    simp [Option.map_map, Function.comp_def]

theorem H213_end20 : H 213 [20] = none := by
  simp [H, _root_.H]

theorem H213_terminal106 (S : List Nat) :
  H 213 (101::2::S) = some (106::106::106::S) := by
  simp [H, _root_.H]

theorem H125_start150 (S : List Nat) :
  H 125 (150::S) = (H 213 S).map (62::·) := by
  simpa using odd_cons 62 150 S

theorem H127_start150 (S : List Nat) :
  H 127 (237::62::S) = (H 213 S).map (fun U => 63::150::U) := by
  rw [odd_cons 63 237 (62::S)]
  rw [odd_cons 150 62 S]
  simp [Option.map_map, Function.comp_def]

theorem compatible_danger (n : Nat) :
  compactNext ([80,150] ++ List.replicate n 106 ++ [20]) = none := by
  simp only [List.cons_append, List.nil_append, compactNext, Nat.reduceAdd]
  rw [H125_start150, H213_replicate106, H213_end20]
  simp

theorem compatible_incoming (k m : Nat) :
    compactNext ([82,237,62] ++ List.replicate k 106 ++ [101,2] ++ List.replicate m 106 ++ [20]) =
      some ([80,150] ++ List.replicate (k+m+3) 106 ++ [20]) := by
  simp only [List.cons_append, List.nil_append, compactNext, Nat.reduceAdd]
  rw [H127_start150]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [H213_replicate106, H213_terminal106]
  simp [bumpBy]
  change List.replicate k 106 ++ (List.replicate 3 106 ++ (List.replicate m 106 ++ [20])) =
    List.replicate (k+m+3) 106 ++ [20]
  rw [←List.append_assoc, ←List.append_assoc]
  rw [List.replicate_append_replicate, List.replicate_append_replicate]
  simp only [show k+3+m=k+m+3 by omega]

#print axioms compatible_incoming
#print axioms compatible_danger
end S4Collision
