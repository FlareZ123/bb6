From BusyCoq Require Import Agent42Q2800BatchData.
From Coq Require Import List Bool.

(* Balanced shard 3/5; original source-tree rows: 2, 8, 10, 11, 13, 16, 18, 20, 26, 31, 34, 42, 44, 46, 51, 53, 56, 57, 59, 63, 64, 67, 68, 73, 76, 77, 85, 89, 91, 94.
   The VM proof is isolated so make -j 2 can check independent groups in parallel. *)
Theorem q2800_trees_shard03_checked :
  forallb (q2800_tree_check 1000006) q2800_trees_shard03 = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Print Assumptions q2800_trees_shard03_checked.
