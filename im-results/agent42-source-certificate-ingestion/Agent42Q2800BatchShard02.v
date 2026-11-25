From BusyCoq Require Import Agent42Q2800BatchData.
From Coq Require Import List Bool.

(* Balanced shard 2/5; original source-tree rows: 1, 4, 7, 9, 12, 14, 15, 21, 28, 32, 37, 43, 45, 47, 49, 54, 55, 58, 60, 61, 66, 69, 71, 75, 81, 84, 86, 87, 93.
   The VM proof is isolated so make -j 2 can check independent groups in parallel. *)
Theorem q2800_trees_shard02_checked :
  forallb (q2800_tree_check 1000006) q2800_trees_shard02 = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Print Assumptions q2800_trees_shard02_checked.
