From BusyCoq Require Import Agent42Q2800BatchData.
From Coq Require Import List Bool.

(* Balanced shard 4/5; original source-tree rows: 27, 38, 39.
   The VM proof is isolated so make -j 2 can check independent groups in parallel. *)
Theorem q2800_trees_shard04_checked :
  forallb (q2800_tree_check 1000006) q2800_trees_shard04 = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Print Assumptions q2800_trees_shard04_checked.
