From BusyCoq Require Import Agent42Q2800BatchData.
From Coq Require Import List Bool.

(* Balanced shard 1/5; original source-tree rows: 3, 5, 6, 17, 19, 22, 23, 24, 25, 30, 33, 40, 41, 48, 50, 52, 62, 65, 70, 72, 74, 78, 79, 80, 82, 83, 88, 90, 92, 95.
   The VM proof is isolated so make -j 2 can check independent groups in parallel. *)
Theorem q2800_trees_shard01_checked :
  forallb (q2800_tree_check 1000006) q2800_trees_shard01 = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Print Assumptions q2800_trees_shard01_checked.
