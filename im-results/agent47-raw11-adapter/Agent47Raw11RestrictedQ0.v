From BusyCoq Require Import Enumerate62 Individual62 TC62 CTL62 Eqb
  Agent32SourceBackwards SourceResidualRoster.
From Coq Require Import List Bool NArith Lia Strings.String.
Import ListNotations TNF_Node.
Open Scope nat_scope.
Open Scope string_scope.

(* Raw11 is the source-root branch A0=1RB, B0=1RC, C0=0LA.  The
   metadata (9 holes, next unused state D) is the exact state after the
   first two breadth-first source expansions from root_1RB. *)
Definition raw11_parent : TM :=
  TM_from_str "1RB---_1RC---_0LA---_------_------_------".
Definition raw11_node : T := Build_T raw11_parent 9 3.

Definition raw11_q0_restriction : SearchQueue :=
  (filter (source_roster_covers [raw11_parent]) (fst q_0),
   filter (source_roster_covers [raw11_parent]) (snd q_0)).

Definition raw11_local_q0 : SearchQueue :=
  SearchQueue_upds_bfs decider
    (SearchQueue_upds_bfs decider ([raw11_node], [])).

Theorem raw11_node_metadata :
  raw11_node.(num_undef_trans) = 9 /\ raw11_node.(min_unused_state) = 3.
Proof. split; reflexivity. Qed.

(* This is the missing partition edge: restricting the actual pinned q_0
   frontier to Raw11 must equal replaying the same two remaining BFS rounds
   from the Raw11 branch itself. *)
Theorem raw11_q0_restriction_exact :
  raw11_q0_restriction = raw11_local_q0.
Proof. vm_compute. reflexivity. Qed.

(* If all residual nodes in the restricted frontier are safe, the two
   backwards BFS steps recover safety of the complete Raw11 cylinder. *)
Theorem raw11_safe_from_restricted_q0 (Safe : T -> Prop) :
  (forall x, match decider (tm x) with
    | TC62.TM.Halt h => Forall Safe (expand' x h) -> Safe x
    | TC62.TM.NonHalt => Safe x
    | TC62.TM.Unknown => True
    end) ->
  safeQ Safe raw11_q0_restriction ->
  Safe raw11_node.
Proof.
  intros Hlocal Hq.
  rewrite raw11_q0_restriction_exact in Hq.
  apply (source_bfs_round_backwards Safe decider Hlocal) in Hq.
  apply (source_bfs_round_backwards Safe decider Hlocal) in Hq.
  destruct Hq as [Hnode _].
  inversion Hnode; subst; assumption.
Qed.

Print Assumptions raw11_node_metadata.
Print Assumptions raw11_q0_restriction_exact.
Print Assumptions raw11_safe_from_restricted_q0.
