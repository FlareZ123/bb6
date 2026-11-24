From BusyCoq Require Import Enumerate62.
From Coq Require Import List NArith Lia Arith.PeanoNat.
Import ListNotations.

(* The census is a VM-checked equality of the original pinned source,
   not a count from a reimplementation. *)
Theorem agent32_q0_length :
  length (fst q_0) = 12820%nat.
Proof. vm_compute; reflexivity. Qed.

Theorem agent32_q0_holdout_empty : snd q_0 = [].
Proof. vm_compute; reflexivity. Qed.

Lemma agent32_q0_uniform_bool :
  forallb (fun x => Nat.eqb (TNF_Node.num_undef_trans x) 7) (fst q_0) = true.
Proof. vm_compute; reflexivity. Qed.

Theorem agent32_q0_uniform :
  forall x, In x (fst q_0) -> TNF_Node.num_undef_trans x = 7%nat.
Proof.
  intros x Hx.
  pose proof agent32_q0_uniform_bool as H.
  apply forallb_forall with (x:=x) in H; [apply Nat.eqb_eq; exact H|exact Hx].
Qed.

Lemma agent32_nth_error_firstn {A : Type} (xs : list A) n k :
  (k<n)%nat -> nth_error (firstn n xs) k = nth_error xs k.
Proof.
  revert n k; induction xs as [|x xs IH]; intros [|n] [|k] H; try lia; cbn; auto.
  apply IH; lia.
Qed.

Lemma agent32_nth_error_skipn {A : Type} (xs : list A) n k :
  nth_error (skipn n xs) k = nth_error xs (n+k).
Proof.
  revert xs; induction n as [|n IH]; intros xs.
  - reflexivity.
  - destruct xs as [|x xs].
    + destruct k; reflexivity.
    + cbn; apply IH.
Qed.

(* Explicit schedule: 129 chunks, starting at 0,100,...,12800.
   The final chunk has 20 nodes, and the first 128 have 100. *)
Theorem agent32_q0_chunk_cover (x : TNF_Node.T) :
  In x (fst q_0) ->
  exists i, (i<129)%nat /\ In x (fst (q_i (100*i) 100)).
Proof.
  intros H.
  apply In_nth_error in H.
  destruct H as [j Hj].
  assert (Hjlt : (j<12820)%nat).
  { rewrite <- agent32_q0_length.
    apply nth_error_Some; rewrite Hj; discriminate. }
  pose proof (Nat.div_mod j 100 ltac:(lia)) as Hdiv.
  pose proof (Nat.mod_upper_bound j 100 ltac:(lia)) as Hmod.
  exists (j/100)%nat.
  split.
  { apply Nat.div_lt_upper_bound; [lia|].
    eapply Nat.lt_trans; [exact Hjlt|].
    apply Nat.ltb_lt; vm_compute; reflexivity. }
  apply nth_error_In with (n:=(j mod 100)%nat).
  unfold q_i; cbn [fst].
  rewrite agent32_nth_error_firstn by exact Hmod.
  rewrite agent32_nth_error_skipn.
  replace (100 * (j / 100) + j mod 100)%nat with j by lia.
  exact Hj.
Qed.

Theorem agent32_q0_chunk_length i :
  (i < 129)%nat ->
  length (fst (q_i (100*i) 100)) = (if Nat.eqb i 128 then 20 else 100)%nat.
Proof.
  intros Hi.
  unfold q_i; cbn [fst].
  rewrite firstn_length, skipn_length, agent32_q0_length.
  destruct (Nat.eqb i 128) eqn:E.
  - apply Nat.eqb_eq in E; subst; reflexivity.
  - apply Nat.eqb_neq in E.
    apply Nat.min_l.
    change (100 <= 128*100+20-100*i)%nat.
    lia.
Qed.

Print Assumptions agent32_q0_chunk_cover.
Print Assumptions agent32_q0_chunk_length.
