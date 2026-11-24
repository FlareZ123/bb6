From BusyCoq Require Import Enumerate62 Individual62 TC62 CTL62 Eqb Agent32SourceEncoding.
From Coq Require Import List NArith Strings.String.
Import ListNotations.
Import TNF_Node.

(* Complete ordered queue data: the actual table and both metadata fields.
   Source nodes have canonical finite tables, making exact equality possible
   without functional extensionality. *)
Definition checkpoint_canonical (x : T) : Prop :=
  tm_simpl (tm x) = tm x.

Definition checkpoint_canonicalQ (q : SearchQueue) : Prop :=
  Forall checkpoint_canonical (fst q) /\
  Forall checkpoint_canonical (snd q).

Definition packed_node := (string * nat * nat)%type.
Definition packed_queue := (list packed_node * list packed_node)%type.

Definition encode_node (x : T) : packed_node :=
  (TM_to_str (tm x), num_undef_trans x, min_unused_state x).

Definition decode_node (p : packed_node) : T :=
  let '(s,n,m) := p in Build_T (tm_simpl (TM_from_str s)) n m.

Definition encode_queue (q : SearchQueue) : packed_queue :=
  (List.map encode_node (fst q), List.map encode_node (snd q)).

Definition decode_queue (p : packed_queue) : SearchQueue :=
  (List.map decode_node (fst p), List.map decode_node (snd p)).

Lemma checkpoint_simpl_pointwise (a b : TM) :
  (forall s, a s = b s) -> tm_simpl a = tm_simpl b.
Proof.
  intro H. unfold tm_simpl.
  rewrite (H (A,S0)), (H (A,S1)), (H (B,S0)), (H (B,S1)),
          (H (C,S0)), (H (C,S1)), (H (D,S0)), (H (D,S1)),
          (H (E,S0)), (H (E,S1)), (H (F,S0)), (H (F,S1)).
  reflexivity.
Qed.

Lemma checkpoint_node_roundtrip x :
  checkpoint_canonical x -> decode_node (encode_node x) = x.
Proof.
  destruct x as [t n m].
  unfold checkpoint_canonical, decode_node, encode_node.
  cbn [tm num_undef_trans min_unused_state].
  intro H.
  assert (E : tm_simpl (TM_from_str (TM_to_str t)) = tm_simpl t).
  { apply checkpoint_simpl_pointwise. apply agent32_table_roundtrip. }
  rewrite E, H. reflexivity.
Qed.

Lemma checkpoint_list_roundtrip xs :
  Forall checkpoint_canonical xs ->
  List.map decode_node (List.map encode_node xs) = xs.
Proof.
  intro H. induction H as [|x xs Hx Hxs IH].
  - reflexivity.
  - cbn [List.map]. rewrite (checkpoint_node_roundtrip x Hx), IH.
    reflexivity.
Qed.

Theorem checkpoint_queue_roundtrip q :
  checkpoint_canonicalQ q -> decode_queue (encode_queue q) = q.
Proof.
  destruct q as [a b]. intros [Ha Hb].
  unfold decode_queue, encode_queue. cbn [fst snd].
  rewrite (checkpoint_list_roundtrip a Ha),
          (checkpoint_list_roundtrip b Hb). reflexivity.
Qed.

Lemma checkpoint_expand_canonical x h :
  Forall checkpoint_canonical (expand x h).
Proof.
  destruct x as [t n m].
  cbn [expand].
  apply Forall_app. split.
  - apply Forall_forall. intros y Hy.
    apply in_flat_map in Hy. destruct Hy as [s [_ Hy]].
    apply in_flat_map in Hy. destruct Hy as [o [_ Hy]].
    apply in_map_iff in Hy. destruct Hy as [d [<- _]].
    reflexivity.
  - destruct (skipn m all_qs) as [|s ss].
    + constructor.
    + apply Forall_forall. intros y Hy.
      apply in_flat_map in Hy. destruct Hy as [o [_ Hy]].
      apply in_map_iff in Hy. destruct Hy as [d [<- _]].
      reflexivity.
Qed.

Lemma checkpoint_expand'_canonical x h :
  Forall checkpoint_canonical (expand' x h).
Proof.
  unfold expand'.
  destruct (BusyCoq.Eqb.eqb (num_undef_trans x) (S O)).
  - constructor.
  - apply checkpoint_expand_canonical.
Qed.

Section CanonicalQueue.
  Variable f : TC62.TM.TM -> TC62.TM.DecideResult.

  Lemma checkpoint_update_canonical q :
    checkpoint_canonicalQ q ->
    checkpoint_canonicalQ (get_SQ (SearchQueue_upd f q)).
  Proof.
    destruct q as [[|x xs] ys]; intros [Ha Hb].
    - exact (conj Ha Hb).
    - cbn [fst snd] in Ha,Hb.
      inversion Ha as [|x' xs' Hx Hxs]; subst.
      unfold checkpoint_canonicalQ.
      cbn [SearchQueue_upd].
      destruct (f (tm x)); cbn [get_SQ fst snd].
      + split; [apply Forall_app; split;
          [apply checkpoint_expand'_canonical|exact Hxs]|exact Hb].
      + split; assumption.
      + split; [exact Hxs|constructor; assumption].
  Qed.

  Lemma checkpoint_bfs_canonical q :
    checkpoint_canonicalQ q ->
    checkpoint_canonicalQ (get_SQ (SearchQueue_upd_bfs f q)).
  Proof.
    destruct q as [[|x xs] ys]; intros [Ha Hb].
    - exact (conj Ha Hb).
    - cbn [fst snd] in Ha,Hb.
      inversion Ha as [|x' xs' Hx Hxs]; subst.
      unfold checkpoint_canonicalQ.
      cbn [SearchQueue_upd_bfs].
      destruct (f (tm x)); cbn [get_SQ fst snd].
      + split; [exact Hxs|apply Forall_app; split;
          [apply checkpoint_expand'_canonical|exact Hb]].
      + split; assumption.
      + split; [exact Hxs|constructor; assumption].
  Qed.

  Lemma checkpoint_iter_canonical
      (g : SearchQueue -> SearchQueue + SearchQueue)
      (Hstep : forall q, checkpoint_canonicalQ q ->
                    checkpoint_canonicalQ (get_SQ (g q)))
      q fuel :
    checkpoint_canonicalQ q ->
    checkpoint_canonicalQ (get_SQ (N_iter_until g (inl q) fuel)).
  Proof.
    intro Hq.
    assert (Hinv :
      match N_iter_until g (inl q) fuel with
      | inl s => checkpoint_canonicalQ s
      | inr s => checkpoint_canonicalQ s
      end).
    { eapply (N_iter_until_spec checkpoint_canonicalQ checkpoint_canonicalQ).
      - intros x Hx. specialize (Hstep x Hx).
        destruct (g x); exact Hstep.
      - exact Hq. }
    destruct (N_iter_until g (inl q) fuel); exact Hinv.
  Qed.

  Theorem checkpoint_updates_canonical q fuel :
    checkpoint_canonicalQ q ->
    checkpoint_canonicalQ (SearchQueue_upds f q fuel).
  Proof.
    unfold SearchQueue_upds.
    apply checkpoint_iter_canonical, checkpoint_update_canonical.
  Qed.

  Lemma checkpoint_bfs_round_canonical q :
    checkpoint_canonicalQ q ->
    checkpoint_canonicalQ (SearchQueue_upds_bfs f q).
  Proof.
    intro Hq. unfold SearchQueue_upds_bfs.
    pose proof (checkpoint_iter_canonical (SearchQueue_upd_bfs f)
      checkpoint_bfs_canonical q (length_tail (fst q)) Hq) as Hres.
    remember (get_SQ (N_iter_until (SearchQueue_upd_bfs f) (inl q)
      (length_tail (fst q)))) as s.
    destruct s as [a b].
    destruct Hres as [Ha Hb].
    unfold checkpoint_canonicalQ, SearchQueue_rst.
    cbn [fst snd] in *.
    split; [apply Forall_app; split; assumption|constructor].
  Qed.
End CanonicalQueue.

Lemma checkpoint_root_canonical : checkpoint_canonicalQ root_1RB.
Proof.
  split.
  - constructor; [reflexivity|constructor].
  - constructor.
Qed.

Theorem checkpoint_q0_canonical : checkpoint_canonicalQ q_0.
Proof.
  change (checkpoint_canonicalQ
    (SearchQueue_upds_bfs decider
      (SearchQueue_upds_bfs decider
        (SearchQueue_upds_bfs decider
          (SearchQueue_upds_bfs decider root_1RB))))).
  apply checkpoint_bfs_round_canonical.
  apply checkpoint_bfs_round_canonical.
  apply checkpoint_bfs_round_canonical.
  apply checkpoint_bfs_round_canonical.
  exact checkpoint_root_canonical.
Qed.

Lemma checkpoint_split_canonical n xs :
  Forall checkpoint_canonical xs ->
  Forall checkpoint_canonical (firstn n xs) /\
  Forall checkpoint_canonical (skipn n xs).
Proof.
  intro H. rewrite <- (firstn_skipn n xs) in H.
  apply Forall_app in H. exact H.
Qed.

Theorem checkpoint_chunk_canonical offset size :
  checkpoint_canonicalQ (q_i offset size).
Proof.
  pose proof checkpoint_q0_canonical as [Ha Hb].
  pose proof (checkpoint_split_canonical offset (fst q_0) Ha) as [_ Hsuffix].
  pose proof (checkpoint_split_canonical size (skipn offset (fst q_0))
    Hsuffix) as [Hslice _].
  split; assumption.
Qed.

(* Exact finite data equality gives the full source checkpoint equation. *)
Theorem source_checkpoint_decode
    (f : TC62.TM.TM -> TC62.TM.DecideResult) q fuel p :
  checkpoint_canonicalQ q ->
  encode_queue (SearchQueue_upds f q fuel) = p ->
  SearchQueue_upds f q fuel = decode_queue p.
Proof.
  intros H E. rewrite <- E. symmetry.
  apply checkpoint_queue_roundtrip.
  apply checkpoint_updates_canonical. exact H.
Qed.

Print Assumptions checkpoint_queue_roundtrip.
Print Assumptions checkpoint_chunk_canonical.
Print Assumptions source_checkpoint_decode.
