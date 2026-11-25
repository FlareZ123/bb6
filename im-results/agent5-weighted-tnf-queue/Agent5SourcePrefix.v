From BusyCoq Require Import Enumerate62 Individual62 TC62 Agent32SourceBackwards Agent32Q0Partition.
From Coq Require Import List NArith Lia.
Import ListNotations TNF_Node.
Open Scope nat_scope.

(* Ignore the final k active nodes, while retaining every held obligation.
   A depth-first update on the ignored suffix cannot invalidate safety
   already established for the preceding prefix. *)
Definition cut_active (k : nat) (xs : list T) :=
  firstn (length xs - k) xs.
Definition cut_queue k (q : SearchQueue) : SearchQueue :=
  (cut_active k (fst q), snd q).

Lemma cut_small k xs :
  length xs <= k -> cut_active k xs = [].
Proof.
  intro H. unfold cut_active.
  replace (length xs-k) with 0 by lia. reflexivity.
Qed.
Lemma cut_cons k x xs :
  k <= length xs -> cut_active k (x::xs) = x::cut_active k xs.
Proof.
  intro H. unfold cut_active. cbn [length].
  replace (S (length xs)-k) with (S (length xs-k)) by lia.
  reflexivity.
Qed.
Lemma cut_app k xs ys :
  k <= length ys -> cut_active k (xs++ys) = xs++cut_active k ys.
Proof.
  intro H. unfold cut_active. rewrite app_length.
  replace (length xs+length ys-k) with (length xs+(length ys-k)) by lia.
  rewrite firstn_app, firstn_all2 by lia.
  replace (length xs+(length ys-k)-length xs) with (length ys-k) by lia.
  reflexivity.
Qed.

Section Prefix.
  Variable Safe : T -> Prop.
  Variable f : TC62.TM.TM -> TC62.TM.DecideResult.
  Hypothesis local_safe : forall x,
    match f (tm x) with
    | TC62.TM.Halt h => Forall Safe (expand' x h) -> Safe x
    | TC62.TM.NonHalt => Safe x
    | TC62.TM.Unknown => True
    end.

  Lemma cut_update_backwards k q :
    safeQ Safe (cut_queue k (get_SQ (SearchQueue_upd f q))) ->
    safeQ Safe (cut_queue k q).
  Proof.
    destruct q as [[|x xs] ys].
    - exact (fun H => H).
    - destruct (Nat.le_gt_cases k (length xs)) as [Hlarge|Hsmall].
      + pose proof (local_safe x) as Hloc.
        unfold cut_queue, safeQ.
        cbn [SearchQueue_upd fst snd].
        rewrite cut_cons by exact Hlarge.
        destruct (f (tm x)) as [h| |] eqn:E;
          cbn [get_SQ fst snd].
        * rewrite cut_app by exact Hlarge.
          intros [H Hys]. apply Forall_app in H. destruct H as [Hkids Hrest].
          split; [constructor; [apply Hloc; exact Hkids|exact Hrest]|exact Hys].
        * intros [Hrest Hys]. split; [constructor; assumption|exact Hys].
        * intros [Hrest Hys]. inversion Hys; subst.
          split; [constructor; assumption|assumption].
      + unfold cut_queue, safeQ.
        cbn [SearchQueue_upd fst snd].
        rewrite cut_small by (cbn [length]; lia).
        destruct (f (tm x)) as [h| |] eqn:E; cbn [get_SQ fst snd].
        * intros [_ Hys]. split; [constructor|exact Hys].
        * intros [_ Hys]. split; [constructor|exact Hys].
        * intros [_ Hys]. inversion Hys; subst.
          split; [constructor|assumption].
  Qed.

  Theorem source_cut_updates_backwards k q fuel :
    safeQ Safe (cut_queue k (SearchQueue_upds f q fuel)) ->
    safeQ Safe (cut_queue k q).
  Proof.
    unfold SearchQueue_upds.
    assert (Hinv :
      match N_iter_until (SearchQueue_upd f) (inl q) fuel with
      | inl s => safeQ Safe (cut_queue k s) -> safeQ Safe (cut_queue k q)
      | inr s => safeQ Safe (cut_queue k s) -> safeQ Safe (cut_queue k q)
      end).
    { eapply (N_iter_until_spec
        (fun s => safeQ Safe (cut_queue k s) -> safeQ Safe (cut_queue k q))
        (fun s => safeQ Safe (cut_queue k s) -> safeQ Safe (cut_queue k q))).
      - intros x Hx.
        pose proof (cut_update_backwards k x) as Hb.
        destruct (SearchQueue_upd f x) as [y|y] eqn:E;
          intro Hy; apply Hx; apply Hb; exact Hy.
      - exact (fun H => H). }
    destruct (N_iter_until (SearchQueue_upd f) (inl q) fuel); exact Hinv.
  Qed.
End Prefix.

Lemma cut_q0_prefix :
  cut_queue 97 (q_i 0 100) = q_i 0 3.
Proof.
  unfold cut_queue, cut_active, q_i.
  cbn [fst snd skipn].
  rewrite firstn_length, agent32_q0_length.
  replace (Nat.min 100 12820 - 97) with 3 by reflexivity.
  rewrite firstn_firstn. reflexivity.
Qed.
Print Assumptions source_cut_updates_backwards.
Print Assumptions cut_q0_prefix.
