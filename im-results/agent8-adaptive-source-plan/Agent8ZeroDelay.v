From BusyCoq Require Import Enumerate62 Individual62 Eqb.
From Coq Require Import List Bool Arith Lia.
Import ListNotations.
Open Scope nat_scope.
Open Scope string_scope.

(* The exact zero-writing path relation, shared by the weighted source
   normalization and the finite margin checker. *)
Inductive zero_path (t : TM) : Q -> nat -> Q -> Prop :=
| zp0 q : zero_path t q 0 q
| zpS q q' z d k : t (q,S0) = Some (S0,d,q') ->
    zero_path t q' k z -> zero_path t q (S k) z.

Definition source_zero_edgeb (t : TM) (q r : Q) : bool :=
  orb (BusyCoq.Eqb.eqb (t (q,S0)) (Some (S0,L,r)))
      (BusyCoq.Eqb.eqb (t (q,S0)) (Some (S0,R,r))).

Lemma source_zero_edgeb_spec t q r :
  source_zero_edgeb t q r = true <->
  exists d, t (q,S0) = Some (S0,d,r).
Proof.
  unfold source_zero_edgeb. rewrite Bool.orb_true_iff.
  split.
  - intros [H|H].
    + exists L. destruct (BusyCoq.Eqb.eqb_spec (t (q,S0)) (Some (S0,L,r))); congruence.
    + exists R. destruct (BusyCoq.Eqb.eqb_spec (t (q,S0)) (Some (S0,R,r))); congruence.
  - intros [d H]. destruct d.
    + left. destruct (BusyCoq.Eqb.eqb_spec (t (q,S0)) (Some (S0,L,r))); congruence.
    + right. destruct (BusyCoq.Eqb.eqb_spec (t (q,S0)) (Some (S0,R,r))); congruence.
Qed.

Fixpoint source_zero_pathb (t : TM) (k : nat) (q r : Q) : bool :=
  match k with
  | O => BusyCoq.Eqb.eqb q r
  | S j => existsb (fun u => andb (source_zero_edgeb t q u)
                                  (source_zero_pathb t j u r)) all_qs
  end.

Theorem source_zero_pathb_spec t k q r :
  source_zero_pathb t k q r = true <-> zero_path t q k r.
Proof.
  revert q r. induction k as [|k IH]; intros q r; cbn [source_zero_pathb].
  - destruct (BusyCoq.Eqb.eqb_spec q r) as [E|E].
    + subst r. split; [intro; constructor|intro; reflexivity].
    + split; [discriminate|]. intro H. inversion H; subst; congruence.
  - rewrite existsb_exists. split.
    + intros [u [_ H]]. apply andb_true_iff in H. destruct H as [He Hp].
      apply source_zero_edgeb_spec in He. destruct He as [d Hd].
      eapply zpS; [exact Hd|]. apply (proj1 (IH u r)). exact Hp.
    + intro H. inversion H as [|q0 u z d k0 Hact Htail]; subst.
      exists u. split; [apply all_qs_spec|].
      apply andb_true_iff. split.
      * apply source_zero_edgeb_spec. exists d. exact Hact.
      * apply (proj2 (IH u r)). exact Htail.
Qed.

Definition source_has_delay (t : TM) (k : nat) : bool :=
  existsb (fun q => source_zero_pathb t k q A) all_qs.

Lemma source_has_delay_spec t k :
  source_has_delay t k = true <-> exists q, zero_path t q k A.
Proof.
  unfold source_has_delay. rewrite existsb_exists. split.
  - intros [q [_ H]]. exists q. apply source_zero_pathb_spec. exact H.
  - intros [q H]. exists q. split; [apply all_qs_spec|].
    apply source_zero_pathb_spec. exact H.
Qed.

(* A check on the six small delays alone; the astronomical primitive
   runtime never has to be evaluated by this boolean. *)
Definition source_delay_check (t : TM) (margin : nat) : bool :=
  forallb (fun k => if source_has_delay t k then Nat.leb k margin else true)
    (seq 0 6).

Theorem source_delay_check_spec t margin :
  source_delay_check t margin = true <->
  forall k q, zero_path t q k A -> k <= 5 -> k <= margin.
Proof.
  unfold source_delay_check. split.
  - intros H k q Hz Hk.
    apply forallb_forall with (x:=k) in H.
    + assert (E : source_has_delay t k = true).
      { apply source_has_delay_spec. exists q. exact Hz. }
      rewrite E in H. apply Nat.leb_le. exact H.
    + apply in_seq. lia.
  - intros H. apply forallb_forall. intros k Hk.
    apply in_seq in Hk.
    destruct (source_has_delay t k) eqn:E; [|reflexivity].
    apply source_has_delay_spec in E. destruct E as [q Hz].
    apply Nat.leb_le. eapply H; [exact Hz|lia].
Qed.

Lemma source_zero_path_congr (t u : TM) q k r :
  (forall h, t h = u h) -> zero_path t q k r -> zero_path u q k r.
Proof.
  intros E H. induction H.
  - constructor.
  - eapply zpS; [rewrite <- E; eassumption|exact IHHzero_path].
Qed.

(* Source parser's undefined transition is ---; this is the literal
   published champion, with its final B/1 query counted separately. *)
Definition source_champion_table : TM :=
  TM_from_str "1RB1RA_1RC---_1LD0RF_1RA0LE_0LD1RC_1RA0RE".

Theorem source_champion_delay_zero :
  source_delay_check source_champion_table 0 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem source_champion_no_positive_delay k q :
  zero_path source_champion_table q k A -> k <= 5 -> k = 0.
Proof.
  intros Hz Hk.
  pose proof ((proj1 (source_delay_check_spec source_champion_table 0))
    source_champion_delay_zero k q Hz Hk). lia.
Qed.

Print Assumptions source_zero_pathb_spec.
Print Assumptions source_delay_check_spec.
Print Assumptions source_champion_no_positive_delay.
