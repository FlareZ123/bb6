From BusyCoq Require Import Agent47SourceWitness SourceResidualRoster
  Agent8WeightedSource Agent8SourceWF Enumerate62 Individual62 Eqb.
From Coq Require Import List Bool Lia Arith.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.

(* An exact source trace which reports its reached undefined row. *)
Definition source_hole_atb (p : TM) (n : nat) (h : Q * Sym) : bool :=
  match Agent47TC.Flip.Compute.cmultistep p n Agent47TC.Flip.Compute.starting with
  | inleft (exist _ (q, (_, s, _)) _) =>
      match p (q,s) with
      | None => BusyCoq.Eqb.eqb (q,s) h
      | Some _ => false
      end
  | inright _ => false
  end.

Lemma source_hole_atb_sound p n h :
  source_hole_atb p n h = true -> halts_at p c0 n h.
Proof.
  unfold source_hole_atb.
  destruct (Agent47TC.Flip.Compute.cmultistep p n Agent47TC.Flip.Compute.starting)
    as [[c Hrun]|Hearly].
  - destruct c as [q [[l s] r]].
    destruct (p (q,s)) as [v|] eqn:E; [discriminate|].
    destruct (BusyCoq.Eqb.eqb_spec (q,s) h) as [Heq|Hne]; [|discriminate].
    intros _. subst h.
    eapply halts_at_intro.
    + rewrite Agent47TC.Flip.Compute.lift_starting in Hrun.
      apply translated_multistep_transfer. exact Hrun.
    + exact E.
  - discriminate.
Qed.

(* The halt continuation costs at most n+6, including the incoming
   zero-write prefix. The other 24 actions are retained as children. *)
Theorem source_first_hole_split bound p n h :
  halts_at p c0 n h ->
  n + 6 <= bound ->
  (forall v, source_table_safe bound (tm_upd p h v)) ->
  source_table_safe bound p.
Proof.
  intros Htrace Hbound Hchildren m Hchild k d start Hk Hz Hd.
  destruct h as [q s].
  inversion Htrace as [t c nn q' l s' r Hrun Hhole]; subst.
  destruct (m (q,s)) as [v|] eqn:Eact.
  - exact (Hchildren v m (completion_refine m p (q,s) v Hchild Eact)
      k d start Hk Hz Hd).
  - assert (Hnm : halts_in m c0 n).
    { exists (q,(l,s,r)). split.
      - eapply child_multistep; eassumption.
      - exact Eact. }
    pose proof (source_time_unique m c0 k n Hk Hnm). lia.
Qed.

Definition source_move := (Sym * dir * Q)%type.
Definition source_moves : list source_move :=
  flat_map (fun q => flat_map (fun s => map (fun d => (s,d,q)) [L;R]) all_syms) all_qs.

Lemma source_moves_complete (v : source_move) : In v source_moves.
Proof.
  destruct v as [[s d] q].
  unfold source_moves. apply in_flat_map.
  exists q. split; [apply all_qs_spec|].
  apply in_flat_map. exists s. split; [apply all_syms_spec|].
  apply in_map. destruct d; simpl; auto.
Qed.

(* Positive function branching gives an induction hypothesis for every
   ordinary child. Unassigned certificate entries explicitly stay open. *)
Inductive source_tree : Type :=
| STopen
| STcert (w : source_witness)
| STsplit (n : nat) (h : Q * Sym) (children : source_move -> source_tree).

Fixpoint source_tree_check bound p (t : source_tree) : bool :=
  match t with
  | STopen => true
  | STcert w => source_witness_check bound p w
  | STsplit n h kids =>
      andb (Nat.leb (n+6) bound)
        (andb (source_hole_atb p n h)
          (forallb (fun v => source_tree_check bound (tm_upd p h v) (kids v))
            source_moves))
  end.

Fixpoint source_tree_open p (t : source_tree) : list TM :=
  match t with
  | STopen => [p]
  | STcert _ => []
  | STsplit _ h kids =>
      flat_map (fun v => source_tree_open (tm_upd p h v) (kids v)) source_moves
  end.

Theorem source_tree_sound bound p t :
  source_tree_check bound p t = true ->
  Forall (source_table_safe bound) (source_tree_open p t) ->
  source_table_safe bound p.
Proof.
  revert p.
  induction t as [|w|n h kids IH]; intros p Hcheck Hopen;
    cbn [source_tree_check source_tree_open] in Hcheck,Hopen.
  - inversion Hopen; assumption.
  - eapply source_witness_check_sound; exact Hcheck.
  - rewrite !andb_true_iff in Hcheck.
    destruct Hcheck as [Hbound [Htrace Hkids]].
    apply Nat.leb_le in Hbound.
    eapply source_first_hole_split.
    + apply source_hole_atb_sound. exact Htrace.
    + exact Hbound.
    + intro v. apply (IH v).
      * apply forallb_forall with (x:=v) in Hkids.
        -- exact Hkids.
        -- apply source_moves_complete.
      * apply Forall_forall. intros q Hq.
        apply Forall_forall with (x:=q) in Hopen.
        -- exact Hopen.
        -- apply in_flat_map. exists v. split; [apply source_moves_complete|exact Hq].
Qed.

(* Finite data can use a list; a missing entry is always open. *)
Definition source_move_index (v : source_move) : nat :=
  let '(s,d,q) := v in
  4 * state_index q +
    (match s with S0 => 0 | S1 => 2 end) +
    (match d with L => 0 | R => 1 end).

Definition source_children (xs : list source_tree) (v : source_move) :=
  nth (source_move_index v) xs STopen.

Definition source_split n h xs := STsplit n h (source_children xs).

Print Assumptions source_hole_atb_sound.
Print Assumptions source_first_hole_split.
Print Assumptions source_tree_sound.
