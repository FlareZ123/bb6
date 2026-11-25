From BusyCoq Require Import SourceResidualRoster TranslatedCyclers
  Enumerate62 Agent8WeightedSource Individual62.
From Coq Require Import List Bool Lia Arith Strings.String.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.
Open Scope nat_scope.

(* Direct original-source checking, not a cross-language assertion. *)
Module Agent47TC := TranslatedCyclers BB62.

Lemma translated_nonhalt_transfer (p : TM) :
  ~ Agent47TC.TM.halts p Agent47TC.TM.c0 -> ~ halts p c0.
Proof.
  rewrite Agent47TC.TM.halts_halts', halts_halts'.
  exact (fun h => h).
Qed.

Definition source_side_check (p : TM) (d : dir) (entry period budget : nat) : bool :=
  if Agent47TC.verify_tcycler p d entry period budget then true else false.

Theorem source_side_check_sound bound p d entry period budget :
  source_side_check p d entry period budget = true ->
  source_table_safe bound p.
Proof.
  unfold source_side_check.
  destruct (Agent47TC.verify_tcycler p d entry period budget) as [H|H].
  - intro _. apply source_nonhalt_cylinder.
    exact (translated_nonhalt_transfer p H).
  - discriminate.
Qed.

(* The successful branch of cmultistep includes the original multistep proof.
   Test that the reached row really is undefined; never accept an early abort. *)
Definition source_trace_haltb (p : TM) (n : nat) : bool :=
  match Individual62.cmultistep p n Individual62.starting with
  | inleft (exist _ (q, (_, s, _)) _) =>
      match p (q,s) with None => true | Some _ => false end
  | inright _ => false
  end.

Lemma source_trace_haltb_sound p n :
  source_trace_haltb p n = true -> exists h, halts_at p c0 n h.
Proof.
  unfold source_trace_haltb.
  destruct (Individual62.cmultistep p n Individual62.starting)
    as [[c Hrun]|Hearly].
  - destruct c as [q [[l s] r]].
    destruct (p (q,s)) as [mv|] eqn:E; [discriminate|].
    intro _. exists (q,s).
    eapply halts_at_intro.
    + exact Hrun.
    + exact E.
  - discriminate.
Qed.

Definition source_last_check (bound : nat) (p : TM) (n : nat) : bool :=
  andb (Nat.eqb (get_num_undef_trans p) 1)
  (andb (Nat.leb (n+6) bound) (source_trace_haltb p n)).

Theorem source_last_check_sound bound p n :
  source_last_check bound p n = true -> source_table_safe bound p.
Proof.
  unfold source_last_check.
  rewrite !andb_true_iff.
  intros [Hcount [Hbound Htrace]].
  apply Nat.eqb_eq in Hcount.
  apply Nat.leb_le in Hbound.
  destruct (source_trace_haltb_sound p n Htrace) as [h Hh].
  eapply source_last_hole_cylinder; eassumption.
Qed.

Inductive source_witness :=
| SWside (d : dir) (entry period budget : nat)
| SWlast (n : nat).

Definition source_witness_check bound p w :=
  match w with
  | SWside d entry period budget => source_side_check p d entry period budget
  | SWlast n => source_last_check bound p n
  end.

Lemma source_witness_check_sound bound p w :
  source_witness_check bound p w = true -> source_table_safe bound p.
Proof.
  destruct w; cbn [source_witness_check].
  - apply source_side_check_sound.
  - apply source_last_check_sound.
Qed.

Definition source_certificate := (string * source_witness)%type.
Definition certificate_tm (w : source_certificate) : TM := TM_from_str (fst w).
Definition certificate_check bound (w : source_certificate) :=
  source_witness_check bound (certificate_tm w) (snd w).
Definition certificate_roster (certs : list source_certificate) : list TM :=
  map certificate_tm certs.

Theorem certificate_roster_safe bound certs :
  forallb (certificate_check bound) certs = true ->
  Forall (source_table_safe bound) (certificate_roster certs).
Proof.
  induction certs as [|w ws IH]; cbn [certificate_roster map forallb].
  - intros _. constructor.
  - rewrite andb_true_iff. intros [Hw Hws].
    constructor.
    + apply (source_witness_check_sound bound (certificate_tm w) (snd w)).
      exact Hw.
    + apply IH. exact Hws.
Qed.

(* Only checked containment removes a node. The source plan, order and
   metadata remain untouched; every unmatched node stays an obligation. *)
Definition source_uncovered (roster : list TM) (nodes : list T) : list T :=
  filter (fun x => negb (source_roster_covers roster x)) nodes.

Theorem source_uncovered_sound bound roster nodes :
  Forall (source_table_safe bound) roster ->
  Forall (source_weighted_safe bound) (source_uncovered roster nodes) ->
  Forall (source_weighted_safe bound) nodes.
Proof.
  intros Hsafe Hrest.
  rewrite Forall_forall in Hrest |- *.
  intros x Hx.
  destruct (source_roster_covers roster x) eqn:E.
  - eapply source_roster_safe; eassumption.
  - apply Hrest. unfold source_uncovered.
    apply filter_In. split; [exact Hx|now rewrite E].
Qed.

Print Assumptions translated_nonhalt_transfer.
Print Assumptions source_side_check_sound.
Print Assumptions source_last_check_sound.
Print Assumptions certificate_roster_safe.
Print Assumptions source_uncovered_sound.
