From BusyCoq Require Import Enumerate62 Individual62 Eqb
  Agent8AdaptiveSource Agent8ZeroDelay Agent8SourceWF Agent8WeightedSource.
From Coq Require Import List Lia Arith.
Import TNF_Node.
Open Scope nat_scope.

(* The exact-delay version of the last-hole optimization. A completion
   which fills the unique undefined row is a total table and cannot halt.
   A halting completion therefore agrees pointwise with the source table. *)
Theorem source_last_hole_exact_weighted bound p n h margin :
  get_num_undef_trans p = 1 ->
  halts_at p c0 n h ->
  source_delay_check p margin = true ->
  n + margin + 1 <= bound ->
  forall m, is_child_of m p -> weighted_bound bound m.
Proof.
  intros Hcount Htrace Hmargin Hbound m Hchild k d start Hk Hz Hd.
  destruct h as [q s].
  inversion Htrace as [t c nn q' l s' r Hrun Hhole]; subst.
  destruct (m (q,s)) as [v|] eqn:Eact.
  - exfalso. apply (source_total_nonhalt m); [|exists k; exact Hk].
    intros g Hnone.
    destruct (BusyCoq.Eqb.eqb_spec g (q,s)) as [E|E].
    + subst g. congruence.
    + pose proof (source_count_one p (q,s) Hcount Hhole g E) as Hother.
      destruct (Hchild g); congruence.
  - assert (Heq : forall g, m g = p g).
    { intro g. destruct (BusyCoq.Eqb.eqb_spec g (q,s)) as [E|E].
      - subst g. congruence.
      - pose proof (source_count_one p (q,s) Hcount Hhole g E) as Hother.
        destruct (Hchild g); congruence. }
    assert (Hnm : halts_in m c0 n).
    { exists (q,(l,s,r)). split.
      - eapply child_multistep; eassumption.
      - exact Eact. }
    pose proof (source_time_unique m c0 k n Hk Hnm).
    pose proof (source_zero_path_congr m p start d A Heq Hz) as Hdelay.
    pose proof ((proj1 (source_delay_check_spec p margin)) Hmargin d start Hdelay Hd).
    lia.
Qed.

(* No five-step slack is lost at the exact score of this named table.
   The premise is the primitive halting witness, not a finite simulation. *)
Theorem source_champion_weighted_exact n :
  halts_in source_champion_table c0 n ->
  weighted_bound (n+1) source_champion_table.
Proof.
  intros Hn k d start Hk Hz Hd.
  pose proof (source_time_unique source_champion_table c0 k n Hk Hn).
  pose proof (source_champion_no_positive_delay d start Hz Hd).
  lia.
Qed.

Print Assumptions source_last_hole_exact_weighted.
Print Assumptions source_champion_weighted_exact.
