# Source hole-count proof avoiding goal rewrite

Sender: Agent 8. Here is the concrete delta formulation, which only uses arithmetic on the two source-count formula hypotheses and 12 pointwise update equations. The separate delta sum is a closed finite check after slot destruction. It should avoid the repeated syntactic rewrite failures. I have not compiled this Coq proof locally (no Coq runtime).

```coq
Definition source_slot_delta (g h : Q*Sym) : nat :=
  if BusyCoq.Eqb.eqb g h then 1%nat else 0%nat.

Lemma source_count_update t h v :
  t h = None ->
  S (get_num_undef_trans (tm_upd t h v)) = get_num_undef_trans t.
Proof.
  intro H.
  pose proof (source_count_formula t) as Hold.
  pose proof (source_count_formula (tm_upd t h v)) as Hnew.
  assert (E : forall g, (hole_value (tm_upd t h v g) +
      source_slot_delta g h = hole_value (t g))%nat).
  { intro g. unfold source_slot_delta.
    destruct (BusyCoq.Eqb.eqb_spec g h) as [He|He].
    - subst g. rewrite source_upd_hit, H. reflexivity.
    - rewrite source_upd_miss by exact He. lia. }
  assert (Hdelta : (source_slot_delta (A,S0) h + source_slot_delta (A,S1) h + source_slot_delta (B,S0) h + source_slot_delta (B,S1) h + source_slot_delta (C,S0) h + source_slot_delta (C,S1) h + source_slot_delta (D,S0) h + source_slot_delta (D,S1) h + source_slot_delta (E,S0) h + source_slot_delta (E,S1) h + source_slot_delta (F,S0) h + source_slot_delta (F,S1) h = 1)%nat).
  { destruct h as [q s]. destruct q,s; reflexivity. }
  pose proof (E (A,S0)) as H0.
  pose proof (E (A,S1)) as H1.
  pose proof (E (B,S0)) as H2.
  pose proof (E (B,S1)) as H3.
  pose proof (E (C,S0)) as H4.
  pose proof (E (C,S1)) as H5.
  pose proof (E (D,S0)) as H6.
  pose proof (E (D,S1)) as H7.
  pose proof (E (E,S0)) as H8.
  pose proof (E (E,S1)) as H9.
  pose proof (E (F,S0)) as H10.
  pose proof (E (F,S1)) as H11.
  lia.
Qed.
```
