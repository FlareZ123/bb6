From BusyCoq Require Import Individual62.
From Coq Require Import Strings.String Strings.Ascii.
Open Scope string_scope.

Lemma agent32_append_assoc (a b c : string) :
  (a ++ b) ++ c = a ++ (b ++ c).
Proof. induction a; cbn; [reflexivity|rewrite IHa; reflexivity]. Qed.

Lemma agent32_append_empty (a : string) : a ++ EmptyString = a.
Proof. induction a; cbn; [reflexivity|rewrite IHa; reflexivity]. Qed.

Lemma agent32_transition_roundtrip (t : option (Sym*dir*Q)) (tail : string) :
  trans_from_str (Trans_to_str t ++ tail) = (tail,t).
Proof.
  destruct t as [[[s d] q]|]; [destruct s,d,q|]; reflexivity.
Qed.

Lemma agent32_row_roundtrip (tm0 : TM) (q : Q) (tail : string) :
  Q_from_str (TM_Q_to_str tm0 q ++ tail) =
  (skip_sep tail,tm0 (q,S0),tm0 (q,S1)).
Proof.
  unfold Q_from_str,TM_Q_to_str.
  rewrite agent32_append_assoc, agent32_transition_roundtrip, agent32_transition_roundtrip.
  reflexivity.
Qed.

(* Full strings in the actual holdout_i output are lossless, pointwise. *)
Theorem agent32_table_roundtrip (tm0 : TM) (s : Q*Sym) :
  TM_from_str (TM_to_str tm0) s = tm0 s.
Proof.
  unfold TM_from_str,TM_to_str.
  repeat (rewrite agent32_row_roundtrip; cbn [skip_sep append]).
  replace (TM_Q_to_str tm0 F) with (TM_Q_to_str tm0 F ++ EmptyString)
    by (rewrite agent32_append_empty; reflexivity).
  rewrite agent32_row_roundtrip.
  destruct s as [q b]; destruct q,b; reflexivity.
Qed.

Theorem agent32_table_string_injective (a b : TM) :
  TM_to_str a = TM_to_str b -> forall s, a s = b s.
Proof.
  intros H s.
  rewrite <- (agent32_table_roundtrip a s), <- (agent32_table_roundtrip b s), H.
  reflexivity.
Qed.

Print Assumptions agent32_table_roundtrip.
Print Assumptions agent32_table_string_injective.
