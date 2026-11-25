From BusyCoq Require Import Agent5CoarseTree Individual62.
From Coq Require Import List Strings.String.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.
Definition pair_c_35 : coarse_certificate := ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1RB_------", CTpair 5 5).
Theorem pair_checked_35 : coarse_candidate_check 1000006 pair_c_35 = true.
Proof. vm_compute. reflexivity. Qed.
Theorem pair_safe_35 : source_table_safe 1000006 (coarse_tm pair_c_35).
Proof. eapply coarse_check_sound. exact pair_checked_35. Qed.
Print Assumptions pair_safe_35.
