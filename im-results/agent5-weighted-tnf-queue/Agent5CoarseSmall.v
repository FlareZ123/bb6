From BusyCoq Require Import Agent5CoarseTree.
From Coq Require Import List Strings.String.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.
Definition coarse_c_0 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_0LF0LA_0LE---", CTw (SWlast 20)).
Lemma coarse_c_0_checked : coarse_candidate_check 1000006 coarse_c_0 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_1 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_0LF0LA_0RE---", CTw (SWside R 17 2 1)).
Lemma coarse_c_1_checked : coarse_candidate_check 1000006 coarse_c_1 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_2 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_0LF0LA_1LE---", CTw (SWlast 20)).
Lemma coarse_c_2_checked : coarse_candidate_check 1000006 coarse_c_2 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_3 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_0LF0LA_1RE---", CTw (SWlast 20)).
Lemma coarse_c_3_checked : coarse_candidate_check 1000006 coarse_c_3 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_4 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_0LF0LA_0LF---", CTw (SWlast 20)).
Lemma coarse_c_4_checked : coarse_candidate_check 1000006 coarse_c_4 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_5 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_0LF0LA_0RF---", CTw (SWside R 18 1 0)).
Lemma coarse_c_5_checked : coarse_candidate_check 1000006 coarse_c_5 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_6 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_0LF0LA_1LF---", CTw (SWlast 20)).
Lemma coarse_c_6_checked : coarse_candidate_check 1000006 coarse_c_6 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_7 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_0LF0LA_1RF---", CTw (SWside R 18 1 0)).
Lemma coarse_c_7_checked : coarse_candidate_check 1000006 coarse_c_7 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_8 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_0RF0LA_------", coarse_split 18 (F,S0) [CTw (SWside R 0 19 2);
CTw (SWside R 0 19 2);
CTw (SWside R 16 4 0);
CTmitm 0;
CTmitm 0;
CTw (SWside R 11 42 0);
CTmitm 0;
CTw (SWside R 1 18 3);
CTmitm 0;
CTw (SWside R 0 20 2);
CTmitm 0;
CTmitm 0;
CTw (SWside R 16 5 0);
CTw (SWside R 16 5 0);
CTmitm 0;
CTmitm 0;
CTw (SWside R 17 2 0);
CTw (SWside R 17 2 0);
CTw (SWlast 20);
CTw (SWside R 17 2 0);
CTw (SWlast 22);
CTw (SWside R 18 1 0);
CTw (SWlast 22);
CTw (SWside R 18 1 0)]).
Lemma coarse_c_8_checked : coarse_candidate_check 1000006 coarse_c_8 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_9 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_------", coarse_split 18 (F,S0) [CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 16 3 0);
CTw (SWside R 14 5 0);
CTw (SWside R 16 3 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWlast 20);
CTmitm 0;
CTw (SWlast 20);
CTmitm 0;
CTw (SWlast 20);
CTw (SWlast 19);
CTw (SWlast 20);
CTw (SWlast 19)]).
Lemma coarse_c_9_checked : coarse_candidate_check 1000006 coarse_c_9 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_10 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1RF0LA_------", coarse_split 18 (F,S0) [CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 16 3 0);
CTmitm 0;
CTw (SWside R 0 21 2);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 15 4 0);
CTw (SWside R 2 17 4);
CTmitm 0;
CTw (SWside R 16 5 0);
CTmitm 0;
CTw (SWside R 4 15 4);
CTmitm 0;
CTw (SWside R 17 2 0);
CTmitm 0;
CTw (SWside R 17 2 0);
CTw (SWlast 19);
CTw (SWside R 18 1 0);
CTw (SWlast 19);
CTw (SWside R 18 1 0)]).
Lemma coarse_c_10_checked : coarse_candidate_check 1000006 coarse_c_10 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_11 : coarse_certificate := ("1RB1RD_1RC0RE_0LA1LB_1LA1LD_---0LA_------", CTmitm 1).
Lemma coarse_c_11_checked : coarse_candidate_check 1000006 coarse_c_11 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_12 : coarse_certificate := ("1RB1RD_1RC0RE_0LA1RB_1LA1LD_---0LA_------", coarse_split 17 (E,S0) [CTmitm 0;
CTw (SWside R 0 18 2);
CTw (SWside R 16 3 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 16 4 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 17 1 0);
CTmitm 0;
CTw (SWside R 17 1 0);
coarse_split 18 (F,S0) [CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside L 16 61 1);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 15 4 0);
CTmitm 0;
CTmitm 0;
CTw (SWside R 16 5 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 17 2 1);
CTmitm 0;
CTw (SWlast 20);
CTw (SWlast 19);
CTw (SWside R 18 1 0);
CTw (SWlast 19);
CTw (SWside R 18 1 0)];
coarse_split 18 (F,S0) [CTmitm 0;
CTw (SWside R 0 19 2);
CTw (SWside R 16 4 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 1 18 3);
CTmitm 0;
CTw (SWside R 0 20 2);
CTmitm 0;
CTmitm 0;
CTw (SWside R 16 5 0);
CTw (SWside R 16 5 0);
CTmitm 0;
CTmitm 0;
CTw (SWside R 17 2 0);
CTw (SWside R 17 2 0);
CTw (SWlast 20);
CTw (SWside R 17 2 0);
CTw (SWlast 21);
CTw (SWside R 18 1 0);
CTw (SWlast 21);
CTw (SWside R 18 1 0)];
coarse_split 18 (F,S0) [CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 16 3 0);
CTmitm 0;
CTw (SWside R 16 3 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWlast 19);
CTw (SWlast 19);
CTw (SWlast 19);
CTw (SWlast 19)];
coarse_split 18 (F,S0) [CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 16 3 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 15 4 0);
CTmitm 0;
CTmitm 0;
CTw (SWside R 16 5 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 17 2 0);
CTmitm 0;
CTw (SWside R 17 2 0);
CTw (SWlast 19);
CTw (SWside R 18 1 0);
CTw (SWlast 19);
CTw (SWside R 18 1 0)]]).
Lemma coarse_c_12_checked : coarse_candidate_check 1000006 coarse_c_12 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_13 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0LC_1LA1LD_---0LA_------", CTw (SWside L 0 20 2)).
Lemma coarse_c_13_checked : coarse_candidate_check 1000006 coarse_c_13 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_14 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0RC_1LA1LD_---0LA_------", CTw (SWside R 0 46 4)).
Lemma coarse_c_14_checked : coarse_candidate_check 1000006 coarse_c_14 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_15 : coarse_certificate := ("1RB1RD_1RC0RE_0LA1LC_1LA1LD_---0LA_------", CTw (SWside L 16 6 0)).
Lemma coarse_c_15_checked : coarse_candidate_check 1000006 coarse_c_15 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_16 : coarse_certificate := ("1RB1RD_1RC0RE_0LA1RC_1LA1LD_---0LA_------", CTmitm 1).
Lemma coarse_c_16_checked : coarse_candidate_check 1000006 coarse_c_16 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_17 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0LD_1LA1LD_---0LA_------", CTw (SWside L 6 10 0)).
Lemma coarse_c_17_checked : coarse_candidate_check 1000006 coarse_c_17 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_18 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0RD_1LA1LD_---0LA_------", CTw (SWside L 6 14 0)).
Lemma coarse_c_18_checked : coarse_candidate_check 1000006 coarse_c_18 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_19 : coarse_certificate := ("1RB1RD_1RC0RE_0LA1LD_1LA1LD_---0LA_------", CTw (SWside L 6 10 0)).
Lemma coarse_c_19_checked : coarse_candidate_check 1000006 coarse_c_19 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_20 : coarse_certificate := ("1RB1RD_1RC0RE_0LA1RD_1LA1LD_---0LA_------", CTw (SWside L 6 12 0)).
Lemma coarse_c_20_checked : coarse_candidate_check 1000006 coarse_c_20 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_21 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0LE_1LA1LD_---0LA_------", CTw (SWside L 3 14 1)).
Lemma coarse_c_21_checked : coarse_candidate_check 1000006 coarse_c_21 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_22 : coarse_certificate := ("1RB1RD_1RC0RE_0LA0RE_1LA1LD_---0LA_------", coarse_split 44 (E,S0) [CTmitm 0;
CTmitm 0;
CTw (SWside R 44 3 1);
CTmitm 0;
CTmitm 0;
CTw (SWside R 40 15 1);
CTw (SWside R 42 3 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 44 4 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 44 1 0);
CTmitm 0;
CTw (SWside R 44 1 0);
coarse_split 45 (F,S0) [CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside L 56 25 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside L 0 68 4);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 44 5 1);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 44 2 1);
CTmitm 0;
CTw (SWlast 47);
CTw (SWlast 46);
CTw (SWside R 45 1 0);
CTw (SWlast 46);
CTw (SWside R 45 1 0)];
coarse_split 45 (F,S0) [CTmitm 0;
CTmitm 0;
CTw (SWside R 44 4 0);
CTw (SWside R 36 23 1);
CTmitm 0;
CTw (SWside R 40 16 1);
CTw (SWside R 42 4 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 41 6 0);
CTw (SWside R 40 15 1);
CTw (SWside R 44 5 1);
CTw (SWside R 44 5 0);
CTmitm 0;
CTw (SWside R 40 13 1);
CTw (SWside R 44 2 0);
CTw (SWside R 44 2 0);
CTw (SWlast 47);
CTw (SWside R 44 2 0);
CTw (SWlast 48);
CTw (SWside R 45 1 0);
CTw (SWlast 48);
CTw (SWside R 45 1 0)];
coarse_split 45 (F,S0) [CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 44 3 1);
CTw (SWside R 40 7 1);
CTw (SWside R 44 3 1);
CTmitm 0;
CTw (SWside R 43 3 0);
CTw (SWside R 39 7 0);
CTw (SWside R 43 3 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWlast 46);
CTw (SWlast 46);
CTw (SWlast 46);
CTw (SWlast 46)];
coarse_split 45 (F,S0) [CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 44 3 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 43 3 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 44 5 0);
CTmitm 0;
CTmitm 0;
CTmitm 0;
CTw (SWside R 44 2 0);
CTw (SWside R 40 6 1);
CTw (SWside R 44 2 0);
CTw (SWlast 46);
CTw (SWside R 45 1 0);
CTw (SWlast 46);
CTw (SWside R 45 1 0)]]).
Lemma coarse_c_22_checked : coarse_candidate_check 1000006 coarse_c_22 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_23 : coarse_certificate := ("1RB1RD_1RC0RE_0LA1LE_1LA1LD_---0LA_------", CTw (SWside L 3 14 1)).
Lemma coarse_c_23_checked : coarse_candidate_check 1000006 coarse_c_23 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_24 : coarse_certificate := ("1RB1RD_1RC0RE_0LA1RE_1LA1LD_---0LA_------", CTw (SWside L 6 16 0)).
Lemma coarse_c_24_checked : coarse_candidate_check 1000006 coarse_c_24 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_29 : coarse_certificate := ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0RA_------", CTw (SWside R 13 9 2)).
Lemma coarse_c_29_checked : coarse_candidate_check 1000006 coarse_c_29 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_31 : coarse_certificate := ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1RA_------", CTw (SWside L 7 12 1)).
Lemma coarse_c_31_checked : coarse_candidate_check 1000006 coarse_c_31 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_32 : coarse_certificate := ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0LB_------", CTw (SWside L 1 12 1)).
Lemma coarse_c_32_checked : coarse_candidate_check 1000006 coarse_c_32 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_36 : coarse_certificate := ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0LC_------", CTw (SWside L 7 10 0)).
Lemma coarse_c_36_checked : coarse_candidate_check 1000006 coarse_c_36 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_38 : coarse_certificate := ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1LC_------", CTw (SWside L 7 10 0)).
Lemma coarse_c_38_checked : coarse_candidate_check 1000006 coarse_c_38 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_40 : coarse_certificate := ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0LD_------", CTw (SWside L 7 8 0)).
Lemma coarse_c_40_checked : coarse_candidate_check 1000006 coarse_c_40 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_42 : coarse_certificate := ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1LD_------", CTw (SWside L 7 8 0)).
Lemma coarse_c_42_checked : coarse_candidate_check 1000006 coarse_c_42 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_43 : coarse_certificate := ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1RD_------", CTw (SWside L 7 10 0)).
Lemma coarse_c_43_checked : coarse_candidate_check 1000006 coarse_c_43 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_54 : coarse_certificate := ("1RB1RD_1RC---_0LA---_1LA1RD_------_------", CTw (SWside R 4 3 1)).
Lemma coarse_c_54_checked : coarse_candidate_check 1000006 coarse_c_54 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_59 : coarse_certificate := ("1RB1RD_1RC---_0LA---_1RA---_------_------", CTw (SWside R 0 5 0)).
Lemma coarse_c_59_checked : coarse_candidate_check 1000006 coarse_c_59 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_61 : coarse_certificate := ("1RB1RD_1RC---_0LA---_0RB---_------_------", CTw (SWside R 1 4 0)).
Lemma coarse_c_61_checked : coarse_candidate_check 1000006 coarse_c_61 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_63 : coarse_certificate := ("1RB1RD_1RC---_0LA---_1RB---_------_------", CTw (SWside R 1 4 0)).
Lemma coarse_c_63_checked : coarse_candidate_check 1000006 coarse_c_63 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_65 : coarse_certificate := ("1RB1RD_1RC---_0LA---_0RC---_------_------", CTw (SWside R 0 6 0)).
Lemma coarse_c_65_checked : coarse_candidate_check 1000006 coarse_c_65 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_67 : coarse_certificate := ("1RB1RD_1RC---_0LA---_1RC---_------_------", CTw (SWside R 2 3 1)).
Lemma coarse_c_67_checked : coarse_candidate_check 1000006 coarse_c_67 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_69 : coarse_certificate := ("1RB1RD_1RC---_0LA---_0RD---_------_------", CTw (SWside R 4 1 0)).
Lemma coarse_c_69_checked : coarse_candidate_check 1000006 coarse_c_69 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_71 : coarse_certificate := ("1RB1RD_1RC---_0LA---_1RD---_------_------", CTw (SWside R 4 1 0)).
Lemma coarse_c_71_checked : coarse_candidate_check 1000006 coarse_c_71 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_79 : coarse_certificate := ("1RB1LD_1RC---_0LA---_---1RA_------_------", CTw (SWside R 3 2 1)).
Lemma coarse_c_79_checked : coarse_candidate_check 1000006 coarse_c_79 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_84 : coarse_certificate := ("1RB1LD_1RC---_0LA---_---0LC_------_------", CTw (SWside L 0 6 2)).
Lemma coarse_c_84_checked : coarse_candidate_check 1000006 coarse_c_84 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_96 : coarse_certificate := ("1RB0RD_1RC---_0LA---_0LA---_------_------", CTw (SWside R 0 5 0)).
Lemma coarse_c_96_checked : coarse_candidate_check 1000006 coarse_c_96 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_97 : coarse_certificate := ("1RB0RD_1RC---_0LA---_0RA---_------_------", CTw (SWside R 0 5 0)).
Lemma coarse_c_97_checked : coarse_candidate_check 1000006 coarse_c_97 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_99 : coarse_certificate := ("1RB0RD_1RC---_0LA---_1RA---_------_------", CTw (SWside R 0 5 0)).
Lemma coarse_c_99_checked : coarse_candidate_check 1000006 coarse_c_99 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_100 : coarse_certificate := ("1RB0RD_1RC---_0LA---_0LB---_------_------", CTw (SWside R 1 4 0)).
Lemma coarse_c_100_checked : coarse_candidate_check 1000006 coarse_c_100 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_101 : coarse_certificate := ("1RB0RD_1RC---_0LA---_0RB---_------_------", CTw (SWside R 1 4 0)).
Lemma coarse_c_101_checked : coarse_candidate_check 1000006 coarse_c_101 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_103 : coarse_certificate := ("1RB0RD_1RC---_0LA---_1RB---_------_------", CTw (SWside R 1 4 0)).
Lemma coarse_c_103_checked : coarse_candidate_check 1000006 coarse_c_103 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_104 : coarse_certificate := ("1RB0RD_1RC---_0LA---_0LC---_------_------", CTw (SWside L 0 9 2)).
Lemma coarse_c_104_checked : coarse_candidate_check 1000006 coarse_c_104 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_105 : coarse_certificate := ("1RB0RD_1RC---_0LA---_0RC---_------_------", CTw (SWside R 0 6 0)).
Lemma coarse_c_105_checked : coarse_candidate_check 1000006 coarse_c_105 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_107 : coarse_certificate := ("1RB0RD_1RC---_0LA---_1RC---_------_------", CTw (SWside R 2 3 1)).
Lemma coarse_c_107_checked : coarse_candidate_check 1000006 coarse_c_107 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_109 : coarse_certificate := ("1RB0RD_1RC---_0LA---_0RD---_------_------", CTw (SWside R 4 1 0)).
Lemma coarse_c_109_checked : coarse_candidate_check 1000006 coarse_c_109 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_111 : coarse_certificate := ("1RB0RD_1RC---_0LA---_1RD---_------_------", CTw (SWside R 4 1 0)).
Lemma coarse_c_111_checked : coarse_candidate_check 1000006 coarse_c_111 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_116 : coarse_certificate := ("1RB0LD_1RC---_0LA---_---0LA_------_------", CTw (SWside L 0 5 2)).
Lemma coarse_c_116_checked : coarse_candidate_check 1000006 coarse_c_116 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_117 : coarse_certificate := ("1RB0LD_1RC---_0LA---_---0RA_------_------", CTw (SWside R 0 5 0)).
Lemma coarse_c_117_checked : coarse_candidate_check 1000006 coarse_c_117 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_119 : coarse_certificate := ("1RB0LD_1RC---_0LA---_---1RA_------_------", CTw (SWside R 0 5 0)).
Lemma coarse_c_119_checked : coarse_candidate_check 1000006 coarse_c_119 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_123 : coarse_certificate := ("1RB0LD_1RC---_0LA---_---1RB_------_------", CTw (SWside R 1 4 1)).
Lemma coarse_c_123_checked : coarse_candidate_check 1000006 coarse_c_123 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_124 : coarse_certificate := ("1RB0LD_1RC---_0LA---_---0LC_------_------", CTw (SWside L 0 6 2)).
Lemma coarse_c_124_checked : coarse_candidate_check 1000006 coarse_c_124 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_125 : coarse_certificate := ("1RB0LD_1RC---_0LA---_---0RC_------_------", CTw (SWside R 0 6 0)).
Lemma coarse_c_125_checked : coarse_candidate_check 1000006 coarse_c_125 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_136 : coarse_certificate := ("1RB1LC_1RC---_0LA0LA_------_------_------", CTw (SWside L 3 5 0)).
Lemma coarse_c_136_checked : coarse_candidate_check 1000006 coarse_c_136 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_137 : coarse_certificate := ("1RB1LC_1RC---_0LA0RA_------_------_------", CTw (SWside R 0 10 1)).
Lemma coarse_c_137_checked : coarse_candidate_check 1000006 coarse_c_137 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_139 : coarse_certificate := ("1RB1LC_1RC---_0LA1RA_------_------_------", CTw (SWside R 3 2 1)).
Lemma coarse_c_139_checked : coarse_candidate_check 1000006 coarse_c_139 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_144 : coarse_certificate := ("1RB1LC_1RC---_0LA0LC_------_------_------", CTw (SWside L 0 6 2)).
Lemma coarse_c_144_checked : coarse_candidate_check 1000006 coarse_c_144 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_145 : coarse_certificate := ("1RB1LC_1RC---_0LA0RC_------_------_------", CTw (SWside R 0 7 0)).
Lemma coarse_c_145_checked : coarse_candidate_check 1000006 coarse_c_145 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_146 : coarse_certificate := ("1RB1LC_1RC---_0LA1LC_------_------_------", CTw (SWside L 4 6 0)).
Lemma coarse_c_146_checked : coarse_candidate_check 1000006 coarse_c_146 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_147 : coarse_certificate := ("1RB1LC_1RC---_0LA1RC_------_------_------", CTw (SWside R 2 4 2)).
Lemma coarse_c_147_checked : coarse_candidate_check 1000006 coarse_c_147 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_152 : coarse_certificate := ("1RB0LC_1RC---_0LA0LA_------_------_------", CTw (SWside L 0 5 2)).
Lemma coarse_c_152_checked : coarse_candidate_check 1000006 coarse_c_152 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_153 : coarse_certificate := ("1RB0LC_1RC---_0LA0RA_------_------_------", CTw (SWside R 0 5 0)).
Lemma coarse_c_153_checked : coarse_candidate_check 1000006 coarse_c_153 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_c_155 : coarse_certificate := ("1RB0LC_1RC---_0LA1RA_------_------_------", CTw (SWside R 0 5 0)).
Lemma coarse_c_155_checked : coarse_candidate_check 1000006 coarse_c_155 = true.
Proof. vm_compute. reflexivity. Qed.
Definition coarse_candidates_Small : list coarse_certificate := [coarse_c_0; coarse_c_1; coarse_c_2; coarse_c_3; coarse_c_4; coarse_c_5; coarse_c_6; coarse_c_7; coarse_c_8; coarse_c_9; coarse_c_10; coarse_c_11; coarse_c_12; coarse_c_13; coarse_c_14; coarse_c_15; coarse_c_16; coarse_c_17; coarse_c_18; coarse_c_19; coarse_c_20; coarse_c_21; coarse_c_22; coarse_c_23; coarse_c_24; coarse_c_29; coarse_c_31; coarse_c_32; coarse_c_36; coarse_c_38; coarse_c_40; coarse_c_42; coarse_c_43; coarse_c_54; coarse_c_59; coarse_c_61; coarse_c_63; coarse_c_65; coarse_c_67; coarse_c_69; coarse_c_71; coarse_c_79; coarse_c_84; coarse_c_96; coarse_c_97; coarse_c_99; coarse_c_100; coarse_c_101; coarse_c_103; coarse_c_104; coarse_c_105; coarse_c_107; coarse_c_109; coarse_c_111; coarse_c_116; coarse_c_117; coarse_c_119; coarse_c_123; coarse_c_124; coarse_c_125; coarse_c_136; coarse_c_137; coarse_c_139; coarse_c_144; coarse_c_145; coarse_c_146; coarse_c_147; coarse_c_152; coarse_c_153; coarse_c_155].
Definition coarse_roster_Small := map coarse_tm coarse_candidates_Small.
Theorem coarse_roster_Small_safe : Forall (source_table_safe 1000006) coarse_roster_Small.
Proof. apply coarse_roster_safe. unfold coarse_candidates_Small. cbn [forallb]. rewrite coarse_c_0_checked, coarse_c_1_checked, coarse_c_2_checked, coarse_c_3_checked, coarse_c_4_checked, coarse_c_5_checked, coarse_c_6_checked, coarse_c_7_checked, coarse_c_8_checked, coarse_c_9_checked, coarse_c_10_checked, coarse_c_11_checked, coarse_c_12_checked, coarse_c_13_checked, coarse_c_14_checked, coarse_c_15_checked, coarse_c_16_checked, coarse_c_17_checked, coarse_c_18_checked, coarse_c_19_checked, coarse_c_20_checked, coarse_c_21_checked, coarse_c_22_checked, coarse_c_23_checked, coarse_c_24_checked, coarse_c_29_checked, coarse_c_31_checked, coarse_c_32_checked, coarse_c_36_checked, coarse_c_38_checked, coarse_c_40_checked, coarse_c_42_checked, coarse_c_43_checked, coarse_c_54_checked, coarse_c_59_checked, coarse_c_61_checked, coarse_c_63_checked, coarse_c_65_checked, coarse_c_67_checked, coarse_c_69_checked, coarse_c_71_checked, coarse_c_79_checked, coarse_c_84_checked, coarse_c_96_checked, coarse_c_97_checked, coarse_c_99_checked, coarse_c_100_checked, coarse_c_101_checked, coarse_c_103_checked, coarse_c_104_checked, coarse_c_105_checked, coarse_c_107_checked, coarse_c_109_checked, coarse_c_111_checked, coarse_c_116_checked, coarse_c_117_checked, coarse_c_119_checked, coarse_c_123_checked, coarse_c_124_checked, coarse_c_125_checked, coarse_c_136_checked, coarse_c_137_checked, coarse_c_139_checked, coarse_c_144_checked, coarse_c_145_checked, coarse_c_146_checked, coarse_c_147_checked, coarse_c_152_checked, coarse_c_153_checked, coarse_c_155_checked. reflexivity. Qed.
Print Assumptions coarse_roster_Small_safe.
