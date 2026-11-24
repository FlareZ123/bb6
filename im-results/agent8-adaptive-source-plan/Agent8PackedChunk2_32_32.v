From BusyCoq Require Import Enumerate62 Agent8QueueCheckpoint.
From Coq Require Import List NArith Strings.String.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.

(* Literal complete queue exported by CI run 45448919921, original
   source 33209bc7dc282b38c8cd6be507bfc551fea56108.
   This proof can replay the data independently of the expiring artifact. *)
Definition packed_chunk_2_32_32 : packed_queue :=
  ([
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LA_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RA_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LB_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RB_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LB_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RB_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LC_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RC_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LC_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RC_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LD_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RD_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LD_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RD_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LE_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RE_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LE_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RE_------", 3, 5);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LF_------", 3, 6);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RF_------", 3, 6);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LF_------", 3, 6);
    ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RF_------", 3, 6);
    ("1RB1RD_1RC1LB_0LA0RE_1LA0LB_------_------", 4, 5);
    ("1RB1RD_1RC1LB_0LA1LE_1LA0LB_------_------", 4, 5);
    ("1RB1RD_1RC1LB_0LA1RE_1LA0LB_------_------", 4, 5);
    ("1RB1RD_1RC1RB_0LA---_1LA0LB_------_------", 5, 4);
    ("1RB1RD_1RC0LC_0LA---_1LA0LB_------_------", 5, 4);
    ("1RB1RD_1RC0RC_0LA---_1LA0LB_------_------", 5, 4);
    ("1RB1RD_1RC1LC_0LA---_1LA0LB_------_------", 5, 4);
    ("1RB1RD_1RC1RC_0LA---_1LA0LB_------_------", 5, 4);
    ("1RB1RD_1RC0LD_0LA---_1LA0LB_------_------", 5, 4);
    ("1RB1RD_1RC0RD_0LA---_1LA0LB_------_------", 5, 4);
    ("1RB1RD_1RC1LD_0LA---_1LA0LB_------_------", 5, 4);
    ("1RB1RD_1RC1RD_0LA---_1LA0LB_------_------", 5, 4);
    ("1RB1RD_1RC0LE_0LA---_1LA0LB_------_------", 5, 5);
    ("1RB1RD_1RC0RE_0LA---_1LA0LB_------_------", 5, 5);
    ("1RB1RD_1RC1LE_0LA---_1LA0LB_------_------", 5, 5);
    ("1RB1RD_1RC1RE_0LA---_1LA0LB_------_------", 5, 5);
    ("1RB1RD_1RC---_0LA---_1LA0RB_------_------", 6, 4);
    ("1RB1RD_1RC---_0LA---_1LA1LB_------_------", 6, 4);
    ("1RB1RD_1RC---_0LA---_1LA1RB_------_------", 6, 4);
    ("1RB1RD_1RC---_0LA---_1LA0LC_------_------", 6, 4);
    ("1RB1RD_1RC---_0LA---_1LA0RC_------_------", 6, 4);
    ("1RB1RD_1RC---_0LA---_1LA1LC_------_------", 6, 4);
    ("1RB1RD_1RC---_0LA---_1LA1RC_------_------", 6, 4);
    ("1RB1RD_1RC---_0LA---_1LA0LD_------_------", 6, 4);
    ("1RB1RD_1RC---_0LA---_1LA0RD_------_------", 6, 4);
    ("1RB1RD_1RC---_0LA---_1LA1LD_------_------", 6, 4);
    ("1RB1RD_1RC---_0LA---_1LA1RD_------_------", 6, 4);
    ("1RB1RD_1RC---_0LA---_1LA0LE_------_------", 6, 5);
    ("1RB1RD_1RC---_0LA---_1LA0RE_------_------", 6, 5);
    ("1RB1RD_1RC---_0LA---_1LA1LE_------_------", 6, 5);
    ("1RB1RD_1RC---_0LA---_1LA1RE_------_------", 6, 5);
    ("1RB1RD_1RC---_0LA---_1RA---_------_------", 7, 4);
    ("1RB1RD_1RC---_0LA---_0LB---_------_------", 7, 4);
    ("1RB1RD_1RC---_0LA---_0RB---_------_------", 7, 4);
    ("1RB1RD_1RC---_0LA---_1LB---_------_------", 7, 4);
    ("1RB1RD_1RC---_0LA---_1RB---_------_------", 7, 4);
    ("1RB1RD_1RC---_0LA---_0LC---_------_------", 7, 4);
    ("1RB1RD_1RC---_0LA---_0RC---_------_------", 7, 4);
    ("1RB1RD_1RC---_0LA---_1LC---_------_------", 7, 4);
    ("1RB1RD_1RC---_0LA---_1RC---_------_------", 7, 4);
    ("1RB1RD_1RC---_0LA---_0LD---_------_------", 7, 4);
    ("1RB1RD_1RC---_0LA---_0RD---_------_------", 7, 4);
    ("1RB1RD_1RC---_0LA---_1LD---_------_------", 7, 4);
    ("1RB1RD_1RC---_0LA---_1RD---_------_------", 7, 4);
    ("1RB1RD_1RC---_0LA---_0LE---_------_------", 7, 5);
    ("1RB1RD_1RC---_0LA---_0RE---_------_------", 7, 5);
    ("1RB1RD_1RC---_0LA---_1LE---_------_------", 7, 5);
    ("1RB1RD_1RC---_0LA---_1RE---_------_------", 7, 5);
    ("1RB1LD_1RC---_0LA---_---0LA_------_------", 7, 4);
    ("1RB1LD_1RC---_0LA---_---0RA_------_------", 7, 4);
    ("1RB1LD_1RC---_0LA---_---1LA_------_------", 7, 4);
    ("1RB1LD_1RC---_0LA---_---1RA_------_------", 7, 4);
    ("1RB1LD_1RC---_0LA---_---0LB_------_------", 7, 4);
    ("1RB1LD_1RC---_0LA---_---0RB_------_------", 7, 4);
    ("1RB1LD_1RC---_0LA---_---1LB_------_------", 7, 4);
    ("1RB1LD_1RC---_0LA---_---1RB_------_------", 7, 4);
    ("1RB1LD_1RC---_0LA---_---0LC_------_------", 7, 4);
    ("1RB1LD_1RC---_0LA---_---0RC_------_------", 7, 4);
    ("1RB1LD_1RC---_0LA---_---1LC_------_------", 7, 4);
    ("1RB1LD_1RC---_0LA---_---1RC_------_------", 7, 4);
    ("1RB1LD_1RC---_0LA---_---0LD_------_------", 7, 4);
    ("1RB1LD_1RC---_0LA---_---0RD_------_------", 7, 4)
   ], []).

Theorem packed_chunk_2_32_32_exact :
  SearchQueue_upds decider (q_i 2 32) 32%N =
  decode_queue packed_chunk_2_32_32.
Proof.
  apply source_checkpoint_decode.
  - apply checkpoint_chunk_canonical.
  - vm_compute. reflexivity.
Qed.

Print Assumptions packed_chunk_2_32_32_exact.
