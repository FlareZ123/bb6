From BusyCoq Require Import Enumerate62 Agent8QueueCheckpoint Agent8PackedChunk2_32_32.
From Coq Require Import List NArith Strings.String.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.

(* Successful original-source CI run 45460360691; ordered literal active and held data. *)
Definition resume_data_1000000 : packed_queue := ([
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_0LA---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_0RA---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_1LA---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_1RA---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_0LB---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_0RB---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_1LB---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_1RB---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_0LC---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_0RC---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_1LC---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_1RC---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_0LD---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_0RD---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_1LD---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_1RD---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_0LE---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_0RE---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_1LE---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_1RE---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_0LF---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_0RF---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_1LF---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1LF0LA_1RF---", 1, 6);
  ("1RB1RD_1RC0RE_0LA0RB_1LA1LD_1RF0LA_------", 2, 6);
  ("1RB1RD_1RC0RE_0LA1LB_1LA1LD_---0LA_------", 3, 5);
  ("1RB1RD_1RC0RE_0LA1RB_1LA1LD_---0LA_------", 3, 5);
  ("1RB1RD_1RC0RE_0LA0LC_1LA1LD_---0LA_------", 3, 5);
  ("1RB1RD_1RC0RE_0LA0RC_1LA1LD_---0LA_------", 3, 5);
  ("1RB1RD_1RC0RE_0LA1LC_1LA1LD_---0LA_------", 3, 5);
  ("1RB1RD_1RC0RE_0LA1RC_1LA1LD_---0LA_------", 3, 5);
  ("1RB1RD_1RC0RE_0LA0LD_1LA1LD_---0LA_------", 3, 5);
  ("1RB1RD_1RC0RE_0LA0RD_1LA1LD_---0LA_------", 3, 5);
  ("1RB1RD_1RC0RE_0LA1LD_1LA1LD_---0LA_------", 3, 5);
  ("1RB1RD_1RC0RE_0LA1RD_1LA1LD_---0LA_------", 3, 5);
  ("1RB1RD_1RC0RE_0LA0LE_1LA1LD_---0LA_------", 3, 5);
  ("1RB1RD_1RC0RE_0LA0RE_1LA1LD_---0LA_------", 3, 5);
  ("1RB1RD_1RC0RE_0LA1LE_1LA1LD_---0LA_------", 3, 5);
  ("1RB1RD_1RC0RE_0LA1RE_1LA1LD_---0LA_------", 3, 5);
  ("1RB1RD_1RC0RE_0LA0LF_1LA1LD_---0LA_------", 3, 6);
  ("1RB1RD_1RC0RE_0LA0RF_1LA1LD_---0LA_------", 3, 6);
  ("1RB1RD_1RC0RE_0LA1LF_1LA1LD_---0LA_------", 3, 6);
  ("1RB1RD_1RC0RE_0LA1RF_1LA1LD_---0LA_------", 3, 6);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0RA_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1LA_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1RA_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0LB_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0RB_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1LB_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1RB_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0LC_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0RC_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1LC_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1RC_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0LD_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0RD_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1LD_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1RD_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0LE_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0RE_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1LE_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1RE_------", 4, 5);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0LF_------", 4, 6);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---0RF_------", 4, 6);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1LF_------", 4, 6);
  ("1RB1RD_1RC0RE_0LA---_1LA1LD_---1RF_------", 4, 6);
  ("1RB1RD_1RC1LE_0LA---_1LA1LD_------_------", 5, 5);
  ("1RB1RD_1RC1RE_0LA---_1LA1LD_------_------", 5, 5);
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
], [
  ("1RB1RD_1RC0LD_0LA0RE_1LA1LB_0RF---_0LA1RA", 1, 6)
]).

Theorem resume_data_1000000_exact :
  SearchQueue_upds decider (SearchQueue_upds decider (q_i 2 32) 32%N)
    1000000%N = decode_queue resume_data_1000000.
Proof.
  rewrite packed_chunk_2_32_32_exact.
  apply source_checkpoint_decode.
  - rewrite <- packed_chunk_2_32_32_exact.
    apply checkpoint_updates_canonical, checkpoint_chunk_canonical.
  - vm_compute. reflexivity.
Qed.
Print Assumptions resume_data_1000000_exact.
