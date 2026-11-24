From BusyCoq Require Import Enumerate62 Agent8QueueCheckpoint Agent8PackedRoot.
From Coq Require Import List NArith Strings.String.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.

(* Source-checked output of original-source run 45463102601, artifact 14954386853.
   The emitted dynamic theorem chunk_data_exact was checked against source.
   This literal version reproduces its ordered data and proof obligation. *)
Definition packed_chunk_12800_20_1000000 : packed_queue :=
([("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0LB1RF", 1, 6); ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0RB1RF", 1, 6);
  ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1LB1RF", 1, 6); ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1RB1RF", 1, 6);
  ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0LC1RF", 1, 6); ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0RC1RF", 1, 6);
  ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1LC1RF", 1, 6); ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1RC1RF", 1, 6);
  ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0LD1RF", 1, 6); ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0RD1RF", 1, 6);
  ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1LD1RF", 1, 6); ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1RD1RF", 1, 6);
  ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0LE1RF", 1, 6); ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0RE1RF", 1, 6);
  ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1LE1RF", 1, 6); ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1RE1RF", 1, 6);
  ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0LF1RF", 1, 6); ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0RF1RF", 1, 6);
  ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1LF1RF", 1, 6); ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1RF1RF", 1, 6);
  ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1RF_------", 3, 6); ("1RB1RC_0LA0RD_0LB0LF_1RE---_1LC---_------", 4, 6);
  ("1RB1RC_0LA0RD_0LB0RF_1RE---_1LC---_------", 4, 6); ("1RB1RC_0LA0RD_0LB1LF_1RE---_1LC---_------", 4, 6);
  ("1RB1RC_0LA0RD_0LB1RF_1RE---_1LC---_------", 4, 6); ("1RB1RC_0LA0RD_0LB---_1RE---_1RC---_------", 5, 5);
  ("1RB1RC_0LA0RD_0LB---_1RE---_0LD---_------", 5, 5); ("1RB1RC_0LA0RD_0LB---_1RE---_0RD---_------", 5, 5);
  ("1RB1RC_0LA0RD_0LB---_1RE---_1LD---_------", 5, 5); ("1RB1RC_0LA0RD_0LB---_1RE---_1RD---_------", 5, 5);
  ("1RB1RC_0LA0RD_0LB---_1RE---_0LE---_------", 5, 5); ("1RB1RC_0LA0RD_0LB---_1RE---_0RE---_------", 5, 5);
  ("1RB1RC_0LA0RD_0LB---_1RE---_1LE---_------", 5, 5); ("1RB1RC_0LA0RD_0LB---_1RE---_1RE---_------", 5, 5);
  ("1RB1RC_0LA0RD_0LB---_1RE---_0LF---_------", 5, 6); ("1RB1RC_0LA0RD_0LB---_1RE---_0RF---_------", 5, 6);
  ("1RB1RC_0LA0RD_0LB---_1RE---_1LF---_------", 5, 6); ("1RB1RC_0LA0RD_0LB---_1RE---_1RF---_------", 5, 6);
  ("1RB1RC_0LA1LD_0LB---_------_------_------", 7, 4); ("1RB1RC_0LA1RD_0LB---_------_------_------", 7, 4);
  ("1RB1RC_0LA---_1LA0LA_------_------_------", 7, 3); ("1RB1RC_0LA---_1LA0RA_------_------_------", 7, 3);
  ("1RB1RC_0LA---_1LA1LA_------_------_------", 7, 3); ("1RB1RC_0LA---_1LA1RA_------_------_------", 7, 3);
  ("1RB1RC_0LA---_1LA0LB_------_------_------", 7, 3); ("1RB1RC_0LA---_1LA0RB_------_------_------", 7, 3);
  ("1RB1RC_0LA---_1LA1LB_------_------_------", 7, 3); ("1RB1RC_0LA---_1LA1RB_------_------_------", 7, 3);
  ("1RB1RC_0LA---_1LA0LC_------_------_------", 7, 3); ("1RB1RC_0LA---_1LA0RC_------_------_------", 7, 3);
  ("1RB1RC_0LA---_1LA1LC_------_------_------", 7, 3); ("1RB1RC_0LA---_1LA1RC_------_------_------", 7, 3);
  ("1RB1RC_0LA---_1LA0LD_------_------_------", 7, 4); ("1RB1RC_0LA---_1LA0RD_------_------_------", 7, 4);
  ("1RB1RC_0LA---_1LA1LD_------_------_------", 7, 4); ("1RB1RC_0LA---_1LA1RD_------_------_------", 7, 4)], []).

Theorem packed_chunk_12800_20_1000000_exact :
  SearchQueue_upds decider (q_i 12800 20) 1000000%N =
    decode_queue packed_chunk_12800_20_1000000.
Proof.
  apply source_checkpoint_decode.
  - apply checkpoint_chunk_canonical.
  - vm_compute. reflexivity.
Qed.
Print Assumptions packed_chunk_12800_20_1000000_exact.
