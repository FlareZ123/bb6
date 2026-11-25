From BusyCoq Require Import Enumerate62 CTL62 Individual62 Agent8WeightedSource Agent47SourceTree Agent47SourceWitness.
From Coq Require Import List Bool Strings.String.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

(* The 95 source certificates are grouped by estimated checker work so
   independent Coq reductions can compile in parallel. The concatenated
   roster contains each original certificate exactly once; roster order is
   immaterial to source_roster_covers, while checkpoint-obligation order is
   preserved separately. *)

Definition q2800_trees_shard01 : list (string * source_tree) :=
[
  ("1RB0RD_1LC1LA_0LE1RA_0LC0RB_0RA1LF_1LB---", STcert (SWside R 21 7 0));
  ("1RB0RD_1LC1LA_0LE1RA_0LC1RB_0RA1LF_1LB---", STcert (SWside R 1 20 5));
  ("1RB0RD_1LC1LA_0LE1RA_0LC0LC_0RA1LF_1LB---", STcert (SWside L 5 17 0));
  ("1RB0RD_1LC1LA_0LE1RA_0LC1RE_0RA1LF_1LB---", STcert (SWlast 16));
  ("1RB0RD_1LC1LA_0LE1RA_0LC0RF_0RA1LF_1LB---", STcert (SWlast 15));
  ("1RB0RD_1LC1RA_0LE1RA_0LC---_0RA1LF_1LB---", source_split 14 (D,S1) [STcert (SWlast 22); STcert (SWside R 15 16 3); STcert (SWlast 24); STcert (SWlast 22); STcert (SWlast 21); STcert (SWlast 27); STcert (SWside R 13 4 1); STcert (SWside R 12 10 0); STcert (SWlast 17); STcert (SWlast 37); STcert (SWlast 17); STcert (SWside R 12 6 0); STcert (SWlast 24); STcert (SWside R 12 14 0); STcert (SWlast 26); STcert (SWlast 24); STcert (SWside R 12 12 0); STcert (SWlast 27); STcert (SWside R 12 16 0); STcert (SWside R 12 12 0); STcert (SWlast 21); STcert (SWlast 19); STcert (SWside R 12 4 0); STcert (SWside R 12 10 0)]);
  ("1RB0RD_1LC0LB_0LE1RA_0LC---_0RA1LF_1LB---", STcert (SWside L 8 6 0));
  ("1RB0RD_1LC1LB_0LE1RA_0LC---_0RA1LF_1LB---", STcert (SWside L 8 6 0));
  ("1RB0RD_1LC0RC_0LE1RA_0LC---_0RA1LF_1LB---", STcert (SWside L 2 18 2));
  ("1RB0RD_1LC1LD_0LE1RA_0LC---_0RA1LF_1LB---", source_split 13 (D,S1) [STcert (SWlast 36); STcert (SWside R 0 20 4); STcert (SWside L 11 3 1); STcert (SWlast 39); STcert (SWside L 8 6 0); STcert (SWside L 4 20 0); STcert (SWside L 8 6 0); STcert (SWside R 12 2 1); STcert (SWside L 5 16 0); STcert (SWlast 39); STcert (SWside L 9 5 1); STcert (SWside R 12 8 1); STcert (SWside L 0 17 2); STcert (SWside R 0 20 4); STcert (SWside L 13 14 0); STcert (SWlast 26); STcert (SWside R 10 4 0); STcert (SWside L 6 8 0); STcert (SWside R 0 28 4); STcert (SWlast 15); STcert (SWside L 7 7 0); STcert (SWlast 14); STcert (SWside L 7 7 0); STcert (SWlast 14)]);
  ("1RB0RD_1LC0RE_0LE1RA_0LC---_0RA1LF_1LB---", STcert (SWside L 6 10 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_0LB1LF_1LB---", STcert (SWside L 8 3 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_0RB1LF_1LB---", STcert (SWside L 8 3 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_0RD1LF_1LB---", STcert (SWside L 9 3 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_0LE1LF_1LB---", STcert (SWside L 10 1 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_1LE1LF_1LB---", STcert (SWside L 10 1 0));
  ("1RB0LD_1LC---_---1RA_---0RA_------_------", STcert (SWside R 0 5 0));
  ("1RB1RC_1LC---_0LA1RA_------_------_------", STcert (SWside R 3 2 0));
  ("1RB1RC_1LC---_0LC1RA_------_------_------", STcert (SWside R 0 6 0));
  ("1RB1RC_1LC---_1LC1RA_------_------_------", STcert (SWside R 2 3 0));
  ("1RB0RC_1LC---_0LA1RA_------_------_------", STcert (SWside R 0 5 0));
  ("1RB0RC_1LC---_1LB1RA_------_------_------", STcert (SWside R 0 9 0));
  ("1RB0RC_1LC---_1RB1RA_------_------_------", STcert (SWside R 1 4 1));
  ("1RB0RC_1LC---_0LC1RA_------_------_------", STcert (SWside R 0 7 0));
  ("1RB0RC_1LC---_1LC1RA_------_------_------", STcert (SWside R 0 9 0));
  ("1RB0RC_1LC---_1RC1RA_------_------_------", STcert (SWside R 4 1 0));
  ("1RB1LB_1LC1RC_---1RA_------_------_------", STcert (SWside R 0 6 0));
  ("1RB0RB_1LC---_1RA1RA_------_------_------", STcert (SWside R 3 3 0));
  ("1RB0RB_1LC---_1RC1RA_------_------_------", STcert (SWside R 0 7 0));
  ("1RB0LB_1LC1RA_---1RA_------_------_------", STcert (SWside R 0 5 0))
].

Definition q2800_trees_shard02 : list (string * source_tree) :=
[
  ("1RB0RD_1LC1LA_0LE1RA_0LC1RA_0RA1LF_1LB---", STcert (SWlast 24));
  ("1RB0RD_1LC1LA_0LE1RA_0LC1LB_0RA1LF_1LB---", STcert (SWside L 8 7 0));
  ("1RB0RD_1LC1LA_0LE1RA_0LC0RC_0RA1LF_1LB---", STcert (SWside L 2 13 2));
  ("1RB0RD_1LC1LA_0LE1RA_0LC1RC_0RA1LF_1LB---", STcert (SWlast 20));
  ("1RB0RD_1LC1LA_0LE1RA_0LC1LD_0RA1LF_1LB---", STcert (SWside R 21 6 1));
  ("1RB0RD_1LC1LA_0LE1RA_0LC0LE_0RA1LF_1LB---", STcert (SWside R 0 26 4));
  ("1RB0RD_1LC1LA_0LE1RA_0LC0RE_0RA1LF_1LB---", STcert (SWside L 6 9 0));
  ("1RB0RD_1LC1LA_0LE1RA_0LC1RF_0RA1LF_1LB---", STcert (SWlast 15));
  ("1RB0RD_1LC0LD_0LE1RA_0LC---_0RA1LF_1LB---", source_split 13 (D,S1) [STcert (SWside L 0 14 2); STcert (SWside R 0 20 4); STcert (SWside L 11 3 1); STcert (SWlast 27); STcert (SWside L 8 6 0); STcert (SWside R 8 6 2); STcert (SWside L 8 6 0); STcert (SWside L 0 31 2); STcert (SWside L 0 16 2); STcert (SWside R 0 26 4); STcert (SWside L 9 5 1); STcert (SWside L 5 9 0); STcert (SWside L 0 17 2); STcert (SWside R 18 16 1); STcert (SWside L 13 14 0); STcert (SWlast 33); STcert (SWside L 0 37 2); STcert (SWside R 0 18 4); STcert (SWside R 20 20 1); STcert (SWlast 47); STcert (SWside L 7 7 0); STcert (SWside L 7 7 0); STcert (SWside L 7 7 0); STcert (SWside L 0 19 2)]);
  ("1RB0RD_1LC0LE_0LE1RA_0LC---_0RA1LF_1LB---", STcert (SWside L 6 7 0));
  ("1RB0RD_1LC0RF_0LE1RA_0LC---_0RA1LF_1LB---", source_split 13 (F,S1) [STcert (SWlast 18); STcert (SWlast 29); STcert (SWlast 23); STcert (SWside L 3 18 1); STcert (SWside L 1 13 1); STcert (SWlast 31); STcert (SWlast 17); STcert (SWlast 19); STcert (SWside L 5 9 0); STcert (SWside R 13 9 0); STcert (SWside L 5 9 0); STcert (SWside R 13 9 0); STcert (SWlast 20); STcert (SWlast 14); STcert (SWlast 27); STcert (SWlast 14); STcert (SWlast 21); STcert (SWlast 19); STcert (SWlast 16); STcert (SWside R 13 2 0); STcert (SWside L 7 10 0); STcert (SWlast 54); STcert (SWside L 7 10 0); STcert (SWside R 14 3 0)]);
  ("1RB0RD_1LC---_0LE1RA_0LC---_0LC1LF_1LB---", STcert (SWside L 9 2 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_1LC1LF_1LB---", STcert (SWside L 9 2 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_0LD1LF_1LB---", STcert (SWside L 9 3 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_1LD1LF_1LB---", STcert (SWside L 9 3 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_0RF1LF_1LB---", STcert (SWside L 7 4 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_1LF1LF_1LB---", STcert (SWside L 7 4 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_---1LF_1LF---", STcert (SWside L 7 1 0));
  ("1RB0RD_1LC---_---1RA_1RD---_------_------", STcert (SWside R 4 1 0));
  ("1RB0LD_1LC---_---1RA_---0LA_------_------", STcert (SWside L 0 5 1));
  ("1RB1RC_1LC---_0RA1RA_------_------_------", STcert (SWside R 0 5 0));
  ("1RB1RC_1LC---_1RB1RA_------_------_------", STcert (SWside R 1 4 1));
  ("1RB1RC_1LC---_0RC1RA_------_------_------", STcert (SWside R 4 1 0));
  ("1RB0RC_1LC---_0RA1RA_------_------_------", STcert (SWside R 0 5 0));
  ("1RB0RC_1LC---_0RC1RA_------_------_------", STcert (SWside R 4 1 0));
  ("1RB1LB_1LC0LA_---1RA_------_------_------", STcert (SWside L 0 5 1));
  ("1RB1LB_1LC1RB_---1RA_------_------_------", STcert (SWside R 1 5 1));
  ("1RB1LB_1LC0RC_---1RA_------_------_------", STcert (SWside R 0 6 0));
  ("1RB0LB_1LC0LA_---1RA_------_------_------", STcert (SWside L 0 5 1))
].

Definition q2800_trees_shard03 : list (string * source_tree) :=
[
  ("1RB0RD_1LC1LA_0LE1RA_0LC0LB_0RA1LF_1LB---", STcert (SWside L 8 7 0));
  ("1RB0RD_1LC1LA_0LE1RA_0LC1LC_0RA1LF_1LB---", STcert (SWside R 9 6 1));
  ("1RB0RD_1LC1LA_0LE1RA_0LC0LD_0RA1LF_1LB---", STcert (SWside L 0 18 2));
  ("1RB0RD_1LC1LA_0LE1RA_0LC0RD_0RA1LF_1LB---", STcert (SWside R 0 20 4));
  ("1RB0RD_1LC1LA_0LE1RA_0LC1RD_0RA1LF_1LB---", STcert (SWlast 26));
  ("1RB0RD_1LC1LA_0LE1RA_0LC1LE_0RA1LF_1LB---", STcert (SWside R 0 26 4));
  ("1RB0RD_1LC1LA_0LE1RA_0LC0LF_0RA1LF_1LB---", STcert (SWside L 7 8 0));
  ("1RB0RD_1LC1LA_0LE1RA_0LC1LF_0RA1LF_1LB---", STcert (SWside L 7 8 0));
  ("1RB0RD_1LC1LC_0LE1RA_0LC---_0RA1LF_1LB---", source_split 15 (D,S1) [STcert (SWlast 28); STcert (SWside R 13 16 0); STcert (SWlast 28); STcert (SWside L 9 13 4); STcert (SWside L 1 15 1); STcert (SWside L 9 19 4); STcert (SWside R 13 4 0); STcert (SWside L 9 15 4); STcert (SWside L 5 11 0); STcert (SWlast 24); STcert (SWside L 5 11 0); STcert (SWlast 24); STcert (SWlast 32); STcert (SWside R 13 16 0); STcert (SWlast 32); STcert (SWlast 26); STcert (SWside L 9 17 4); STcert (SWside R 13 6 0); STcert (SWside R 13 20 0); STcert (SWlast 17); STcert (SWside L 9 9 2); STcert (SWlast 16); STcert (SWside L 9 9 2); STcert (SWlast 16)]);
  ("1RB0RD_1LC1RD_0LE1RA_0LC---_0RA1LF_1LB---", source_split 13 (D,S1) [STcert (SWside L 3 11 1); STcert (SWside R 12 14 0); STcert (SWlast 32); STcert (SWlast 18); STcert (SWlast 28); STcert (SWlast 24); STcert (SWside R 12 2 0); STcert (SWlast 24); STcert (SWlast 26); STcert (SWlast 22); STcert (SWlast 19); STcert (SWlast 22); STcert (SWside L 0 19 2); STcert (SWside R 12 14 0); STcert (SWside L 13 16 0); STcert (SWlast 24); STcert (SWlast 15); STcert (SWside R 12 4 0); STcert (SWlast 15); STcert (SWlast 15); STcert (SWlast 14); STcert (SWlast 14); STcert (SWlast 14); STcert (SWlast 14)]);
  ("1RB0RD_1LC1LE_0LE1RA_0LC---_0RA1LF_1LB---", STcert (SWside L 6 7 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_1LB1LF_1LB---", STcert (SWside L 8 3 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_0RC1LF_1LB---", STcert (SWside R 9 2 1));
  ("1RB0RD_1LC---_0LE1RA_0LC---_1RC1LF_1LB---", STcert (SWside L 5 6 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_0RE1LF_1LB---", STcert (SWside L 6 6 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_0LF1LF_1LB---", STcert (SWside L 7 4 0));
  ("1RB0RD_1LC---_0LE1RA_0LC---_---1LF_0RE---", STcert (SWside R 6 2 1));
  ("1RB0RD_1LC---_0LE1RA_0LC---_---1LF_0LF---", STcert (SWside L 7 1 0));
  ("1RB0RD_1LC---_---1RA_0RD---_------_------", STcert (SWside R 4 1 0));
  ("1RB0LD_1LC---_---1RA_---1RA_------_------", STcert (SWside R 0 5 0));
  ("1RB0LD_1LC---_---1RA_---1RB_------_------", STcert (SWside R 1 4 1));
  ("1RB1RC_1LC---_1LA1RA_------_------_------", STcert (SWside R 0 7 0));
  ("1RB1RC_1LC---_1RA1RA_------_------_------", STcert (SWside R 0 5 0));
  ("1RB1RC_1LC---_1RC1RA_------_------_------", STcert (SWside R 4 1 0));
  ("1RB0RC_1LC---_1RA1RA_------_------_------", STcert (SWside R 0 5 0));
  ("1RB0RC_1LC---_0LB1RA_------_------_------", STcert (SWside R 1 4 1));
  ("1RB1LB_1LC1RA_---1RA_------_------_------", STcert (SWside R 3 2 1));
  ("1RB0RB_1LC---_0RA1RA_------_------_------", STcert (SWside R 3 3 0));
  ("1RB0RB_1LC---_0RC1RA_------_------_------", STcert (SWside R 0 7 0));
  ("1RB0LB_1LC0RA_---1RA_------_------_------", STcert (SWside R 0 5 0))
].

Definition q2800_trees_shard04 : list (string * source_tree) :=
[
  ("1RB0RD_1LC1RC_0LE1RA_0LC---_0RA1LF_1LB---", source_split 18 (F,S1) [STcert (SWlast 27); STcert (SWside L 0 42 2); STcert (SWlast 20); STcert (SWside L 3 21 1); STcert (SWside L 5 15 0); STcert (SWside L 5 26 0); STcert (SWside L 8 18 3); STcert (SWside R 16 4 2); STcert (SWside R 16 6 3); STcert (SWside R 13 9 1); STcert (SWlast 21); STcert (SWside R 13 9 1); STcert (SWlast 19); STcert (SWlast 19); STcert (SWlast 19); STcert (SWlast 19); STcert (SWside L 6 13 1); STcert (SWside L 6 22 1); STcert (SWlast 28); STcert (SWside R 17 2 1); STcert (SWlast 31); STcert (SWside L 5 17 0); STcert (SWlast 28); STcert (SWside R 13 12 1)]);
  ("1RB0RD_1LC1LF_0LE1RA_0LC---_0RA1LF_1LB---", source_split 13 (F,S1) [STcert (SWlast 18); STcert (SWlast 15); STcert (SWside L 11 3 1); STcert (SWlast 15); STcert (SWside L 8 6 0); STcert (SWside L 7 8 0); STcert (SWside L 8 6 0); STcert (SWside R 12 2 1); STcert (SWlast 20); STcert (SWlast 16); STcert (SWside L 9 5 1); STcert (SWlast 16); STcert (SWside L 0 17 2); STcert (SWlast 14); STcert (SWlast 21); STcert (SWlast 14); STcert (SWside R 10 4 0); STcert (SWside L 6 8 0); STcert (SWlast 16); STcert (SWside R 13 2 0); STcert (SWside L 7 7 0); STcert (SWside R 14 9 0); STcert (SWside L 7 7 0); STcert (SWside R 14 5 0)]);
  ("1RB0RD_1LC1RF_0LE1RA_0LC---_0RA1LF_1LB---", source_split 13 (F,S1) [STcert (SWside L 3 11 1); STcert (SWside R 12 14 0); STcert (SWlast 15); STcert (SWside L 3 21 1); STcert (SWside R 12 4 0); STcert (SWside R 12 14 0); STcert (SWside R 12 2 0); STcert (SWside R 13 11 0); STcert (SWside R 13 15 1); STcert (SWside R 13 9 0); STcert (SWlast 16); STcert (SWside R 13 9 0); STcert (SWlast 14); STcert (SWlast 14); STcert (SWlast 14); STcert (SWlast 14); STcert (SWside R 12 8 2); STcert (SWside R 12 4 0); STcert (SWlast 18); STcert (SWside R 13 2 0); STcert (SWside L 7 9 0); STcert (SWlast 41); STcert (SWside L 7 9 0); STcert (SWside R 14 3 0)])
].

Definition q2800_trees_shard05 : list (string * source_tree) :=
[
  ("1RB0RD_1LC0RD_0LE1RA_0LC---_0RA1LF_1LB---", source_split 13 (D,S1) [STcert (SWlast 26); STcert (SWside R 13 16 2); STcert (SWlast 22); STcert (SWside L 3 18 1); STcert (SWside L 1 13 1); STcert (SWside R 13 16 2); STcert (SWside R 13 4 2); STcert (SWside L 4 18 0); STcert (SWside L 5 9 0); STcert (SWlast 22); STcert (SWside L 5 9 0); STcert (SWlast 22); STcert (SWlast 30); STcert (SWside R 13 16 2); STcert (SWlast 26); STcert (SWlast 24); STcert (SWside L 4 22 0); STcert (SWside R 13 6 2); STcert (SWside R 13 20 2); STcert (SWlast 15); STcert (SWside L 7 10 0); STcert (SWlast 14); STcert (SWside L 7 10 0); STcert (SWlast 14)]);
  ("1RB0RD_1LC1RE_0LE1RA_0LC---_0RA1LF_1LB---", source_split 14 (F,S1) [STcert (SWlast 23); STcert (SWlast 16); STcert (SWlast 16); STcert (SWlast 16); STcert (SWlast 18); STcert (SWside R 12 16 0); STcert (SWside L 8 10 1); STcert (SWside R 12 16 0); STcert (SWside R 12 20 1); STcert (SWside L 2 22 2); STcert (SWlast 17); STcert (SWside R 15 9 1); STcert (SWlast 15); STcert (SWlast 15); STcert (SWlast 15); STcert (SWlast 15); STcert (SWside L 6 9 0); STcert (SWside L 6 14 0); STcert (SWside L 6 9 0); STcert (SWside R 13 2 1); STcert (SWside L 7 9 0); STcert (SWlast 64); STcert (SWside L 7 9 0); STcert (SWside R 15 5 0)]);
  ("1RB0RD_1LC0LF_0LE1RA_0LC---_0RA1LF_1LB---", source_split 13 (F,S1) [STcert (SWside L 0 14 2); STcert (SWside R 0 20 4); STcert (SWside L 11 3 1); STcert (SWside L 3 35 1); STcert (SWside L 8 6 0); STcert (SWside R 8 6 2); STcert (SWside L 8 6 0); STcert (SWlast 17); STcert (SWside L 0 16 2); STcert (SWside R 0 26 4); STcert (SWside L 9 5 1); STcert (SWside L 5 9 0); STcert (SWside L 0 17 2); STcert (SWlast 21); STcert (SWlast 21); STcert (SWlast 34); STcert (SWlast 19); STcert (SWlast 16); STcert (SWlast 23); STcert (SWlast 16); STcert (SWside L 7 7 0); STcert (SWside L 7 7 0); STcert (SWside L 7 7 0); STcert (SWside L 7 9 0)])
].

Definition q2800_trees : list (string * source_tree) :=
  q2800_trees_shard01 ++
  q2800_trees_shard02 ++
  q2800_trees_shard03 ++
  q2800_trees_shard04 ++
  q2800_trees_shard05.

Definition q2800_tree_check (bound : nat) (c : string * source_tree) : bool :=
  let (s,t) := c in
  source_tree_check bound (TM_from_str s) t &&
  match source_tree_open (TM_from_str s) t with
  | [] => true
  | _ => false
  end.

Lemma q2800_tree_check_sound (bound : nat) (c : string * source_tree) :
  q2800_tree_check bound c = true ->
  source_table_safe bound (TM_from_str (fst c)).
Proof.
  destruct c as [s t].
  cbn [q2800_tree_check fst].
  rewrite andb_true_iff.
  intros [Hcheck Hopen].
  apply (source_tree_sound bound (TM_from_str s) t Hcheck).
  destruct (source_tree_open (TM_from_str s) t); [constructor|discriminate].
Qed.

Definition q2800_tree_roster : list TM :=
  map (fun c => TM_from_str (fst c)) q2800_trees.
