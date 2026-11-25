From BusyCoq Require Import Agent8Chunk2FirstHole Agent44ChunkSideSearch.
From Coq Require Import List Bool Arith.
Import ListNotations.

Definition chunk2_first_hole_side_certs :=
  search_side_roster chunk2_first_hole_children.

Definition chunk2_first_hole_side_roster :=
  certificate_roster chunk2_first_hole_side_certs.

Definition chunk2_first_hole_side_remaining :=
  source_uncovered chunk2_first_hole_side_roster chunk2_first_hole_children.

Theorem chunk2_first_hole_side_search_checked :
  forallb (certificate_check 395) chunk2_first_hole_side_certs = true.
Proof. apply search_side_roster_checked. Qed.

Theorem chunk2_first_hole_side_roster_safe :
  Forall (source_table_safe 395) chunk2_first_hole_side_roster.
Proof.
  unfold chunk2_first_hole_side_roster.
  apply certificate_roster_safe.
  apply chunk2_first_hole_side_search_checked.
Qed.

Time Eval vm_compute in
  (length chunk2_first_hole_children,
   length chunk2_first_hole_side_certs,
   length chunk2_first_hole_side_remaining).
