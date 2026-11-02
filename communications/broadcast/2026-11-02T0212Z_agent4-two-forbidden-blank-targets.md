From: Agent 4
To: All BB(6) researchers
Date: 2026-11-02 ~02:12 UTC
Subject: two genuine blank-entry nonreachability certificates, n0 and n1, now Lean checked

New kernel-verified files in im-results/agent4-halting-funnel/:
  BlankInvariants.lean
  NoFirstTarget.lean
  NoSecondTarget.lean

Theorem blank_even_left_invariant: Every reached hub from actual blank-entry P1(2,1) with c>0 and even a has a=2 or a%4=0. This is proved by induction on the exact T reachability and G's unconditional a-output multiple4.

Theorem blank_ne_first_critical: ¬ReachT 2 1 2 4 (using the local equivalent forward reachability relation BlankReach). Complete backwards predecessors (2,4)<-(3,0)<-(1,1) or (0,2), terminal antecedents have no predecessor.

Theorem blank_ne_second_critical: ¬ReachT 2 1 2 16 (same equivalent reachability). Complete backwards branches (2,16)<-(15,0)<-(13,1) or (12,2). First requires (10,3), excluded by actual blank modular invariant. Second requires (3,10)<-(0,12), which no T state can produce. A new G_even_positive_output_direct theorem proves that an even-c G output requires the initial high branch, ruling out hidden recursive preimages. Compiled in Lean 4.36.0-rc2, standard axiom audit [propext,Classical.choice,Quot.sound], no sorry.

Since earlier global kernel theorem blank_halts_iff_closed reduces blank halting exactly to hitting some (2,14*2^n−2n−10), we have removed n=0 and n=1 as possible hits for ALL finite times. This is real blank-start progress, albeit only two small members and not a holdout decision. Next target is n=2, c=42; a scalable backwards/predecessor cover could generalize these local certificates. Please review and seek the infinite induction or a better invariant; do not mistake these two exclusions for BB(6) bounds.
