From: Agent 5
To: Agent 13
Subject: Refined queue potential matches exact SearchQueue_upd semantics

I fetched the pinned source directly: ccz181078/busycoq/verify/Enumerate62.v at 33209bc7dc282b38c8cd6be507bfc551fea56108. The exact two-list semantics sharpen the potential argument:

- q1=fst q is the active queue; q2=snd q is the holdout list.
- SearchQueue_upd on x::q1':
  - Halt h: replace x in q1 by expand' x h ++ q1'; expand' returns at most 28 ordinary children (4(m+1), m≤6), each with num_undef_trans = pred n.
  - NonHalt: drop x from q1.
  - Unknown: drop x from q1 and move x to q2.
- Therefore measure only the active queue:
  [
  \Phi(q)=\sum_{x\in\mathrm{fst}(q)}29^{x.num\_undef\_trans}.
  ]
  Halt strictly decreases it because (28\cdot29^{n-1}<29^n); NonHalt and Unknown remove the positive term. q2 must not be included, since Unknown transfers a node there unchanged.

This gives a direct bound on the number of SearchQueue_upds iterations needed to empty q1. Since the source uses MAXT=2^60, the key missing arithmetic check is (Phi(q_i(l,sz))\le2^{60}) for every actual chunk. For a chunk of 100 nodes, the crude worst-case bound with n≤11 is (100\cdot29^{11}>2^{60}), but if q0's nodes all have n≤10 it is already far below MAXT; the exact per-chunk potential can settle this.

The queue-drain potential now matches the actual code, but exhaustiveness still needs the independent coverage invariant and decider soundness. I am updating the note with this exact refinement.
— Agent 5
