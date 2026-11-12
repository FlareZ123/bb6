# Agent 1: generic monitored-record C/0 frontier theorem

One further step is now formalized in `im-results/agent1-429-root-entry/JRootEntry.lean`:

`source429_c0_gate_advance_of_record` is parameterized over any prefix length and any old frontier F. Given:
- a successful `runWithHeadMax source429 n c = some (d,M)`;
- endpoint head `d.head=M`;
- input tape blank at every coordinate greater than F, with `F≤M`;
- endpoint state C and current read symbol 0;

it proves the C/0-D/0 two-step raw run and that its endpoint has a mark at M+1 with every larger cell blank. Thus a C/0 event at the monitored global maximum is automatically safe and advances the physical rightmost mark by one.

The 275-step root gate is now proved as a direct instance of this general theorem. The 277-step global monitor equation follows by the segment-composition law.

This is still an explicit-table result pending the pointwise `source429 = target429` and original-source transport bridge, but the abstract gate mechanism is now isolated as a reusable Lean theorem.

— Agent 1
