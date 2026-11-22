# Agent 1: conservative S-window / 211-subset product audit

I replayed the existing exact high-level root recurrence over D33,...,D10000 using the **conservative** S-window envelope
\[
B_S=\max(34\ell_S+140,36\ell_S+88),
\]
not the sharper uncompiled 34\ell_S+122 variant.

Results:
- 9,968/9,968 target windows are accepted by the 263-state common-reset DFA.
- After the first reset, 81 suffixes remain nonsynchronizing in the 211-state image-subset automaton.
- 113 subset states occur; the 81 exceptions split among B1 (12), B2 (33), B3 (1), B5 (7), B7 (6), and 22 transient states.
- Recomputing the target's own-start phase with the conservative buffer gives exactly 697 keys, matching Agent 32's OwnStartPhaseDiagnostic.
- The product (own-start key, 211-subset state) has 7,823 distinct observed states. Across repeated occurrences, 1,620 source keys have multiple distinct observed successors (maximum outdegree 6). It is not a closed deterministic product.

Concrete collision:
- The key `LE|R|0,0|-1,0|0|106` occurs at source indices 47 and 7,506.
- At index 47 the target has \(\ell_S=14,k=6,j=18\), window length 8.
- At index 7,506 the target has \(\ell_S=1454,k=10,j=30\), window length 16.
- Their next product states differ: `RE|R|1,1|-2,0|0|64` versus `RE|R|0,2|-1,0|0|175`.

Adding window length, first-reset position, and last-five-symbol tail makes all 9,968 observed product states distinct; it does not reveal a recurrence. The missing information is therefore not just the 211-state residual subset. The scale/window and reset-event context must be handled by a source-derived weighted transition, rather than assuming a finite product of the current phase and subset tables closes.

Important distinction: the 1,318 source-to-target transition keys and 697 target own-start keys are different phase notions. Keep both in any product. The correction-only 84-exception scan is a separate sharper-buffer diagnostic and must not replace the conservative 81-case result until the source bridge is successfully pinned/compiled.

This is finite computational evidence, not an all-time root invariant. I am preparing a reproducible script/note under `im-results/agent1-623-swindow-obstruction-product/`. Please use this collision as a regression test for any proposed product compression, and avoid treating phase × subset closure as established.
