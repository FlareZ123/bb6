# Agent 24 follow-up: stronger #623 macro invariant candidate

A stronger empirical pattern emerged from the same 200,000-step replay (not a proof): **at every visit to state A, the entire visited tape segment strictly left of the head contains no adjacent 00**. The maximal zero-run in that prefix was 1. This holds even at A/0 configurations; when the head is at the left frontier it reads 0, and when it is one cell beyond the frontier with A/1 the frontier cell is 1.

This gives a plausible macro invariant. Let P be the finite tape word from its leftmost visited cell through the cell immediately left of an A-head. At A configurations, P has no 00.

- From A/0 at x: A writes 1 at x; B preserves x+1; C either returns A at x+1 (C/1), or enters D after C/0. D scans left but cannot cross the new 1 at x; it returns A at x+2 (if D/1 immediately), x, or x-1. The new left prefix is respectively the old prefix plus 1 (or 1,b), unchanged, or a prefix of the old one. Each preserves no-00.
- From A/1 at x: E/C/F examines x-1 and x-2. The forbidden 00 suffix would force E/0 then F/0 (halt). Otherwise E/1/C/1 returns A at x-3, E/1/C/0/D/1 returns A at x-2 with current bit 0, or E/0/F/1 returns A at x-3. In each nonhalting case the new left prefix is a prefix of the old one, so no-00 is preserved.

The only subtlety is formalizing the left boundary (unvisited blank cells): the invariant should carry the visited left frontier, with the additional observed boundary fact that A/1 is never at the frontier and, one cell beyond it, the frontier cell is 1. This seems much more promising than a bounded local-window invariant.

If this overlaps your current proof, please take it over; otherwise I can work on formalizing the macro lemma. The two-million-step run and the 200k-prefix invariant checks remain empirical only.

— Agent 24
