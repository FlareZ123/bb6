# Raw42/1LB leaf 4828: kernel-checked total arithmetic recurrence

The seven original B0 run-counter macro rules and the normalized streaming reduction are in [Raw42Leaf4828Recurrence.md](Raw42Leaf4828Recurrence.md). This module solves the arithmetic safety problem of the normalized recurrence, with the original-source transport still required to claim a machine Cover.

Decode `base64 -d Raw42Leaf4828Arithmetic.lean.gz.b64 | gzip -d > Raw42Leaf4828Arithmetic.lean`. SHA256 `70094dc99b336aa78193133c92c31452ce69d85aa579b8b0f0a28d47310221ca`; Git blob of encoded source 9b37fd2fbc3de431337d727b23574edcd0bb25e1. Compiles standalone against Lean 4.36.0-rc2 (Std.Tactic).

The crucial change from the earlier sufficient guard: Q need not have effective counter >=8. Q residue-0 and residue-1 transfers are sound at q=0 and q=1 as well; only small terminal residue-2 (effective 2 or 5) is excluded. The source defines relations Q for terminal cases b=3q+3 (q>=0), b=3q+2 (q>=2), or transfer b=3q+4 followed by a recursive Q; P permits these plus the two initial small cases 2 and 5. Counters are positive (>=2), absent counters are 0.

The forbidden exact words are [4], [4,2], [4,5], [4,5,3], [7], [5], [10], [5,3]. The forbidden prefixes (arbitrary tail) are [4,3], [4,2,2], [4,2,3], [4,2,5], [4,5,3,3], [7,3], [10,5], [5,3,5], [2,5,3], [4,11,3]. The only nontrivial preimages:
- [4,3] prefix: [10] exact or [10,5] prefix.
- [7] exact: [5] exact.
- [10] exact: [5,3] exact.
- [10,5] prefix: [5,3,5] or [2,5,3] prefix.
- [2,5,3] prefix: [4,11,3] prefix.
All others have no preimages over positive counters. Each follows exact output-head inversion: an emitted x corresponds to b=3x-3,3x+2,3x-2 in the three respective Q cases. All arithmetic and arbitrary tails are checked, not bounded.

The finite set includes all dangerous low-Q transfer patterns. For high Q (b=6 or b>=8), any transfer carries 2q+2>=6 to a following positive count or to blank extension; the result is again 6 or >=8. Total remaining counter mass strictly decreases on every transfer. For starting 4 or7, the exclusions imply entrance to high Q within at most three transfers. Thus every nonempty positive list avoiding Bad admits a P return; its result is again nonempty, positive, and avoids Bad.

Checked exports `BB6.Agent4Raw42Leaf4828.p_bad`, `p_total`, `p_preserves`, `progress`, and `unlimited` (arbitrarily many P returns from [2]). Axioms for p_bad/unlimited [propext, Classical.choice, Quot.sound], p_total [propext, Quot.sound]. No admitted goals. The remaining bridge must prove the exact positive-cost primitive run for every P relation, including Q low residue-0/1, and the authentic blank entry (time7). Then arbitrarily long live prefixes imply NeverHalts for every compatible F0 completion.