# Raw120 E0=1LB — complete candidate assignment

**Status:** all five previously difficult leaves have a proof route; the full generated sibling coverage theorem is pending source checking. The weighted candidate bound is **224707** (attained by index 1341 in the local original-artifact proof). No global roster entry is removed.

Parent `1RB---_1RC---_0RD---_1LD1RE_1LB1LE_------`: 1,599 splits, 24,218 cycles, 8,209 last-hole leaves, 4,351 initially open leaves, totaling 9,765,625 raw completions. Open SHA-256 `1679cd38cd74165dc392e47f46bcf018ff35cf23decf44120241bb7fa30ade06`.

The initial search found 4,295 FAR, 45 one-block, two multi-block, two late-query and two BiDFA candidates. The two earlier late queries are index 3035 (3,787 live steps, F0) and index 3138 (3,721 live steps, F0). Their provisional 3,793 weighted bound is superseded by index 1341, which reaches A1 after 224,705 live steps; its incoming blank delays are [0,1] and its weighted threshold is 224,707. See [the exact accelerated trace dossier](../agent13-raw120-late1341/README.md).

| Previous difficult leaf | Evidence |
| --- | --- |
| 1265, 3656, 4072 | Source-accepted TreeBiDFA nonhalting certificates, run [45663147964](https://github.com/FlareZ123/bb6/actions/runs/45663147964). |
| 1947 | Source-accepted TreeBiDFA nonhalting certificate, run [45665829257](https://github.com/FlareZ123/bb6/actions/runs/45665829257). |
| 1341 | Exact weighted threshold 224707, kernel-checked locally against original-source coverage artifacts (standard axioms only); fresh exact repository-source CI pending. |

The two prior BiDFA pairs at indices 820 and 850 remain in `1LB-bidfa.json`. The earlier `1LB-hard.json` is preserved as a historical search input, not a current unresolved list.

The existing `generate_sibling.py 1LB` target regenerates the pinned complete first-hole tree, includes all six BiDFA witnesses, and consumes the 1341 accelerated checker through an explicit split ancestry and checked table equality. The source check must accept every other generated leaf, including the earlier 45 one-block and two multi-block candidates, before the whole sibling can be declared covered. If the new discovery pass reports a residual, retain it and repair the specific missing witness.

The manual workflow selector `weighted-tnf-raw120-1lb` is running as [45687881460](https://github.com/FlareZ123/bb6/actions/runs/45687881460) to check the generated `Raw120OneLBData.lean`; it must prove `allOneLB` at 224707 using standard axioms. The former 3793 bound is false for the whole sibling. The other E0 alternatives remain separate obligations.
